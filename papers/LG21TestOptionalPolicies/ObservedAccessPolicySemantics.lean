import LG21TestOptionalPolicies.ContinuousAccessConditionedPopulation
import LG21TestOptionalPolicies.ContinuousResampling
import LG21TestOptionalPolicies.Section4LiteralGaussianSourceBridge

/-!
# Literal two-branch semantics for observed-access policies

Definition 6 has a deterministic access branch and a randomized no-access
branch.  This file records that policy as an actual total branch function and
states the two fairness obligations directly on its attained access output and
its no-access resampling kernel.  In particular, the definitions do not name
or assume a conclusion-bearing protocol-specific theorem.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- The two branches of an observed-access estimation policy.  The access
branch is the literal realized school output; the no-access branch is the
randomized kernel prescribed by the policy. -/
structure LG21ObservedAccessTwoBranchOutput
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) where
  accessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ
  noAccessKernel : Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ
  noAccessKernel_isMarkov : IsMarkovKernel noAccessKernel

/-- The total policy evaluated at a literal source student.  On access it
returns the point mass at the attained output; without access it returns the
policy's randomized output law conditional on the public base profile. -/
def lg21ObservedAccessTwoBranchOutput
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (policy : LG21ObservedAccessTwoBranchOutput testFeature) :
    Bool × (ℝ × (Feature -> ℝ)) -> Measure ℝ :=
  fun student =>
    if lg21ContinuousPopulationAccess student = true then
      Measure.dirac (policy.accessOutput student)
    else
      policy.noAccessKernel (lg21ContinuousPopulationBase testFeature student)

theorem lg21ObservedAccessTwoBranchOutput_on_access
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (policy : LG21ObservedAccessTwoBranchOutput testFeature)
    (student : Bool × (ℝ × (Feature -> ℝ)))
    (haccess : lg21ContinuousPopulationAccess student = true) :
    lg21ObservedAccessTwoBranchOutput testFeature policy student =
      Measure.dirac (policy.accessOutput student) := by
  simp [lg21ObservedAccessTwoBranchOutput, haccess]

theorem lg21ObservedAccessTwoBranchOutput_on_noAccess
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (policy : LG21ObservedAccessTwoBranchOutput testFeature)
    (student : Bool × (ℝ × (Feature -> ℝ)))
    (hnoAccess : lg21ContinuousPopulationAccess student = false) :
    lg21ObservedAccessTwoBranchOutput testFeature policy student =
      policy.noAccessKernel (lg21ContinuousPopulationBase testFeature student) := by
  simp [lg21ObservedAccessTwoBranchOutput, hnoAccess]

/-- Observable fairness for a literal observed-access policy.  The equality
is necessarily only almost everywhere in the attained public-base law: a
regular conditional distribution has no canonical value on null fibres. -/
def LG21ObservedAccessObservableFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    [IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M)]
    (policy : LG21ObservedAccessTwoBranchOutput testFeature) : Prop :=
  condDistrib policy.accessOutput (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
        (lg21ContinuousGaussianAccessPopulationLaw M).map
          (lg21ContinuousPopulationBase testFeature)]
    policy.noAccessKernel

/-- Demographic fairness for the same literal policy: the access output law
equals the randomized no-access output law induced by the actual no-access
base population. -/
def LG21ObservedAccessDemographicallyFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (policy : LG21ObservedAccessTwoBranchOutput testFeature) : Prop :=
  (lg21ContinuousGaussianAccessPopulationLaw M).map policy.accessOutput =
    Measure.bind
      ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
        (lg21ContinuousPopulationBase testFeature))
      policy.noAccessKernel

/-- The transparent conjunction of Definition 3's observable and demographic
fairness obligations for a Definition 6 two-branch policy. -/
def LG21ObservedAccessFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    [IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M)]
    (policy : LG21ObservedAccessTwoBranchOutput testFeature) : Prop :=
  LG21ObservedAccessObservableFair M testFeature policy ∧
    LG21ObservedAccessDemographicallyFair M testFeature policy

/-- Package the proved conditional-kernel and output-law obligations as the
semantic two-branch policy fairness predicate. -/
theorem lg21ObservedAccessFair_of_kernel_and_outputLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    [IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M)]
    (accessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (noAccessKernel : Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    [IsMarkovKernel noAccessKernel]
    (hobservable :
      condDistrib accessOutput (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
            (lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature)]
        noAccessKernel)
    (hdemographic :
      (lg21ContinuousGaussianAccessPopulationLaw M).map accessOutput =
        Measure.bind
          ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
            (lg21ContinuousPopulationBase testFeature))
          noAccessKernel) :
    LG21ObservedAccessFair M testFeature
      { accessOutput := accessOutput
        noAccessKernel := noAccessKernel
        noAccessKernel_isMarkov := inferInstance } := by
  exact ⟨hobservable, hdemographic⟩

/-! ## Deterministic PBO branch semantics -/

/-- Assemble the two realized branches of a deterministic observed-access PBO
policy.  This is separate from `LG21ObservedAccessTwoBranchOutput`, whose
no-access branch is randomized for Definition 6. -/
def lg21ObservedAccessDeterministicTwoBranchOutput
    {Omega Estimate : Type*} (hasAccess : Omega -> Bool)
    (accessOutput noAccessOutput : Omega -> Estimate) : Omega -> Estimate :=
  fun omega => if hasAccess omega then accessOutput omega else noAccessOutput omega

/-- A deterministic two-branch PBO output agrees with its access branch on
the attained access population. -/
theorem lg21ObservedAccessDeterministicTwoBranchOutput_eq_access_ae
    {Omega Estimate : Type*} [MeasurableSpace Omega]
    (law : Measure Omega) (hasAccess : Omega -> Bool)
    (accessOutput noAccessOutput : Omega -> Estimate)
    (haccess : ∀ᵐ omega ∂law, hasAccess omega = true) :
    lg21ObservedAccessDeterministicTwoBranchOutput hasAccess accessOutput
      noAccessOutput =ᵐ[law] accessOutput := by
  filter_upwards [haccess] with omega homega
  simp [lg21ObservedAccessDeterministicTwoBranchOutput, homega]

/-- A deterministic two-branch PBO output agrees with its no-access branch on
the attained no-access population. -/
theorem lg21ObservedAccessDeterministicTwoBranchOutput_eq_noAccess_ae
    {Omega Estimate : Type*} [MeasurableSpace Omega]
    (law : Measure Omega) (hasAccess : Omega -> Bool)
    (accessOutput noAccessOutput : Omega -> Estimate)
    (hnoAccess : ∀ᵐ omega ∂law, hasAccess omega = false) :
    lg21ObservedAccessDeterministicTwoBranchOutput hasAccess accessOutput
      noAccessOutput =ᵐ[law] noAccessOutput := by
  filter_upwards [hnoAccess] with omega homega
  simp [lg21ObservedAccessDeterministicTwoBranchOutput, homega]

/-- Definition 3 for a deterministic PBO policy, at the RCD-a.e. scope that
does not fabricate values on null base fibres. The displayed base law is
required to be the actual base marginal for both access-status populations;
it is not an arbitrary auxiliary measure. -/
def LG21ObservedAccessDeterministicObservableFairAE
    {Omega Base Estimate : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    [MeasurableSpace Estimate] [StandardBorelSpace Estimate] [Nonempty Estimate]
    (baseLaw : Measure Base) (base : Omega -> Base)
    (accessLaw noAccessLaw : Measure Omega) [IsFiniteMeasure accessLaw]
    [IsFiniteMeasure noAccessLaw] (output : Omega -> Estimate) : Prop :=
  accessLaw.map base = baseLaw ∧
    noAccessLaw.map base = baseLaw ∧
    condDistrib output base accessLaw =ᵐ[baseLaw]
      condDistrib output base noAccessLaw

/-- Definition 4 for the same deterministic PBO policy. -/
def LG21ObservedAccessDeterministicDemographicallyFair
    {Omega Estimate : Type*} [MeasurableSpace Omega] [MeasurableSpace Estimate]
    (accessLaw noAccessLaw : Measure Omega) (output : Omega -> Estimate) : Prop :=
  accessLaw.map output = noAccessLaw.map output

/-- The paired Definition 3/4 predicate for one deterministic PBO policy. -/
def LG21ObservedAccessDeterministicFairAE
    {Omega Base Estimate : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    [MeasurableSpace Estimate] [StandardBorelSpace Estimate] [Nonempty Estimate]
    (baseLaw : Measure Base) (base : Omega -> Base)
    (accessLaw noAccessLaw : Measure Omega) [IsFiniteMeasure accessLaw]
    [IsFiniteMeasure noAccessLaw] (output : Omega -> Estimate) : Prop :=
  LG21ObservedAccessDeterministicObservableFairAE
      baseLaw base accessLaw noAccessLaw output ∧
    LG21ObservedAccessDeterministicDemographicallyFair
      accessLaw noAccessLaw output

end

end LG21TestOptionalPolicies
