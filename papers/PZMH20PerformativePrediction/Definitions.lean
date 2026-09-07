import AppliedModelingLib.GameTheory.PerformativePrediction

/-!
# Source Definitions for *Performative Prediction*

Definitions 2.1, 2.3, 3.1, and 3.3 of Perdomo, Zrnic, Mendler-Dünner, and
Hardt (PMLR 119, 2020).  The original finite-PMF realization remains available
for the finite theorem slice; the general probability-measure realization
below carries the source's arbitrary data-distribution domain with explicit
integrability and finite-first-moment assumptions where required.
-/

namespace PZMH20PerformativePrediction

open AppliedModelingLib

/-- General-distribution Definition 2.1: performative optimality. -/
def IsMeasurePerformativelyOptimal {Parameter Data : Type*} [MeasurableSpace Data]
    (model : MeasurePerformativeModel Parameter Data) (parameter : Parameter) : Prop :=
  AppliedModelingLib.IsMeasurePerformativelyOptimal model parameter

/-- General-distribution Definition 2.1 on the source parameter domain. -/
def IsMeasurePerformativelyOptimalOn {Parameter Data : Type*} [MeasurableSpace Data]
    (model : MeasurePerformativeModel Parameter Data) (domain : Set Parameter)
    (parameter : Parameter) : Prop :=
  AppliedModelingLib.IsMeasurePerformativelyOptimalOn model domain parameter

/-- General-distribution Definition 2.3: performative stability. -/
def IsMeasureStable {Parameter Data : Type*} [MeasurableSpace Data]
    (model : MeasurePerformativeModel Parameter Data) (parameter : Parameter) : Prop :=
  AppliedModelingLib.IsMeasurePerformativelyStable model parameter

/-- General-distribution Definition 3.3: repeated risk minimization. -/
def IsMeasureRRM {Parameter Data : Type*} [MeasurableSpace Data]
    (model : MeasurePerformativeModel Parameter Data) (update : Parameter → Parameter) : Prop :=
  AppliedModelingLib.IsMeasureRepeatedRiskMinimization model update

/-- General-distribution Definition 2.3 on the source's parameter domain. -/
def IsMeasureStableOn {Parameter Data : Type*} [MeasurableSpace Data]
    (model : MeasurePerformativeModel Parameter Data) (domain : Set Parameter)
    (parameter : Parameter) : Prop :=
  AppliedModelingLib.IsMeasurePerformativelyStableOn model domain parameter

/-- General-distribution Definition 3.3 with minimization over the parameter domain. -/
def IsMeasureRRMOn {Parameter Data : Type*} [MeasurableSpace Data]
    (model : MeasurePerformativeModel Parameter Data) (domain : Set Parameter)
    (update : Parameter → Parameter) : Prop :=
  AppliedModelingLib.IsMeasureRepeatedRiskMinimizationOn model domain update

/--
General-distribution Definition 3.1: W₁ sensitivity with an explicit
finite-first-moment witness for each pair of induced laws.
-/
def IsMeasureWassersteinSensitive {Parameter Data : Type*}
    [MetricSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data) (sensitivity : ℝ) : Prop :=
  AppliedModelingLib.IsMeasureWassersteinSensitive model sensitivity

/-- General-distribution Definition 3.1 on the source parameter domain. -/
def IsMeasureWassersteinSensitiveOn {Parameter Data : Type*}
    [MetricSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data) (domain : Set Parameter)
    (sensitivity : ℝ) : Prop :=
  AppliedModelingLib.IsMeasureWassersteinSensitiveOn model domain sensitivity

/--
Assumption A2 for an arbitrary data law: every pointwise loss is strongly
convex in the deployed parameter, with the displayed gradient realization.
-/
def IsMeasurePointwiseGradientStronglyConvex {Parameter Data : Type*}
    [MeasurableSpace Data] [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) (modulus : ℝ) : Prop :=
  AppliedModelingLib.IsMeasurePointwiseGradientStronglyConvex model gradient modulus

/-- Assumption A2 on the source parameter domain. -/
def IsMeasurePointwiseGradientStronglyConvexOn {Parameter Data : Type*}
    [MeasurableSpace Data] [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) (domain : Set Parameter)
    (modulus : ℝ) : Prop :=
  AppliedModelingLib.IsMeasurePointwiseGradientStronglyConvexOn
    model gradient domain modulus

/-- Definition 2.1: performative optimality minimizes performative risk. -/
def IsPerformativelyOptimal {Parameter Data : Type*}
    [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data) (parameter : Parameter) : Prop :=
  ∀ candidate, performativeRisk model parameter ≤ performativeRisk model candidate

/-- The finite-PMF specialization of Definition 2.1 attains a performative optimum. -/
theorem exists_isPerformativelyOptimal
    {Parameter Data : Type*} [Fintype Parameter] [Nonempty Parameter]
    [Fintype Data] [DecidableEq Data] (model : FinitePerformativeModel Parameter Data) :
    ∃ parameter, IsPerformativelyOptimal model parameter :=
  exists_performativelyOptimal model

/-- Definition 3.3: a selected repeated-risk-minimization update. -/
def IsRRM {Parameter Data : Type*} [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data) (update : Parameter → Parameter) : Prop :=
  IsRepeatedRiskMinimization model update

/--
Definition 3.3 restricted to the paper's designated parameter set.  The RRM
selector is required to return a frozen-law population-risk minimizer in that
set for every deployed parameter in the set.
-/
def IsRRMOn {Parameter Data : Type*} [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data) (domain : Set Parameter)
    (update : Parameter → Parameter) : Prop :=
  IsRepeatedRiskMinimizationOn model domain update

/-- Definition 2.3 in the paper's decoupled-risk notation. -/
def IsStable {Parameter Data : Type*} [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data) (parameter : Parameter) : Prop :=
  IsPerformativelyStable model parameter

/-- Definition 2.3 relative to the paper's designated parameter domain. -/
def IsStableOn {Parameter Data : Type*} [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data) (domain : Set Parameter)
    (parameter : Parameter) : Prop :=
  IsPerformativelyStableOn model domain parameter

/--
Finite-PMF primal transport realization of Definition 3.1's distribution-map
sensitivity.  It supplies a coupling witness at the displayed bound; relating
it extensionally to the source's Wasserstein-1 definition is a separate bridge.
-/
def IsFiniteTransportSensitive {Parameter Data : Type*}
    [Fintype Data] [DecidableEq Data] [MetricSpace Parameter] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data) (sensitivity : ℝ) : Prop :=
  AppliedModelingLib.IsFiniteTransportSensitive model sensitivity

/--
Finite-PMF realization of the paper's Wasserstein-1 sensitivity condition.
The underlying distance is the infimum of finite coupling costs; this is a
finite-carrier specialization, not the source's arbitrary-measure definition.
-/
def IsFiniteWassersteinSensitive {Parameter Data : Type*}
    [Fintype Data] [DecidableEq Data] [MetricSpace Parameter] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data) (sensitivity : ℝ) : Prop :=
  AppliedModelingLib.IsFiniteWassersteinSensitive model sensitivity

/-- Theorem 4.3's loss regularity condition in its finite-PMF realization. -/
def IsDataLossLipschitz {Parameter Data : Type*}
    [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data) (constant : NNReal) : Prop :=
  AppliedModelingLib.IsDataLossLipschitz model constant

/-- Corollary 5.1's parameter-coordinate loss regularity condition. -/
def IsParameterLossLipschitz {Parameter Data : Type*}
    [Fintype Data] [DecidableEq Data] [NormedAddCommGroup Parameter]
    (model : FinitePerformativeModel Parameter Data) (constant : NNReal) : Prop :=
  AppliedModelingLib.IsParameterLossLipschitz model constant

end PZMH20PerformativePrediction
