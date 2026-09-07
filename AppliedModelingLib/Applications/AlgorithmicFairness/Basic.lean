import AppliedModelingLib.Learning.Statistics.Prediction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Algorithmic Fairness Interfaces

Reusable finite interfaces for group fairness objectives, fairness-threshold
families, Pareto-front statements, and postprocessing guarantees.  Generic
prediction and loss definitions live in `AppliedModelingLib.Learning.Statistics`.
-/

namespace AppliedModelingLib
namespace AlgorithmicFairness

open scoped BigOperators

abbrev Model (X : Type*) := Statistics.Model X
abbrev Group (X : Type*) := Statistics.Group X

/--
Abstract group-fairness predicate: each group-specific metric must be within
`gamma` of the population metric after multiplying by the supplied group
slack/weight.
-/
def GammaFairForMetric {X : Type*} (G : Set (Group X))
    (groupMetric : Group X → Model X → ℝ) (populationMetric : Model X → ℝ)
    (slack : Group X → ℝ) (gamma : ℝ) (c : Model X) : Prop :=
  ∀ g ∈ G, slack g * |groupMetric g c - populationMetric c| ≤ gamma

/-- The max-over-g fairness objective induced by a group metric. -/
def FairnessObjective {X : Type*} (G : Set (Group X))
    (groupMetric : Group X → Model X → ℝ) (populationMetric : Model X → ℝ)
    (slack : Group X → ℝ) (phi : Model X → ℝ) : Prop :=
  ∀ c, (∀ g ∈ G, slack g * |groupMetric g c - populationMetric c| ≤ phi c) ∧
    ∀ bound : ℝ,
      (∀ g ∈ G, slack g * |groupMetric g c - populationMetric c| ≤ bound) →
        phi c ≤ bound

/-- A max-over-g fairness objective bounded by `gamma` implies gamma-fairness. -/
theorem gammaFairForMetric_of_fairnessObjective_le {X : Type*}
    {G : Set (Group X)}
    {groupMetric : Group X → Model X → ℝ} {populationMetric : Model X → ℝ}
    {slack : Group X → ℝ} {phi : Model X → ℝ} {gamma : ℝ} {c : Model X}
    (hphi : FairnessObjective G groupMetric populationMetric slack phi)
    (hbound : phi c ≤ gamma) :
    GammaFairForMetric G groupMetric populationMetric slack gamma c := by
  intro g hg
  exact le_trans ((hphi c).1 g hg) hbound

/-- Gamma-fairness bounds the associated max-over-g fairness objective. -/
theorem fairnessObjective_le_of_gammaFairForMetric {X : Type*}
    {G : Set (Group X)}
    {groupMetric : Group X → Model X → ℝ} {populationMetric : Model X → ℝ}
    {slack : Group X → ℝ} {phi : Model X → ℝ} {gamma : ℝ} {c : Model X}
    (hphi : FairnessObjective G groupMetric populationMetric slack phi)
    (hfair : GammaFairForMetric G groupMetric populationMetric slack gamma c) :
    phi c ≤ gamma :=
  (hphi c).2 gamma hfair

/--
For a well-specified max-over-g fairness objective, the group-indexed
`gamma`-fair constraints are equivalent to the scalar objective bound.
-/
theorem gammaFairForMetric_iff_fairnessObjective_le {X : Type*}
    {G : Set (Group X)}
    {groupMetric : Group X → Model X → ℝ} {populationMetric : Model X → ℝ}
    {slack : Group X → ℝ} {phi : Model X → ℝ} {gamma : ℝ} {c : Model X}
    (hphi : FairnessObjective G groupMetric populationMetric slack phi) :
    GammaFairForMetric G groupMetric populationMetric slack gamma c ↔
      phi c ≤ gamma :=
  ⟨fairnessObjective_le_of_gammaFairForMetric hphi,
    gammaFairForMetric_of_fairnessObjective_le hphi⟩

/-- The four fairness notions used by common threshold-postprocessing formulas. -/
inductive FairnessKind where
  | falsePositive
  | falseNegative
  | statisticalParity
  | errorRate
deriving DecidableEq

/--
Domain condition under which the threshold boundary formula for a fairness
notion has no zero denominator. Statistical parity has no denominator.
-/
def FairnessKind.ValidThresholdValue : FairnessKind → ℝ → Prop
  | FairnessKind.falsePositive, v => v ≠ 1
  | FairnessKind.falseNegative, v => v ≠ 0
  | FairnessKind.statisticalParity, _ => True
  | FairnessKind.errorRate, v => v ≠ 1 / 2

/-- Threshold boundary for one of the standard group-fairness notions. -/
noncomputable def fairnessThresholdBoundary : FairnessKind → ℝ → ℝ
  | FairnessKind.falsePositive, v => (2 * v - 1) / (1 - v)
  | FairnessKind.falseNegative, v => (1 - 2 * v) / v
  | FairnessKind.statisticalParity, v => 2 * v - 1
  | FairnessKind.errorRate, v => (2 * v - 1) / (1 - 2 * v)

/-- Linear group-membership score `sum_i lambda_i * (g_i x - beta_i)`. -/
def groupThresholdScore {I X : Type*} [Fintype I]
    (groups : I → Group X) (lambda beta : I → ℝ) (x : X) : ℝ :=
  ∑ i, lambda i * (groups i x - beta i)

/-- One thresholding function from a group-threshold family. -/
noncomputable def fairnessThresholdFunction {I X : Type*} [Fintype I]
    (kind : FairnessKind) (groups : I → Group X)
    (lambda beta : I → ℝ) : X → ℝ → ℝ :=
  fun x v =>
    if fairnessThresholdBoundary kind v ≤ groupThresholdScore groups lambda beta x then
      1
    else
      0

/-- Membership in a norm-bounded group-threshold function family. -/
def ThresholdFunctionFamilyMember {I X : Type*} [Fintype I]
    (kind : FairnessKind) (groups : I → Group X) (Cbound : ℝ)
    (b : X → ℝ → ℝ) : Prop :=
  ∃ lambda beta : I → ℝ,
    (∑ i, |lambda i|) ≤ Cbound ∧
      b = fairnessThresholdFunction kind groups lambda beta

/--
Membership in a threshold-function family over a finite set of prediction
values, including the source-domain condition that every threshold formula
used on that value set has nonzero denominators.
-/
def ThresholdFunctionFamilyMemberOnValues {I X : Type*} [Fintype I]
    (kind : FairnessKind) (groups : I → Group X) (R : Finset ℝ) (Cbound : ℝ)
    (b : X → ℝ → ℝ) : Prop :=
  (∀ v ∈ R, kind.ValidThresholdValue v) ∧
    ThresholdFunctionFamilyMember kind groups Cbound b

/--
The finite-value threshold family carries the denominator-domain side
conditions needed by the threshold boundary formula on every value in `R`.
-/
theorem validThresholdValue_of_thresholdFunctionFamilyMemberOnValues
    {I X : Type*} [Fintype I]
    {kind : FairnessKind} {groups : I → Group X}
    {R : Finset ℝ} {Cbound : ℝ} {b : X → ℝ → ℝ}
    (hb : ThresholdFunctionFamilyMemberOnValues kind groups R Cbound b) :
    ∀ v ∈ R, kind.ValidThresholdValue v :=
  hb.1

/--
The finite-value threshold family is still a member of the underlying
norm-bounded threshold-function family after forgetting value-domain
side conditions.
-/
theorem thresholdFunctionFamilyMember_of_onValues
    {I X : Type*} [Fintype I]
    {kind : FairnessKind} {groups : I → Group X}
    {R : Finset ℝ} {Cbound : ℝ} {b : X → ℝ → ℝ}
    (hb : ThresholdFunctionFamilyMemberOnValues kind groups R Cbound b) :
    ThresholdFunctionFamilyMember kind groups Cbound b :=
  hb.2

/--
Build the finite-value threshold family from a threshold-function
witness and the value-domain side conditions.
-/
theorem thresholdFunctionFamilyMemberOnValues_intro
    {I X : Type*} [Fintype I]
    {kind : FairnessKind} {groups : I → Group X}
    {R : Finset ℝ} {Cbound : ℝ} {b : X → ℝ → ℝ}
    (hvalid : ∀ v ∈ R, kind.ValidThresholdValue v)
    (hb : ThresholdFunctionFamilyMember kind groups Cbound b) :
    ThresholdFunctionFamilyMemberOnValues kind groups R Cbound b :=
  ⟨hvalid, hb⟩

/-- Pareto-front membership for accuracy and fairness objectives. -/
def ParetoFrontMember {X : Type*} (C : Set (Model X))
    (err fairness : Model X → ℝ) (c : Model X) : Prop :=
  c ∈ C ∧
    ¬ ∃ c' ∈ C,
      err c' ≤ err c ∧ fairness c' ≤ fairness c ∧
        (err c' < err c ∨ fairness c' < fairness c)

/-- Approximate Pareto-front membership with error and fairness tolerances. -/
def ApproxParetoFrontMember {X : Type*} (C : Set (Model X))
    (err fairness : Model X → ℝ) (errTol fairTol : ℝ) (c : Model X) : Prop :=
  c ∈ C ∧
    ¬ ∃ c' ∈ C,
      err c' + errTol < err c ∧ fairness c' + fairTol < fairness c

/-- Optimality under a hard group-fairness constraint. -/
def OptimalGammaFairModel {X : Type*} (C : Set (Model X))
    (err : Model X → ℝ) (fair : Model X → Prop) (c : Model X) : Prop :=
  c ∈ C ∧ fair c ∧ ∀ c' ∈ C, fair c' → err c ≤ err c'

/--
The optimal constrained model can be stated either with group-indexed fairness
constraints or with the associated max-over-g fairness objective bound.
-/
theorem optimalGammaFairModel_groupConstraint_iff_objectiveBound {X : Type*}
    {C : Set (Model X)} {err : Model X → ℝ}
    {G : Set (Group X)}
    {groupMetric : Group X → Model X → ℝ} {populationMetric : Model X → ℝ}
    {slack : Group X → ℝ} {phi : Model X → ℝ} {gamma : ℝ} {c : Model X}
    (hphi : FairnessObjective G groupMetric populationMetric slack phi) :
    OptimalGammaFairModel C err
        (GammaFairForMetric G groupMetric populationMetric slack gamma) c ↔
      OptimalGammaFairModel C err (fun c => phi c ≤ gamma) c := by
  constructor
  · rintro ⟨hcC, hfair, hopt⟩
    refine ⟨hcC, (gammaFairForMetric_iff_fairnessObjective_le hphi).mp hfair, ?_⟩
    intro c' hc'C hphi_le
    exact hopt c' hc'C
      ((gammaFairForMetric_iff_fairnessObjective_le hphi).mpr hphi_le)
  · rintro ⟨hcC, hphi_le, hopt⟩
    refine ⟨hcC, (gammaFairForMetric_iff_fairnessObjective_le hphi).mpr hphi_le, ?_⟩
    intro c' hc'C hfair
    exact hopt c' hc'C
      ((gammaFairForMetric_iff_fairnessObjective_le hphi).mp hfair)

/-- Abstract postprocessing optimum for a predictor-dependent objective. -/
def OptimalPostprocessingForPredictor {X : Type*} (C : Set (Model X))
    (predictor : Model X) (err : Model X → Model X → ℝ)
    (fair : Model X → Model X → Prop) (c : Model X) : Prop :=
  c ∈ C ∧ fair predictor c ∧
    ∀ c' ∈ C, fair predictor c' → err predictor c ≤ err predictor c'

/--
Approximate postprocessing guarantee: the output is in `C`, feasible up to a
fairness tolerance, and error-optimal up to `errTol` among exact `gamma`-fair
classifiers.
-/
def ApproxPostprocessingGuarantee {X : Type*} (C : Set (Model X))
    (err fairness : Model X → ℝ) (c : Model X)
    (gamma errTol fairTol : ℝ) : Prop :=
  c ∈ C ∧ fairness c ≤ gamma + fairTol ∧
    ∀ c' ∈ C, fairness c' ≤ gamma → err c ≤ err c' + errTol

/-- Approximate postprocessing guarantees imply approximate Pareto membership. -/
theorem approxParetoFrontMember_of_postprocessingGuarantee {X : Type*}
    {C : Set (Model X)} {err fairness : Model X → ℝ}
    {c : Model X} {gamma errTol fairTol : ℝ}
    (hpost : ApproxPostprocessingGuarantee C err fairness c gamma errTol fairTol) :
    ApproxParetoFrontMember C err fairness errTol fairTol c := by
  rcases hpost with ⟨hcC, hcFair, hopt⟩
  refine ⟨hcC, ?_⟩
  rintro ⟨c', hc'C, herr, hfair⟩
  have hc'_fair : fairness c' ≤ gamma := by
    linarith
  have hopt' := hopt c' hc'C hc'_fair
  linarith

end AlgorithmicFairness
end AppliedModelingLib
