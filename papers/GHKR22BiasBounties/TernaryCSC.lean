import GHKR22BiasBounties.AdaptiveChecker
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic.Linarith

/-!
# Ternary cost-sensitive classification reduction

Definitions 17--19 and Theorem 20 are specialized, as in the source, to binary
classification with zero-one loss.  The central identity is proved pointwise:
the induced ternary cost is the negative of the mass-weighted certificate
improvement contribution.
-/

namespace GHKR22BiasBounties

noncomputable section

/-- Zero-one loss on Boolean labels. -/
def binaryZeroOneLoss : BoundedLoss Bool where
  value prediction truth := if prediction = truth then 0 else 1
  nonneg prediction truth := by split <;> norm_num
  le_one prediction truth := by split <;> norm_num

/-- The ternary label alphabet `{0,1,?}`. -/
inductive TernaryLabel where
  | zero
  | one
  | defer
deriving DecidableEq, Fintype, Repr

/-- A ternary classifier. -/
abbrev TernaryPredictor (X : Type*) := X → TernaryLabel

/-- Definition 17: the non-deferral group induced by `p`. -/
def derivedGroup {X : Type*} (p : TernaryPredictor X) : Group X :=
  fun x => p x != .defer

/-- Definition 17: the binary model induced by `p` (arbitrary zero on defer). -/
def derivedModel {X : Type*} (p : TernaryPredictor X) : Model X Bool :=
  fun x =>
    match p x with
    | .zero => false
    | .one => true
    | .defer => false

/-- The binary prediction represented by a non-deferring ternary label. -/
def ternaryBinaryPrediction : TernaryLabel → Bool
  | .zero => false
  | .one => true
  | .defer => false

/--
Definition 19: cost induced by the current binary model.  Deferral costs zero;
otherwise this is new zero-one loss minus current zero-one loss.
-/
def inducedCost {X : Type*} (current : Model X Bool)
    (datum : X × Bool) (prediction : TernaryLabel) : ℝ :=
  match prediction with
  | .defer => 0
  | label =>
      binaryZeroOneLoss.value (ternaryBinaryPrediction label) datum.2 -
        binaryZeroOneLoss.value (current datum.1) datum.2

/-- The induced cost has exactly the source's `-1,0,1` case semantics. -/
theorem inducedCost_cases {X : Type*} (current : Model X Bool)
    (datum : X × Bool) (prediction : TernaryLabel) :
    inducedCost current datum prediction =
      if prediction = .defer then 0
      else if current datum.1 = datum.2 ∧
          ternaryBinaryPrediction prediction ≠ datum.2 then 1
      else if ternaryBinaryPrediction prediction = datum.2 ∧
          current datum.1 ≠ datum.2 then -1
      else 0 := by
  cases prediction <;> cases hcurrent : current datum.1 <;> cases htruth : datum.2 <;>
    simp [inducedCost, ternaryBinaryPrediction, binaryZeroOneLoss, hcurrent, htruth]

/-- Definition 18: expected cost of a ternary predictor. -/
def expectedTernaryCost {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (p : TernaryPredictor X) : ℝ :=
  AppliedModelingLib.pmfExp law (fun datum => inducedCost current datum (p datum.1))

/-- Definition 18: minimizer of a cost-sensitive classification problem. -/
def CostSensitiveMinimizer {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (K : Set (TernaryPredictor X)) (pStar : TernaryPredictor X) : Prop :=
  pStar ∈ K ∧ ∀ p ∈ K,
    expectedTernaryCost law current pStar ≤ expectedTernaryCost law current p

/-- The pointwise induced cost is the negative certificate contribution. -/
theorem inducedCost_eq_neg_submissionScore {X : Type*}
    (current : Model X Bool) (p : TernaryPredictor X) (datum : X × Bool) :
    inducedCost current datum (p datum.1) =
      -submissionScore binaryZeroOneLoss
        { current := current, group := derivedGroup p,
          replacement := derivedModel p } datum := by
  cases hp : p datum.1 <;> cases hcurrent : current datum.1 <;>
    cases htruth : datum.2 <;>
    simp [inducedCost, submissionScore, derivedGroup, derivedModel,
      groupIndicator, datumLoss, binaryZeroOneLoss, ternaryBinaryPrediction,
      hp, hcurrent, htruth]

/-- Expected induced cost is negative weighted certificate improvement. -/
theorem expectedTernaryCost_eq_neg_certificateImprovementScore
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (p : TernaryPredictor X) :
    expectedTernaryCost law current p =
      -certificateImprovementScore law binaryZeroOneLoss current
        (derivedGroup p) (derivedModel p) := by
  calc
    expectedTernaryCost law current p =
        AppliedModelingLib.pmfExp law (fun datum =>
          -submissionScore binaryZeroOneLoss
            { current := current, group := derivedGroup p,
              replacement := derivedModel p } datum) := by
      apply AppliedModelingLib.pmfExp_congr
      exact fun datum => inducedCost_eq_neg_submissionScore current p datum
    _ = -AppliedModelingLib.pmfExp law
          (submissionScore binaryZeroOneLoss
            { current := current, group := derivedGroup p,
              replacement := derivedModel p }) := by
      exact AppliedModelingLib.pmfExp_neg _ _
    _ = -certificateImprovementScore law binaryZeroOneLoss current
          (derivedGroup p) (derivedModel p) := by
      rw [pmfExp_submissionScore_eq_certificateImprovementScore]

/-- The derived pair of a ternary predictor maximizes the certificate objective. -/
def DerivedCertificateMaximizer {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (K : Set (TernaryPredictor X)) (pStar : TernaryPredictor X) : Prop :=
  pStar ∈ K ∧ ∀ p ∈ K,
    certificateImprovementScore law binaryZeroOneLoss current
        (derivedGroup p) (derivedModel p) ≤
      certificateImprovementScore law binaryZeroOneLoss current
        (derivedGroup pStar) (derivedModel pStar)

/-- Theorem 20: ternary CSC minimization exactly solves certificate maximization. -/
theorem theorem20_costSensitive_minimizer_is_certificate_maximizer
    {X : Type*} [Fintype X] [DecidableEq X]
    (law : Distribution X Bool) (current : Model X Bool)
    (K : Set (TernaryPredictor X)) (pStar : TernaryPredictor X)
    (hmin : CostSensitiveMinimizer law current K pStar) :
    DerivedCertificateMaximizer law current K pStar := by
  refine ⟨hmin.1, ?_⟩
  intro p hp
  have hcost := hmin.2 p hp
  rw [expectedTernaryCost_eq_neg_certificateImprovementScore,
    expectedTernaryCost_eq_neg_certificateImprovementScore] at hcost
  linarith

end

end GHKR22BiasBounties
