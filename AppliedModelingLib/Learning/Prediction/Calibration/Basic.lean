import AppliedModelingLib.Learning.Prediction.Risk
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Multiaccuracy and multicalibration primitives

Finite weighted calibration definitions and the elementary sign bridges used
across multicalibration, outcome-indistinguishability, and omniprediction
papers.
-/

namespace AppliedModelingLib.Learning.Prediction

open scoped BigOperators

/-- Indicator for a finite prediction level set `f(x) = v`. -/
noncomputable def levelSetIndicator {X : Type*} (f : Score X) (v : ℝ) : X → ℝ :=
  fun x => if f x = v then 1 else 0

/-- Absolute product-class multiaccuracy in finite weighted notation. -/
def ApproxMultiaccurateOnProducts {X : Type*} [Fintype X]
    (w : FiniteWeight X) (f y : Score X)
    (G : Set (SoftGroup X)) (H : Set (Score X)) (eta : ℝ) : Prop :=
  ∀ g ∈ G, ∀ h ∈ H,
    |groupLossNumerator w g (fun x => h x * (f x - y x))| ≤ eta

/-- Source-style one-sided product-class multiaccuracy. -/
def OneSidedMultiaccurateOnProducts {X : Type*} [Fintype X]
    (w : FiniteWeight X) (f y : Score X)
    (G : Set (SoftGroup X)) (H : Set (Score X)) (eta : ℝ) : Prop :=
  ∀ g ∈ G, ∀ h ∈ H,
    groupLossNumerator w g (fun x => h x * (y x - f x)) ≤ eta

/-- A score class is closed under pointwise negation. -/
def ModelClassClosedUnderNegation {X : Type*} (H : Set (Score X)) : Prop :=
  ∀ h ∈ H, (fun x => -h x) ∈ H

/-- Flipping the residual sign negates the weighted residual correlation. -/
theorem groupLossNumerator_residual_flip {X : Type*} [Fintype X]
    (w : FiniteWeight X) (g : SoftGroup X) (h f y : Score X) :
    groupLossNumerator w g (fun x => h x * (f x - y x)) =
      -groupLossNumerator w g (fun x => h x * (y x - f x)) := by
  classical
  unfold groupLossNumerator
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  ring

/-- Negating the feature converts source-style residuals to the opposite sign. -/
theorem groupLossNumerator_neg_sourceResidual_eq {X : Type*} [Fintype X]
    (w : FiniteWeight X) (g : SoftGroup X) (h f y : Score X) :
    groupLossNumerator w g (fun x => (-h x) * (y x - f x)) =
      groupLossNumerator w g (fun x => h x * (f x - y x)) := by
  classical
  unfold groupLossNumerator
  refine Finset.sum_congr rfl ?_
  intro x _hx
  ring

/-- One-sided multiaccuracy gives absolute multiaccuracy when the score class
is closed under negation. -/
theorem approxMultiaccurateOnProducts_of_oneSided_negationClosed
    {X : Type*} [Fintype X]
    {w : FiniteWeight X} {f y : Score X}
    {G : Set (SoftGroup X)} {H : Set (Score X)} {eta : ℝ}
    (hma : OneSidedMultiaccurateOnProducts w f y G H eta)
    (hneg : ModelClassClosedUnderNegation H) :
    ApproxMultiaccurateOnProducts w f y G H eta := by
  intro g hg h hh
  have hsource :
      groupLossNumerator w g (fun x => h x * (y x - f x)) ≤ eta :=
    hma g hg h hh
  have hnegsource :
      groupLossNumerator w g (fun x => (-h x) * (y x - f x)) ≤ eta :=
    hma g hg (fun x => -h x) (hneg h hh)
  have hupper :
      groupLossNumerator w g (fun x => h x * (f x - y x)) ≤ eta := by
    rw [groupLossNumerator_neg_sourceResidual_eq w g h f y] at hnegsource
    exact hnegsource
  have hlower :
      -eta ≤ groupLossNumerator w g (fun x => h x * (f x - y x)) := by
    have hneg_le : -eta ≤
        -groupLossNumerator w g (fun x => h x * (y x - f x)) :=
      neg_le_neg hsource
    simpa [groupLossNumerator_residual_flip w g h f y] using hneg_le
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Absolute product-class multiaccuracy implies the printed one-sided source
convention after flipping the residual sign. -/
theorem oneSidedMultiaccurateOnProducts_of_approxMultiaccurateOnProducts
    {X : Type*} [Fintype X]
    {w : FiniteWeight X} {f y : Score X}
    {G : Set (SoftGroup X)} {H : Set (Score X)} {eta : ℝ}
    (hma : ApproxMultiaccurateOnProducts w f y G H eta) :
    OneSidedMultiaccurateOnProducts w f y G H eta := by
  intro g hg h hh
  have hcorr := hma g hg h hh
  have hlower :
      -eta ≤ groupLossNumerator w g (fun x => h x * (f x - y x)) :=
    (abs_le.mp hcorr).1
  have hneg_le :
      -groupLossNumerator w g (fun x => h x * (f x - y x)) ≤ eta :=
    by simpa using neg_le_neg hlower
  simpa [groupLossNumerator_residual_flip w g h f y] using hneg_le

/-- Approximate multicalibration in expectation over finite prediction values. -/
def ApproxMulticalibratedInExpectation {X : Type*} [Fintype X]
    (w : FiniteWeight X) (R : Finset ℝ) (f y : Score X)
    (C : Set (Score X)) (alpha : ℝ) : Prop :=
  ∀ c ∈ C,
    R.sum (fun v =>
      |weightedRateNumerator w (levelSetIndicator f v)
        (fun x => c x * (f x - y x))|) ≤ alpha

/-- Approximate joint multicalibration over a class of threshold functions. -/
def ApproxJointMulticalibratedInExpectation {X : Type*} [Fintype X]
    (w : FiniteWeight X) (R : Finset ℝ) (f y : Score X)
    (B : Set (X → ℝ → ℝ)) (alpha : ℝ) : Prop :=
  ∀ b ∈ B,
    R.sum (fun v =>
      |weightedRateNumerator w
        (fun x => levelSetIndicator f v x * b x v)
        (fun x => f x - y x)|) ≤ alpha

/-- Absolute self-orthogonality of a predictor on a group collection. -/
def SelfOrthogonalOnGroups {X : Type*} [Fintype X]
    (w : FiniteWeight X) (f y : Score X)
    (G : Set (SoftGroup X)) (eta : ℝ) : Prop :=
  ∀ g ∈ G,
    |groupLossNumerator w g (fun x => f x * (f x - y x))| ≤ eta

end AppliedModelingLib.Learning.Prediction
