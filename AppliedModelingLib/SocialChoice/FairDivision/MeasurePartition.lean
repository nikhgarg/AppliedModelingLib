import AppliedModelingLib.Foundations.Probability.MeasureAtoms
import AppliedModelingLib.SocialChoice.FairDivision.IndivisibleGoods
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory
open scoped BigOperators

namespace AppliedModelingLib
namespace FairDivision

/-!
# Finite Measurable Partitions as Indivisible Goods

This file packages the reusable bridge used by cake-cutting reductions: once a
measurable space has been cut into finitely many pieces, those pieces can be
treated as indivisible goods whose additive item weights are their measures.
-/

variable {Agent Ω Piece Residual : Type*} [MeasurableSpace Ω]

/-- Aggregate measure obtained by summing a finite family of players' measures. -/
noncomputable def aggregateMeasure [Fintype Agent]
    (μ : Agent → Measure Ω) : Measure Ω :=
  ∑ agent : Agent, μ agent

/-- Each player's measure is dominated by the finite aggregate measure. -/
theorem measure_le_aggregateMeasure [Fintype Agent]
    (μ : Agent → Measure Ω) (agent : Agent) :
    μ agent ≤ aggregateMeasure μ := by
  rw [aggregateMeasure, ← Measure.sum_fintype μ]
  exact Measure.le_sum μ agent

/-- Real-valued version of domination by the finite aggregate measure. -/
theorem measureReal_le_aggregateMeasureReal [Fintype Agent]
    (μ : Agent → Measure Ω)
    [∀ agent, IsFiniteMeasure (μ agent)]
    (agent : Agent) (s : Set Ω) :
    (μ agent).real s ≤ (aggregateMeasure μ).real s := by
  haveI : IsFiniteMeasure (aggregateMeasure μ) := by
    unfold aggregateMeasure
    infer_instance
  exact
    ENNReal.toReal_mono (measure_ne_top (aggregateMeasure μ) s)
      ((measure_le_aggregateMeasure μ agent) s)

/-- If every player's measure of a set is zero, then the aggregate measure is zero there. -/
theorem aggregateMeasure_apply_eq_zero_of_forall
    [Fintype Agent] (μ : Agent → Measure Ω) (s : Set Ω)
    (hzero : ∀ agent, μ agent s = 0) :
    aggregateMeasure μ s = 0 := by
  classical
  simp [aggregateMeasure, hzero]

/-- Real-valued zero version for finite player measures. -/
theorem aggregateMeasureReal_eq_zero_of_forall
    [Fintype Agent] (μ : Agent → Measure Ω)
    [∀ agent, IsFiniteMeasure (μ agent)] (s : Set Ω)
    (hzero : ∀ agent, (μ agent).real s = 0) :
    (aggregateMeasure μ).real s = 0 := by
  haveI : IsFiniteMeasure (aggregateMeasure μ) := by
    unfold aggregateMeasure
    infer_instance
  have hmeasure_zero : aggregateMeasure μ s = 0 := by
    apply aggregateMeasure_apply_eq_zero_of_forall
    intro agent
    exact (measureReal_eq_zero_iff (μ := μ agent) (s := s)).1 (hzero agent)
  simp [Measure.real, hmeasure_zero]

/--
Points whose singleton mass under the aggregate measure exceeds `α`. These are
the atoms that must be split off before applying a scalar small-piece
partition argument to the residual aggregate measure.
-/
def highAggregatePointMasses [Fintype Agent]
    (μ : Agent → Measure Ω) (α : ℝ) : Set Ω :=
  {x | α < (aggregateMeasure μ).real ({x} : Set Ω)}

/--
Piece map that combines a finite set of singleton pieces with a residual
partition indexed by `Residual`.
-/
def finiteSingletonsWithResidualPieceSet
    (H : Finset Ω) (residualSet : Residual → Set Ω) :
    ({x : Ω // x ∈ H} ⊕ Residual) → Set Ω
  | Sum.inl x => {x.1}
  | Sum.inr r => residualSet r

/-- A finite aggregate measure has only finitely many point masses above `α`. -/
theorem highAggregatePointMasses_finite
    [MeasurableSingletonClass Ω] [Fintype Agent]
    (μ : Agent → Measure Ω) [∀ agent, IsFiniteMeasure (μ agent)]
    {α : ℝ} (hα : 0 < α) :
    (highAggregatePointMasses μ α).Finite := by
  haveI : IsFiniteMeasure (aggregateMeasure μ) := by
    unfold aggregateMeasure
    infer_instance
  exact
    Set.Finite.subset
      (AppliedModelingLib.finite_setOf_le_measureReal_singleton
        (μ := aggregateMeasure μ) hα)
      (by
        intro x hx
        exact le_of_lt (by simpa [highAggregatePointMasses] using hx))

/-- Finset version of the large aggregate point masses. -/
noncomputable def highAggregatePointMassesFinset
    [MeasurableSingletonClass Ω] [Fintype Agent]
    (μ : Agent → Measure Ω) [∀ agent, IsFiniteMeasure (μ agent)]
    {α : ℝ} (hα : 0 < α) : Finset Ω :=
  (highAggregatePointMasses_finite μ hα).toFinset

@[simp] theorem mem_highAggregatePointMassesFinset
    [MeasurableSingletonClass Ω] [Fintype Agent]
    (μ : Agent → Measure Ω) [∀ agent, IsFiniteMeasure (μ agent)]
    {α : ℝ} (hα : 0 < α) (x : Ω) :
    x ∈ highAggregatePointMassesFinset μ hα ↔
      x ∈ highAggregatePointMasses μ α := by
  exact (highAggregatePointMasses_finite μ hα).mem_toFinset

@[simp] theorem coe_highAggregatePointMassesFinset
    [MeasurableSingletonClass Ω] [Fintype Agent]
    (μ : Agent → Measure Ω) [∀ agent, IsFiniteMeasure (μ agent)]
    {α : ℝ} (hα : 0 < α) :
    (highAggregatePointMassesFinset μ hα : Set Ω) =
      highAggregatePointMasses μ α := by
  exact (highAggregatePointMasses_finite μ hα).coe_toFinset

/--
After removing the large aggregate point masses, every singleton has residual
aggregate mass at most `α`.
-/
theorem restrict_compl_highAggregatePointMasses_singleton_le
    [MeasurableSingletonClass Ω] [Fintype Agent]
    (μ : Agent → Measure Ω) [∀ agent, IsFiniteMeasure (μ agent)]
    {α : ℝ} (hα : 0 < α) (x : Ω) :
    ((aggregateMeasure μ).restrict (highAggregatePointMasses μ α)ᶜ).real
        ({x} : Set Ω) ≤ α := by
  haveI : IsFiniteMeasure (aggregateMeasure μ) := by
    unfold aggregateMeasure
    infer_instance
  by_cases hx : x ∈ highAggregatePointMasses μ α
  · have hzero_measure :
        ((aggregateMeasure μ).restrict (highAggregatePointMasses μ α)ᶜ)
          ({x} : Set Ω) = 0 := by
      rw [Measure.restrict_apply (MeasurableSet.singleton x)]
      have hempty :
          ({x} : Set Ω) ∩ (highAggregatePointMasses μ α)ᶜ = ∅ := by
        ext y
        by_cases hy : y = x
        · subst y
          simp [hx]
        · simp [hy]
      simp [hempty]
    have hzero_real :
        ((aggregateMeasure μ).restrict (highAggregatePointMasses μ α)ᶜ).real
          ({x} : Set Ω) = 0 := by
      simp [Measure.real, hzero_measure]
    linarith
  · have hle_restrict :
        ((aggregateMeasure μ).restrict (highAggregatePointMasses μ α)ᶜ).real
          ({x} : Set Ω) ≤ (aggregateMeasure μ).real ({x} : Set Ω) := by
      exact
        ENNReal.toReal_mono (measure_ne_top (aggregateMeasure μ) ({x} : Set Ω))
          (Measure.restrict_apply_le
            (μ := aggregateMeasure μ)
            (s := (highAggregatePointMasses μ α)ᶜ)
            (t := ({x} : Set Ω)))
    have hnot : ¬ α < (aggregateMeasure μ).real ({x} : Set Ω) := by
      simpa [highAggregatePointMasses] using hx
    exact hle_restrict.trans (le_of_not_gt hnot)

/--
A finite measurable partition certificate for a family of measure-valued
utilities.

The `piece_value_le` field is the condition needed by the bounded-envy
theorem after the measurable pieces are treated as indivisible goods.  The
cover/disjoint fields record the intended cake-partition semantics; the finite
allocation theorem below only needs the per-piece bound.
-/
structure MeasurePartitionCertificate
    (μ : Agent → Measure Ω) (α : ℝ) (Piece : Type*) where
  pieceSet : Piece → Set Ω
  measurable_piece : ∀ piece, MeasurableSet (pieceSet piece)
  pairwiseDisjoint : Set.PairwiseDisjoint Set.univ pieceSet
  cover : Set.iUnion pieceSet = Set.univ
  piece_value_le : ∀ agent piece, (μ agent).real (pieceSet piece) ≤ α

namespace MeasurePartitionCertificate

variable {μ : Agent → Measure Ω} {α : ℝ}

/-- The additive item weight of a measurable piece for one agent. -/
noncomputable def weight (C : MeasurePartitionCertificate μ α Piece)
    (agent : Agent) (piece : Piece) : ℝ :=
  (μ agent).real (C.pieceSet piece)

theorem weight_nonneg (C : MeasurePartitionCertificate μ α Piece)
    (agent : Agent) (piece : Piece) :
    0 ≤ C.weight agent piece := by
  exact measureReal_nonneg

/-- The induced finite-good valuation obtained from the measurable pieces. -/
noncomputable def valuation [DecidableEq Piece]
    (C : MeasurePartitionCertificate μ α Piece) :
    Valuation Agent Piece :=
  additiveValuation C.weight C.weight_nonneg

@[simp] theorem valuation_value [DecidableEq Piece]
    (C : MeasurePartitionCertificate μ α Piece)
    (agent : Agent) (S : Bundle Piece) :
    (C.valuation).value agent S =
      S.sum (fun piece => (μ agent).real (C.pieceSet piece)) := by
  rfl

/--
The induced valuation has maximum marginal at most the per-piece measure bound
from the certificate.
-/
theorem valuation_marginalBound [DecidableEq Piece]
    (C : MeasurePartitionCertificate μ α Piece) :
    MarginalBound C.valuation α := by
  exact additiveValuation_marginalBound C.weight C.weight_nonneg C.piece_value_le

/--
Any finite measurable partition certificate yields an allocation of its pieces
whose envy is bounded by the certificate's per-piece measure bound.
-/
theorem exists_envyBounded_allocation
    [Finite Agent] [Finite Piece] [DecidableEq Piece] [Nonempty Agent]
    (C : MeasurePartitionCertificate μ α Piece)
    (halpha_nonneg : 0 ≤ α) (pieces : Finset Piece) :
    ∃ A : Allocation Agent Piece,
      IsAllocationOf A pieces ∧ EnvyBoundedBy C.valuation A α := by
  exact
    lmms_theorem_2_1_finite C.valuation halpha_nonneg
      C.valuation_marginalBound pieces

end MeasurePartitionCertificate

/--
Build a player-wise partition certificate from a partition whose pieces are all
small for the aggregate measure. Since each player's measure is dominated by
the aggregate measure, aggregate-small pieces are small for every player.
-/
noncomputable def measurePartitionCertificateOfAggregateBound
    [Fintype Agent] (μ : Agent → Measure Ω)
    [∀ agent, IsFiniteMeasure (μ agent)]
    {α : ℝ} (pieceSet : Piece → Set Ω)
    (hmeas : ∀ piece, MeasurableSet (pieceSet piece))
    (hdisjoint : Set.PairwiseDisjoint Set.univ pieceSet)
    (hcover : Set.iUnion pieceSet = Set.univ)
    (haggregate : ∀ piece, (aggregateMeasure μ).real (pieceSet piece) ≤ α) :
    MeasurePartitionCertificate μ α Piece where
  pieceSet := pieceSet
  measurable_piece := hmeas
  pairwiseDisjoint := hdisjoint
  cover := hcover
  piece_value_le := by
    intro agent piece
    exact (measureReal_le_aggregateMeasureReal μ agent (pieceSet piece)).trans
      (haggregate piece)

/--
Combine finitely many singleton pieces with a residual aggregate-small
partition. Singleton pieces use the supplied player-wise bound; residual pieces
use aggregate domination.
-/
noncomputable def measurePartitionCertificateOfFiniteSingletonsAndResidualAggregate
    [MeasurableSingletonClass Ω] [DecidableEq Ω]
    [Fintype Agent] (μ : Agent → Measure Ω)
    [∀ agent, IsFiniteMeasure (μ agent)]
    {α : ℝ} (H : Finset Ω) (residualSet : Residual → Set Ω)
    (hmeas_residual : ∀ piece, MeasurableSet (residualSet piece))
    (hdisjoint_residual : Set.PairwiseDisjoint Set.univ residualSet)
    (hcover_residual : Set.iUnion residualSet = (H : Set Ω)ᶜ)
    (hsingleton : ∀ agent x, x ∈ H → (μ agent).real ({x} : Set Ω) ≤ α)
    (haggregate_residual :
      ∀ piece, (aggregateMeasure μ).real (residualSet piece) ≤ α) :
    MeasurePartitionCertificate μ α ({x : Ω // x ∈ H} ⊕ Residual) where
  pieceSet := finiteSingletonsWithResidualPieceSet H residualSet
  measurable_piece := by
    intro piece
    cases piece with
    | inl x => exact MeasurableSet.singleton x.1
    | inr r => exact hmeas_residual r
  pairwiseDisjoint := by
    intro piece _ piece' _ hne
    have hres_subset : ∀ r, residualSet r ⊆ (H : Set Ω)ᶜ := by
      intro r y hy
      have hy_union : y ∈ Set.iUnion residualSet := by
        exact Set.mem_iUnion.mpr ⟨r, hy⟩
      simpa [hcover_residual] using hy_union
    cases piece with
    | inl x =>
        cases piece' with
        | inl y =>
            have hxy : x.1 ≠ y.1 := by
              intro hval
              exact hne (by cases x; cases y; simp at hval ⊢; exact hval)
            exact Set.disjoint_singleton.2 hxy
        | inr r =>
            exact Set.disjoint_singleton_left.2
              (by
                intro hxmem
                exact (hres_subset r hxmem) x.2)
    | inr r =>
        cases piece' with
        | inl x =>
            exact Set.disjoint_singleton_right.2
              (by
                intro hxmem
                exact (hres_subset r hxmem) x.2)
        | inr r' =>
            have hrr' : r ≠ r' := by
              intro h
              exact hne (by simp [h])
            exact hdisjoint_residual (by simp) (by simp) hrr'
  cover := by
    ext y
    constructor
    · intro _
      simp
    · intro _
      by_cases hyH : y ∈ H
      · exact Set.mem_iUnion.mpr
          ⟨Sum.inl ⟨y, hyH⟩, by simp [finiteSingletonsWithResidualPieceSet]⟩
      · have hy_residual : y ∈ Set.iUnion residualSet := by
          simpa [hcover_residual] using hyH
        rcases Set.mem_iUnion.mp hy_residual with ⟨r, hyr⟩
        exact Set.mem_iUnion.mpr
          ⟨Sum.inr r, by simpa [finiteSingletonsWithResidualPieceSet] using hyr⟩
  piece_value_le := by
    intro agent piece
    cases piece with
    | inl x => exact hsingleton agent x.1 x.2
    | inr r =>
        exact (measureReal_le_aggregateMeasureReal μ agent (residualSet r)).trans
          (haggregate_residual r)

end FairDivision
end AppliedModelingLib
