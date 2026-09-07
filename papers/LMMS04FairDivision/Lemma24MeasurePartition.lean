import AppliedModelingLib.Foundations.Probability.MeasureAtoms
import AppliedModelingLib.Foundations.Probability.RealIntervalPartition
import AppliedModelingLib.SocialChoice.FairDivision.MeasurePartition

open MeasureTheory Set
open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace Lemma24

/-!
# Measure-Partition Bridge for LMMS Lemma 2.4 and Theorem 2.3

Lemma 2.4 in the paper constructs finitely many measurable pieces of `[0,1]`
whose value is at most `α` for every player.  This file proves the downstream
formal step: any such finite measurable-partition certificate can be treated as
an indivisible-goods instance, and then LMMS Theorem 2.1 allocates those pieces
with envy at most `α`.
-/

variable {Agent Ω Piece : Type*} [MeasurableSpace Ω]

/--
Residual pieces obtained from a real interval partition after finite high
points have been split off.  The `none` piece covers everything outside the
modeled interval; it is used with a support-zero assumption.
-/
def realIntervalResidualSet
    {ν : Measure ℝ} {α a b : ℝ} (H : Finset ℝ)
    (P : AppliedModelingLib.Probability.RealIntervalPartition ν α a b) :
    Option P.Piece → Set ℝ
  | none => (Ioc a b)ᶜ \ (H : Set ℝ)
  | some piece => P.pieceSet piece \ (H : Set ℝ)

theorem realIntervalResidualSet_measurable
    {ν : Measure ℝ} {α a b : ℝ} (H : Finset ℝ)
    (P : AppliedModelingLib.Probability.RealIntervalPartition ν α a b) :
    ∀ piece, MeasurableSet (realIntervalResidualSet H P piece) := by
  intro piece
  cases piece with
  | none =>
      exact measurableSet_Ioc.compl.diff H.measurableSet
  | some piece =>
      exact (P.measurable_piece piece).diff H.measurableSet

theorem realIntervalResidualSet_cover
    {ν : Measure ℝ} {α a b : ℝ} (H : Finset ℝ)
    (P : AppliedModelingLib.Probability.RealIntervalPartition ν α a b) :
    Set.iUnion (realIntervalResidualSet H P) = (H : Set ℝ)ᶜ := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨piece, hxpiece⟩
    cases piece with
    | none => exact hxpiece.2
    | some piece => exact hxpiece.2
  · intro hxH
    by_cases hxI : x ∈ Ioc a b
    · have hxU : x ∈ Set.iUnion P.pieceSet := by
        simpa [P.cover] using hxI
      rcases Set.mem_iUnion.mp hxU with ⟨piece, hxpiece⟩
      exact Set.mem_iUnion.mpr ⟨some piece, ⟨hxpiece, hxH⟩⟩
    · exact Set.mem_iUnion.mpr ⟨none, ⟨hxI, hxH⟩⟩

theorem realIntervalResidualSet_pairwiseDisjoint
    {ν : Measure ℝ} {α a b : ℝ} (H : Finset ℝ)
    (P : AppliedModelingLib.Probability.RealIntervalPartition ν α a b) :
    Set.PairwiseDisjoint Set.univ (realIntervalResidualSet H P) := by
  have hpiece_subset : ∀ piece, P.pieceSet piece ⊆ Ioc a b := by
    intro piece x hx
    have hxU : x ∈ Set.iUnion P.pieceSet := Set.mem_iUnion.mpr ⟨piece, hx⟩
    simpa [P.cover] using hxU
  intro piece _ piece' _ hne
  cases piece with
  | none =>
      cases piece' with
      | none => exact (hne rfl).elim
      | some piece' =>
          change Disjoint ((Ioc a b)ᶜ \ (H : Set ℝ))
            (P.pieceSet piece' \ (H : Set ℝ))
          rw [Set.disjoint_left]
          intro x hx_out hx_piece
          exact hx_out.1 (hpiece_subset piece' hx_piece.1)
  | some piece =>
      cases piece' with
      | none =>
          change Disjoint (P.pieceSet piece \ (H : Set ℝ))
            ((Ioc a b)ᶜ \ (H : Set ℝ))
          rw [Set.disjoint_left]
          intro x hx_piece hx_out
          exact hx_out.1 (hpiece_subset piece hx_piece.1)
      | some piece' =>
          have hne_piece : piece ≠ piece' := by
            intro h
            exact hne (by simp [h])
          change Disjoint (P.pieceSet piece \ (H : Set ℝ))
            (P.pieceSet piece' \ (H : Set ℝ))
          exact
            (P.pairwiseDisjoint (by simp) (by simp) hne_piece).mono
              (by intro x hx; exact hx.1)
              (by intro x hx; exact hx.1)

theorem realIntervalResidualSet_aggregate_le
    [Fintype Agent] {μ : Agent → Measure ℝ}
    [∀ agent, IsFiniteMeasure (μ agent)]
    {α a b : ℝ} (hα_nonneg : 0 ≤ α) (H : Finset ℝ)
    (P : AppliedModelingLib.Probability.RealIntervalPartition
      ((aggregateMeasure μ).restrict (H : Set ℝ)ᶜ) α a b)
    (haggregate_support :
      (aggregateMeasure μ).real ((Ioc a b)ᶜ) = 0) :
    ∀ piece, (aggregateMeasure μ).real
      (realIntervalResidualSet H P piece) ≤ α := by
  haveI : IsFiniteMeasure (aggregateMeasure μ) := by
    unfold aggregateMeasure
    infer_instance
  intro piece
  cases piece with
  | none =>
      have hsubset :
          (Ioc a b)ᶜ \ (H : Set ℝ) ⊆ (Ioc a b)ᶜ := by
        intro x hx
        exact hx.1
      have hle :
          (aggregateMeasure μ).real ((Ioc a b)ᶜ \ (H : Set ℝ)) ≤
            (aggregateMeasure μ).real ((Ioc a b)ᶜ) :=
        measureReal_mono hsubset (measure_ne_top (aggregateMeasure μ) _)
      calc
        (aggregateMeasure μ).real ((Ioc a b)ᶜ \ (H : Set ℝ)) ≤
            (aggregateMeasure μ).real ((Ioc a b)ᶜ) := hle
        _ = 0 := haggregate_support
        _ ≤ α := hα_nonneg
  | some piece =>
      have heq :
          (aggregateMeasure μ).real (P.pieceSet piece \ (H : Set ℝ)) =
            ((aggregateMeasure μ).restrict (H : Set ℝ)ᶜ).real
              (P.pieceSet piece) := by
        simp [Measure.real, Measure.restrict_apply (P.measurable_piece piece),
          Set.diff_eq, Set.inter_comm]
      exact heq.trans_le (P.piece_mass_le piece)

/--
Paper atom bound for a measure-valued utility: every atom has value at most
`α`, matching the hypothesis used before Lemma 2.4.
-/
abbrev PaperAtomsBoundedBy (μ : Measure Ω) (α : ℝ) : Prop :=
  AppliedModelingLib.AtomsBoundedBy μ α

/--
The source proof first uses the atom bound to conclude that every point mass is
at most `α`.  This lemma formalizes that reduction for the paper-style atom
predicate.
-/
theorem paper_atom_bound_implies_point_mass_bound
    (μ : Measure Ω) {α : ℝ}
    (halpha_nonneg : 0 ≤ α) (hatoms : PaperAtomsBoundedBy μ α) :
    ∀ x : Ω, μ.real ({x} : Set Ω) ≤ α := by
  exact AppliedModelingLib.atomsBoundedBy_measureReal_singleton_le μ halpha_nonneg hatoms

/--
Paper-facing certificate for the output of Lemma 2.4.  For the source theorem,
`Ω` should be the measurable subtype corresponding to `[0,1]`; the certificate
records the finite measurable pieces, disjointness, cover, and the per-player
`α` bound on each piece.
-/
abbrev PaperMeasurePartitionCertificate
    (μ : Agent → Measure Ω) (α : ℝ) (Piece : Type*) :=
  MeasurePartitionCertificate μ α Piece

/--
Theorem 2.3 bridge from Lemma 2.4's partition output to the finite
indivisible-goods theorem.  Once the paper's measure construction supplies a
finite certificate, the induced finite valuation has marginal value at most
`α`, so Theorem 2.1 gives an allocation of the pieces with envy at most `α`.
-/
theorem theorem2_3_from_measure_partition_certificate
    [Finite Agent] [Finite Piece] [DecidableEq Piece] [Nonempty Agent]
    {μ : Agent → Measure Ω} {α : ℝ}
    (halpha_nonneg : 0 ≤ α)
    (C : PaperMeasurePartitionCertificate μ α Piece)
    (pieces : Finset Piece) :
    ∃ A : Allocation Agent Piece,
      IsAllocationOf A pieces ∧ EnvyBoundedBy C.valuation A α := by
  exact C.exists_envyBounded_allocation halpha_nonneg pieces

/--
Source-shaped version for the full finite partition supplied by Lemma 2.4:
allocate all pieces in the partition.
-/
theorem theorem2_3_from_measure_partition_certificate_univ
    [Fintype Agent] [Fintype Piece] [DecidableEq Piece] [Nonempty Agent]
    {μ : Agent → Measure Ω} {α : ℝ}
    (halpha_nonneg : 0 ≤ α)
    (C : PaperMeasurePartitionCertificate μ α Piece) :
    ∃ A : Allocation Agent Piece,
      IsAllocationOf A (Finset.univ : Finset Piece) ∧
        EnvyBoundedBy C.valuation A α := by
  exact theorem2_3_from_measure_partition_certificate halpha_nonneg C Finset.univ

/--
Aggregate-measure version of the Theorem 2.3 bridge.  It is enough to partition
the cake into pieces whose aggregate value, summed over all players, is at most
`α`: each individual player's value is then also at most `α`, so the finite
LMMS theorem applies.
-/
theorem theorem2_3_from_aggregate_partition
    [Fintype Agent] [Fintype Piece] [DecidableEq Piece] [Nonempty Agent]
    {μ : Agent → Measure Ω} [∀ agent, IsFiniteMeasure (μ agent)]
    {α : ℝ} (halpha_nonneg : 0 ≤ α)
    (pieceSet : Piece → Set Ω)
    (hmeas : ∀ piece, MeasurableSet (pieceSet piece))
    (hdisjoint : Set.PairwiseDisjoint Set.univ pieceSet)
    (hcover : Set.iUnion pieceSet = Set.univ)
    (haggregate :
      ∀ piece, (aggregateMeasure μ).real (pieceSet piece) ≤ α) :
    ∃ A : Allocation Agent Piece,
      IsAllocationOf A (Finset.univ : Finset Piece) ∧
        EnvyBoundedBy
          (measurePartitionCertificateOfAggregateBound μ pieceSet hmeas hdisjoint hcover
            haggregate).valuation A α := by
  exact
    theorem2_3_from_measure_partition_certificate_univ halpha_nonneg
      (measurePartitionCertificateOfAggregateBound μ pieceSet hmeas hdisjoint hcover
        haggregate)

/--
Theorem 2.3 bridge after splitting finitely many point masses off from the
aggregate measure.  Singleton pieces use the point-mass bound from the paper's
atom hypothesis; residual pieces only need to be small for the aggregate
measure.
-/
theorem theorem2_3_from_finite_singletons_and_residual_aggregate_partition
    [MeasurableSingletonClass Ω] [DecidableEq Ω]
    [Fintype Agent] [Nonempty Agent]
    {μ : Agent → Measure Ω} [∀ agent, IsFiniteMeasure (μ agent)]
    {Residual : Type*} [Fintype Residual] [DecidableEq Residual]
    {α : ℝ} (halpha_nonneg : 0 ≤ α)
    (H : Finset Ω) (residualSet : Residual → Set Ω)
    (hmeas_residual : ∀ piece, MeasurableSet (residualSet piece))
    (hdisjoint_residual : Set.PairwiseDisjoint Set.univ residualSet)
    (hcover_residual : Set.iUnion residualSet = (H : Set Ω)ᶜ)
    (hsingleton : ∀ agent x, x ∈ H → (μ agent).real ({x} : Set Ω) ≤ α)
    (haggregate_residual :
      ∀ piece, (aggregateMeasure μ).real (residualSet piece) ≤ α) :
    ∃ A : Allocation Agent ({x : Ω // x ∈ H} ⊕ Residual),
      IsAllocationOf A (Finset.univ : Finset ({x : Ω // x ∈ H} ⊕ Residual)) ∧
        EnvyBoundedBy
          (measurePartitionCertificateOfFiniteSingletonsAndResidualAggregate
            μ H residualSet hmeas_residual hdisjoint_residual hcover_residual
            hsingleton haggregate_residual).valuation A α := by
  exact
    theorem2_3_from_measure_partition_certificate_univ halpha_nonneg
      (measurePartitionCertificateOfFiniteSingletonsAndResidualAggregate
        μ H residualSet hmeas_residual hdisjoint_residual hcover_residual
        hsingleton haggregate_residual)

/--
Variant of the high-atom split bridge that derives the singleton-piece bounds
directly from the paper atom hypothesis.  This is the shape needed after the
aggregate construction chooses a finite set of point masses to split off.
-/
theorem theorem2_3_from_finite_singletons_and_residual_aggregate_partition_atom_bound
    [MeasurableSingletonClass Ω] [DecidableEq Ω]
    [Fintype Agent] [Nonempty Agent]
    {μ : Agent → Measure Ω} [∀ agent, IsFiniteMeasure (μ agent)]
    {Residual : Type*} [Fintype Residual] [DecidableEq Residual]
    {α : ℝ} (halpha_nonneg : 0 ≤ α)
    (hatoms : ∀ agent, PaperAtomsBoundedBy (μ agent) α)
    (H : Finset Ω) (residualSet : Residual → Set Ω)
    (hmeas_residual : ∀ piece, MeasurableSet (residualSet piece))
    (hdisjoint_residual : Set.PairwiseDisjoint Set.univ residualSet)
    (hcover_residual : Set.iUnion residualSet = (H : Set Ω)ᶜ)
    (haggregate_residual :
      ∀ piece, (aggregateMeasure μ).real (residualSet piece) ≤ α) :
    ∃ A : Allocation Agent ({x : Ω // x ∈ H} ⊕ Residual),
      IsAllocationOf A (Finset.univ : Finset ({x : Ω // x ∈ H} ⊕ Residual)) ∧
        EnvyBoundedBy
          (measurePartitionCertificateOfFiniteSingletonsAndResidualAggregate
            μ H residualSet hmeas_residual hdisjoint_residual hcover_residual
            (fun agent x _ => paper_atom_bound_implies_point_mass_bound
              (μ agent) halpha_nonneg (hatoms agent) x)
            haggregate_residual).valuation A α := by
  exact
    theorem2_3_from_finite_singletons_and_residual_aggregate_partition
      halpha_nonneg H residualSet hmeas_residual hdisjoint_residual
      hcover_residual
      (fun agent x hx => paper_atom_bound_implies_point_mass_bound
        (μ agent) halpha_nonneg (hatoms agent) x)
      haggregate_residual

/--
Real-supported Theorem 2.3 assembly from a residual interval partition.  A
finite high-point set `H` is allocated as singleton pieces; the supplied
interval partition is applied to the aggregate measure restricted to `Hᶜ`, and
each residual interval piece is subtractively cleaned by removing `H`.
-/
theorem theorem2_3_from_real_interval_residual_partition_atom_bound
    [Fintype Agent] [Nonempty Agent]
    {μ : Agent → Measure ℝ} [∀ agent, IsFiniteMeasure (μ agent)]
    {α a b : ℝ} (halpha_nonneg : 0 ≤ α)
    (hatoms : ∀ agent, PaperAtomsBoundedBy (μ agent) α)
    (H : Finset ℝ)
    (P : AppliedModelingLib.Probability.RealIntervalPartition
      ((aggregateMeasure μ).restrict (H : Set ℝ)ᶜ) α a b)
    (haggregate_support :
      (aggregateMeasure μ).real ((Ioc a b)ᶜ) = 0) :
    letI := P.instFintype
    letI := P.instDecidableEq
    ∃ A : Allocation Agent ({x : ℝ // x ∈ H} ⊕ Option P.Piece),
      IsAllocationOf A
          (Finset.univ : Finset ({x : ℝ // x ∈ H} ⊕ Option P.Piece)) ∧
        EnvyBoundedBy
          (measurePartitionCertificateOfFiniteSingletonsAndResidualAggregate
            μ H (realIntervalResidualSet H P)
            (realIntervalResidualSet_measurable H P)
            (realIntervalResidualSet_pairwiseDisjoint H P)
            (realIntervalResidualSet_cover H P)
            (fun agent x _ => paper_atom_bound_implies_point_mass_bound
              (μ agent) halpha_nonneg (hatoms agent) x)
            (realIntervalResidualSet_aggregate_le
              (Agent := Agent) halpha_nonneg H P haggregate_support)).valuation A α := by
  letI := P.instFintype
  letI := P.instDecidableEq
  exact
    theorem2_3_from_finite_singletons_and_residual_aggregate_partition_atom_bound
      halpha_nonneg hatoms H (realIntervalResidualSet H P)
      (realIntervalResidualSet_measurable H P)
      (realIntervalResidualSet_pairwiseDisjoint H P)
      (realIntervalResidualSet_cover H P)
      (realIntervalResidualSet_aggregate_le
        (Agent := Agent) halpha_nonneg H P haggregate_support)

/--
Real-supported Theorem 2.3 construction.  The finite set `H` is chosen as the
aggregate point masses above `α / 2`; the residual aggregate measure then has
all singleton masses at most `α / 2`, so the reusable real-interval partition
theorem supplies the remaining finite pieces.
-/
theorem theorem2_3_real_interval_supported_atom_bound
    [Fintype Agent] [Nonempty Agent]
    {μ : Agent → Measure ℝ} [∀ agent, IsFiniteMeasure (μ agent)]
    {α a b : ℝ} (hα : 0 < α)
    (hatoms : ∀ agent, PaperAtomsBoundedBy (μ agent) α)
    (haggregate_support :
      (aggregateMeasure μ).real ((Ioc a b)ᶜ) = 0) :
    ∃ H : Finset ℝ,
      ∃ P : AppliedModelingLib.Probability.RealIntervalPartition
        ((aggregateMeasure μ).restrict (H : Set ℝ)ᶜ) α a b,
        letI := P.instFintype
        letI := P.instDecidableEq
        ∃ A : Allocation Agent ({x : ℝ // x ∈ H} ⊕ Option P.Piece),
          IsAllocationOf A
              (Finset.univ : Finset ({x : ℝ // x ∈ H} ⊕ Option P.Piece)) ∧
            EnvyBoundedBy
              (measurePartitionCertificateOfFiniteSingletonsAndResidualAggregate
                μ H (realIntervalResidualSet H P)
                (realIntervalResidualSet_measurable H P)
                (realIntervalResidualSet_pairwiseDisjoint H P)
                (realIntervalResidualSet_cover H P)
                (fun agent x _ => paper_atom_bound_implies_point_mass_bound
                  (μ agent) (le_of_lt hα) (hatoms agent) x)
                (realIntervalResidualSet_aggregate_le
                  (Agent := Agent) (le_of_lt hα) H P haggregate_support)).valuation A α := by
  classical
  have hhalf : 0 < α / 2 := by linarith
  let H : Finset ℝ := highAggregatePointMassesFinset μ hhalf
  haveI : IsFiniteMeasure (aggregateMeasure μ) := by
    unfold aggregateMeasure
    infer_instance
  haveI : IsFiniteMeasure ((aggregateMeasure μ).restrict (H : Set ℝ)ᶜ) := by
    infer_instance
  have hsingleton_residual :
      ∀ x : ℝ,
        ((aggregateMeasure μ).restrict (H : Set ℝ)ᶜ).real ({x} : Set ℝ) ≤ α / 2 := by
    intro x
    dsimp [H]
    simpa using restrict_compl_highAggregatePointMasses_singleton_le μ hhalf x
  rcases
      AppliedModelingLib.Probability.exists_realIntervalPartition_of_singleton_le_half
        ((aggregateMeasure μ).restrict (H : Set ℝ)ᶜ) hα hsingleton_residual with
    ⟨P⟩
  refine ⟨H, P, ?_⟩
  exact
    theorem2_3_from_real_interval_residual_partition_atom_bound
      (le_of_lt hα) hatoms H P haggregate_support

end Lemma24
end LMMS04FairDivision
