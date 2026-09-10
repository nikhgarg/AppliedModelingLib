import AppliedModelingLib.Foundations.Math.LinearCompressedSensing
import AppliedModelingLib.Foundations.Math.MatrixRankInequalities
import AppliedModelingLib.Foundations.Math.RankBounds
import AppliedModelingLib.Foundations.Math.Asymptotics
import AppliedModelingLib.Foundations.Probability.RademacherCompressedSensing

/-!
# Paper-Facing Theorems: Linear Representation Hypothesis Capacity

This file contains source-shaped definitions and proved theorem seams for
Garg-Kleinberg-Peng, "How Many Features Can a Language Model Store Under the
Linear Representation Hypothesis?"
-/

namespace GKP26LinearRepresentationHypothesis

open AppliedModelingLib.Math.LinearCompressedSensing
open AppliedModelingLib.Math.MatrixRankInequalities
open AppliedModelingLib.Math.RankBounds
open AppliedModelingLib.Probability.RademacherMatrix
open Filter Topology

/-- Feature vectors in the paper's `R^m`. -/
abbrev FeatureVector (m : ℕ) : Type :=
  Fin m → ℝ

/-- Columns of an embedding/probe matrix in the paper's `R^d`. -/
abbrev ColumnVector (d : ℕ) : Type :=
  Fin d → ℝ

/-- A representation or probe matrix, viewed by its feature-indexed columns. -/
abbrev FeatureMatrix (m d : ℕ) : Type :=
  Fin m → ColumnVector d

/-- Euclidean norm of a representation/probe column. -/
noncomputable abbrev columnNorm {d : ℕ} (x : ColumnVector d) : ℝ :=
  vectorNorm x

/-- Unit-normalized representation/probe column. -/
noncomputable abbrev normalizedColumn {d : ℕ} (x : ColumnVector d) : ColumnVector d :=
  normalizedVector x

/-- Correlation of two representation/probe columns after unit normalization. -/
noncomputable abbrev columnCorrelation {d : ℕ}
    (x y : ColumnVector d) : ℝ :=
  vectorCorrelation x y

theorem columnCorrelation_eq_dot_normalized {d : ℕ}
    (x y : ColumnVector d) :
    columnCorrelation x y =
      AppliedModelingLib.FiniteDimensionalNorms.dot (normalizedColumn x) (normalizedColumn y) := by
  rfl

theorem columnCorrelation_comm {d : ℕ}
    (x y : ColumnVector d) :
    columnCorrelation x y = columnCorrelation y x := by
  exact vectorCorrelation_comm x y

/-- Geometry Proposition 1 construction: original feature column inside `m+2`. -/
def geometry1FeatureIndex {m : ℕ} (i : Fin m) : Fin (m + 2) :=
  ⟨i.1, by omega⟩

/-- Geometry Proposition 1 construction: the common representation direction `a*`. -/
def geometry1AStarIndex (m : ℕ) : Fin (m + 2) :=
  ⟨m, by omega⟩

/-- Geometry Proposition 1 construction: the common probe direction `b*`. -/
def geometry1BStarIndex (m : ℕ) : Fin (m + 2) :=
  ⟨m + 1, by omega⟩

@[simp] theorem geometry1FeatureIndex_injective {m : ℕ} :
    Function.Injective (geometry1FeatureIndex (m := m)) := by
  intro i j h
  ext
  simpa [geometry1FeatureIndex] using congrArg Fin.val h

@[simp] theorem geometry1FeatureIndex_ne_aStar {m : ℕ} (i : Fin m) :
    geometry1FeatureIndex i ≠ geometry1AStarIndex m := by
  intro h
  have hval := congrArg Fin.val h
  simp [geometry1FeatureIndex, geometry1AStarIndex] at hval
  omega

@[simp] theorem geometry1FeatureIndex_ne_bStar {m : ℕ} (i : Fin m) :
    geometry1FeatureIndex i ≠ geometry1BStarIndex m := by
  intro h
  have hval := congrArg Fin.val h
  simp [geometry1FeatureIndex, geometry1BStarIndex] at hval
  omega

@[simp] theorem geometry1AStar_ne_bStar (m : ℕ) :
    geometry1AStarIndex m ≠ geometry1BStarIndex m := by
  intro h
  have hval := congrArg Fin.val h
  simp [geometry1AStarIndex, geometry1BStarIndex] at hval

/-- Geometry Proposition 1 representation columns `a_i = c_i + lambda a*`. -/
noncomputable def geometry1RepresentationMatrix {m d : ℕ}
    (C : Fin (m + 2) → ColumnVector d) (lambda : ℝ) : FeatureMatrix m d :=
  fun i r => C (geometry1FeatureIndex i) r +
    lambda * C (geometry1AStarIndex m) r

/-- Geometry Proposition 1 probe columns `b_i = c_i + lambda b*`. -/
noncomputable def geometry1ProbeMatrix {m d : ℕ}
    (C : Fin (m + 2) → ColumnVector d) (lambda : ℝ) : FeatureMatrix m d :=
  fun i r => C (geometry1FeatureIndex i) r +
    lambda * C (geometry1BStarIndex m) r

theorem geometry1_probe_representation_inner_eq
    {m d : ℕ} (C : Fin (m + 2) → ColumnVector d) (lambda : ℝ)
    (i j : Fin m) :
    inner (geometry1ProbeMatrix C lambda i)
        (geometry1RepresentationMatrix C lambda j) =
      inner (C (geometry1FeatureIndex i)) (C (geometry1FeatureIndex j)) +
        lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) +
        lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex j)) +
        lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m)) := by
  simpa [geometry1ProbeMatrix, geometry1RepresentationMatrix] using
    inner_add_smul_add_smul
      (Coord := Fin d) lambda
      (C (geometry1FeatureIndex i)) (C (geometry1BStarIndex m))
      (C (geometry1FeatureIndex j)) (C (geometry1AStarIndex m))

/-- Paper notation: the nonzero support of a finite feature vector. -/
noncomputable abbrev featureSupport {m : ℕ} (z : FeatureVector m) : Finset (Fin m) :=
  support z

/-- Paper notation: `z` is `k`-sparse. -/
abbrev kSparse {m : ℕ} (k : ℕ) (z : FeatureVector m) : Prop :=
  KSparse k z

/-- Paper notation: `z in [-1,1]^m`. -/
abbrev inUnitBox {m : ℕ} (z : FeatureVector m) : Prop :=
  InUnitBox z

/-- Paper notation: `z in {0,1}^m`. -/
abbrev inZeroOne {m : ℕ} (z : FeatureVector m) : Prop :=
  InZeroOne z

/-- Paper notation: coordinate `i` of `B^T A z`. -/
abbrev recoveredCoordinate {m d : ℕ}
    (A B : FeatureMatrix m d) (z : FeatureVector m) (i : Fin m) : ℝ :=
  linearProbe A B z i

/-- Paper notation for the nonlinear compressed-sensing measurement `Az`. -/
def compressedSensingMeasurement {m d : ℕ}
    (A : FeatureMatrix m d) (z : FeatureVector m) : ColumnVector d :=
  fun r => ∑ i : Fin m, z i * A i r

/--
Basis-pursuit exact recovery for a measurement matrix `A`: every `k`-sparse
feature vector is the unique `l1` minimizer among vectors with the same
measurement.
-/
def basisPursuitExactRecovery {m d : ℕ}
    (A : FeatureMatrix m d) (k : ℕ) : Prop :=
  ∀ z : FeatureVector m, kSparse k z →
    ∀ z' : FeatureVector m,
      compressedSensingMeasurement A z' = compressedSensingMeasurement A z →
        AppliedModelingLib.FiniteDimensionalNorms.l1 z' ≤
          AppliedModelingLib.FiniteDimensionalNorms.l1 z →
        z' = z

/--
Paper-local name for the standard deterministic nullspace property used in
classical compressed sensing.
-/
abbrev compressedSensingNullspaceProperty {m d : ℕ}
    (A : FeatureMatrix m d) (k : ℕ) : Prop :=
  NullspaceProperty A k

/--
Paper-local name for the finite restricted isometry property.  The paper cites
classical compressed-sensing results rather than proving random RIP matrix
existence, but this predicate is the standard deterministic route into the
nullspace-property/basis-pursuit theorem.
-/
abbrev compressedSensingRestrictedIsometry {m d : ℕ}
    (A : FeatureMatrix m d) (s : ℕ) (delta : ℝ) : Prop :=
  RestrictedIsometryProperty A s delta

/--
Paper-local name for supportwise RIP.  Random-matrix proofs usually first show
near-isometry on every fixed support and then union-bound over the supports.
-/
abbrev compressedSensingRestrictedIsometryOnSupport {m d : ℕ}
    (A : FeatureMatrix m d) (S : Finset (Fin m)) (delta : ℝ) : Prop :=
  RestrictedIsometryOnSupport A S delta

/-- Finite family of all paper feature supports of cardinality at most `s`. -/
noncomputable abbrev compressedSensingSupportFinsetsCardLe (m s : ℕ) :
    Finset (Finset (Fin m)) :=
  supportFinsetsCardLe (Feature := Fin m) s

/--
Deterministic compressed-sensing bridge: the standard nullspace property
implies the paper's basis-pursuit exact-recovery predicate.
-/
theorem basisPursuitExactRecovery_of_compressedSensingNullspaceProperty
    {m d k : ℕ} {A : FeatureMatrix m d}
    (hnsp : compressedSensingNullspaceProperty A k) :
    basisPursuitExactRecovery A k := by
  classical
  have hshared : BasisPursuitExactRecovery A k :=
    AppliedModelingLib.Math.LinearCompressedSensing.basisPursuitExactRecovery_of_nullspaceProperty
      hnsp
  intro z hz z' hmeas hl1
  exact hshared z hz z'
    (by simpa [compressedSensingMeasurement, measurement] using hmeas)
    hl1

theorem basisPursuitExactRecovery_identityFeatureMatrix
    (m k : ℕ) :
    basisPursuitExactRecovery
      (featureIdentityMatrix : FeatureMatrix m m) k :=
  AppliedModelingLib.Math.LinearCompressedSensing.basisPursuitExactRecovery_featureIdentityMatrix
    (Feature := Fin m) k

/--
Deterministic compressed-sensing bridge: RIP at order `3k` with constant below
`2/5` implies the standard strict nullspace property.
-/
theorem compressedSensingNullspaceProperty_of_restrictedIsometry_three_mul
    {m d k : ℕ} {delta : ℝ} {A : FeatureMatrix m d}
    (hk : 0 < k) (hdelta_nonneg : 0 ≤ delta) (hdelta : delta < 2 / 5)
    (hrip : compressedSensingRestrictedIsometry A (3 * k) delta) :
    compressedSensingNullspaceProperty A k :=
  AppliedModelingLib.Math.LinearCompressedSensing.nullspaceProperty_of_restrictedIsometry_three_mul
    (A := A) (k := k) (δ := delta) hk hdelta_nonneg hdelta hrip

/--
Supportwise RIP bridge: it is enough to prove near-isometry on every support
of size at most `s`.
-/
theorem compressedSensingRestrictedIsometry_of_forall_support_card_le
    {m d s : ℕ} {delta : ℝ} {A : FeatureMatrix m d}
    (h :
      ∀ S : Finset (Fin m), S.card ≤ s →
        compressedSensingRestrictedIsometryOnSupport A S delta) :
    compressedSensingRestrictedIsometry A s delta :=
  AppliedModelingLib.Math.LinearCompressedSensing.restrictedIsometryProperty_of_forall_support_card_le
    (A := A) (s := s) (δ := delta) h

/--
Finite-family supportwise RIP bridge, ready for a union-bound proof over all
supports of size at most `s`.
-/
theorem compressedSensingRestrictedIsometry_of_forall_supportFinsetsCardLe
    {m d s : ℕ} {delta : ℝ} {A : FeatureMatrix m d}
    (h :
      ∀ S ∈ compressedSensingSupportFinsetsCardLe m s,
        compressedSensingRestrictedIsometryOnSupport A S delta) :
    compressedSensingRestrictedIsometry A s delta :=
  AppliedModelingLib.Math.LinearCompressedSensing.restrictedIsometryProperty_of_forall_supportFinsetsCardLe
    (A := A) (s := s) (δ := delta) h

/--
Deterministic compressed-sensing bridge through RIP, in the paper's
basis-pursuit vocabulary.
-/
theorem basisPursuitExactRecovery_of_restrictedIsometry_three_mul
    {m d k : ℕ} {delta : ℝ} {A : FeatureMatrix m d}
    (hk : 0 < k) (hdelta_nonneg : 0 ≤ delta) (hdelta : delta < 2 / 5)
    (hrip : compressedSensingRestrictedIsometry A (3 * k) delta) :
    basisPursuitExactRecovery A k :=
  basisPursuitExactRecovery_of_compressedSensingNullspaceProperty
    (compressedSensingNullspaceProperty_of_restrictedIsometry_three_mul
      (A := A) (k := k) (delta := delta)
      hk hdelta_nonneg hdelta hrip)

/--
Deterministic compressed-sensing bridge through mutual incoherence.  This is a
standard sufficient condition for exact basis-pursuit recovery, although it has
the stronger `k^2`-scale behavior typical of coherence arguments rather than
the classical `k log(m/k)` RIP scale.
-/
theorem basisPursuitExactRecovery_of_muIncoherent
    {m d k : ℕ} {A : FeatureMatrix m d} {mu : ℝ}
    (hmu : 0 ≤ mu) (hA : MuIncoherentLE A mu)
    (hbound : (k : ℝ) * mu < 1 / 2) :
    basisPursuitExactRecovery A k := by
  classical
  have hshared : BasisPursuitExactRecovery A k :=
    AppliedModelingLib.Math.LinearCompressedSensing.basisPursuitExactRecovery_of_muIncoherentLE
      hmu hA hbound
  intro z hz z' hmeas hl1
  exact hshared z hz z'
    (by simpa [compressedSensingMeasurement, measurement] using hmeas)
    hl1

/-- Paper notation for the feature-by-feature matrix `B^T A`. -/
noncomputable abbrev interferenceMatrix {m d : ℕ}
    (A B : FeatureMatrix m d) : Matrix (Fin m) (Fin m) ℝ :=
  crossInnerMatrix A B

@[simp] theorem interferenceMatrix_apply {m d : ℕ}
    (A B : FeatureMatrix m d) (i j : Fin m) :
    interferenceMatrix A B i j = inner (B i) (A j) := by
  rfl

/--
Symmetrized interference matrix `(B^T A + A^T B) / 2`.  This keeps the
threshold/lower-bound obstruction inside Hermitian trace-rank estimates while a
large symmetrized entry still certifies a large directed interference entry.
-/
noncomputable def symmetrizedInterferenceMatrix {m d : ℕ}
    (A B : FeatureMatrix m d) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j =>
    (inner (B i) (A j) + inner (B j) (A i)) / 2

@[simp] theorem symmetrizedInterferenceMatrix_apply {m d : ℕ}
    (A B : FeatureMatrix m d) (i j : Fin m) :
    symmetrizedInterferenceMatrix A B i j =
      (inner (B i) (A j) + inner (B j) (A i)) / 2 := by
  rfl

theorem symmetrizedInterferenceMatrix_symmetric {m d : ℕ}
    (A B : FeatureMatrix m d) :
    ∀ i j : Fin m,
      symmetrizedInterferenceMatrix A B i j =
        symmetrizedInterferenceMatrix A B j i := by
  intro i j
  simp [symmetrizedInterferenceMatrix, add_comm]

theorem symmetrizedInterferenceMatrix_diag_eq {m d : ℕ}
    {A B : FeatureMatrix m d} (hdiag : ∀ i : Fin m, inner (B i) (A i) = 1)
    (i : Fin m) :
    symmetrizedInterferenceMatrix A B i i = 1 := by
  simp [symmetrizedInterferenceMatrix, hdiag i]

theorem symmetrizedInterferenceMatrix_submatrix_dot_factorization
    {m d : ℕ} (A B : FeatureMatrix m d) (t : Finset (Fin m)) :
    ∀ x y : {j // j ∈ t},
      ((symmetrizedInterferenceMatrix A B).submatrix Subtype.val Subtype.val) x y =
        ∑ r : Sum (Fin d) (Fin d),
          (match r with
            | Sum.inl a => B x.1 a / 2
            | Sum.inr a => A x.1 a / 2) *
          (match r with
            | Sum.inl a => A y.1 a
            | Sum.inr a => B y.1 a) := by
  intro x y
  rw [Fintype.sum_sum_type]
  simp [symmetrizedInterferenceMatrix, AppliedModelingLib.Math.LinearCompressedSensing.inner,
    mul_comm]
  ring_nf
  rw [Finset.sum_mul, Finset.sum_mul]
  simp [mul_comm]

/--
Directed off-diagonal entries of `B^T A` whose absolute value is larger than
`eta`.  This is the ordered-pair version of the interference relation used in
the lower-bound and binary-threshold proofs.
-/
noncomputable abbrev largeInterferencePairFinset {m d : ℕ}
    (A B : FeatureMatrix m d) (eta : ℝ) : Finset (Fin m × Fin m) :=
  largeOffdiagPairFinset A B eta

/-- Large off-diagonal entries in row `i` of `B^T A`. -/
noncomputable abbrev largeInterferenceRowFinset {m d : ℕ}
    (A B : FeatureMatrix m d) (eta : ℝ) (i : Fin m) : Finset (Fin m) :=
  largeOffdiagRowFinset A B eta i

/--
The undirected interference graph used in the lower-bound proof: two features
are adjacent when either direction of `B^T A` is a large off-diagonal entry.
-/
noncomputable abbrev largeInterferenceGraph {m d : ℕ}
    (A B : FeatureMatrix m d) (eta : ℝ) : SimpleGraph (Fin m) :=
  largeOffdiagGraph A B eta

/--
The source condition defining linear compressed sensing feasibility at dimension
`d`: there are representation and probe matrices whose linear recovery error is
less than `epsilon` for every `k`-sparse vector in the unit box.
-/
def linearRecoveryCondition {m d : ℕ}
    (A B : FeatureMatrix m d) (k : ℕ) (epsilon : ℝ) : Prop :=
  ∀ z : FeatureVector m, kSparse k z → inUnitBox z →
    SupErrorLt A B z epsilon

/-- Feasibility predicate underlying the paper's `d(m,k,epsilon)`. -/
def linearCompressedSensingFeasible (m k d : ℕ) (epsilon : ℝ) : Prop :=
  ∃ A B : FeatureMatrix m d, linearRecoveryCondition A B k epsilon

/--
The exact "smallest `d`" predicate for the paper's `d(m,k,epsilon)`.
The paper's asymptotic theorems can be stated either through this predicate or
through the equivalent eventual feasibility/lower-bound wrappers.
-/
def linearCompressedSensingDimensionValue
    (m k : ℕ) (epsilon : ℝ) (d : ℕ) : Prop :=
  linearCompressedSensingFeasible m k d epsilon ∧
    ∀ d' : ℕ, linearCompressedSensingFeasible m k d' epsilon → d ≤ d'

/-- Zero-pad a paper feature matrix into a larger coordinate dimension. -/
def padFeatureMatrix {m d D : ℕ} (h : d ≤ D)
    (A : FeatureMatrix m d) : FeatureMatrix m D :=
  fun i => padFinVector h (A i)

theorem inner_padFeatureMatrix {m d D : ℕ} (h : d ≤ D)
    (A B : FeatureMatrix m d) (i j : Fin m) :
    inner (padFeatureMatrix h B i) (padFeatureMatrix h A j) =
      inner (B i) (A j) := by
  exact inner_padFinVector h (B i) (A j)

theorem linearProbe_padFeatureMatrix {m d D : ℕ} (h : d ≤ D)
    (A B : FeatureMatrix m d) (z : FeatureVector m) (i : Fin m) :
    linearProbe (padFeatureMatrix h A) (padFeatureMatrix h B) z i =
      linearProbe A B z i := by
  classical
  unfold linearProbe
  simp [padFeatureMatrix, inner_padFinVector h]

theorem linearRecoveryCondition_padFeatureMatrix {m d D k : ℕ} {epsilon : ℝ}
    (h : d ≤ D) {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon) :
    linearRecoveryCondition (padFeatureMatrix h A) (padFeatureMatrix h B)
      k epsilon := by
  intro z hz_sparse hz_box i
  simpa [SupErrorLt, linearProbe_padFeatureMatrix h A B z i]
    using hrec z hz_sparse hz_box i

theorem linearCompressedSensingFeasible_mono_dimension
    {m k d D : ℕ} {epsilon : ℝ}
    (h : d ≤ D) (hfeas : linearCompressedSensingFeasible m k d epsilon) :
    linearCompressedSensingFeasible m k D epsilon := by
  rcases hfeas with ⟨A, B, hrec⟩
  exact ⟨padFeatureMatrix h A, padFeatureMatrix h B,
    linearRecoveryCondition_padFeatureMatrix h hrec⟩

/-- Identity construction witnessing feasibility at dimension `m`. -/
abbrev identityFeatureMatrix (m : ℕ) : FeatureMatrix m m :=
  featureIdentityMatrix

theorem linearRecoveryCondition_identityFeatureMatrix
    {m k : ℕ} {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    linearRecoveryCondition (identityFeatureMatrix m) (identityFeatureMatrix m)
      k epsilon := by
  intro z _hz_sparse _hz_box
  exact supErrorLt_featureIdentityMatrix z hepsilon

theorem linearCompressedSensingFeasible_identity
    (m k : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    linearCompressedSensingFeasible m k m epsilon := by
  exact ⟨identityFeatureMatrix m, identityFeatureMatrix m,
    linearRecoveryCondition_identityFeatureMatrix (m := m) (k := k)
      (epsilon := epsilon) hepsilon⟩

theorem exists_linearCompressedSensingDimensionValue
    (m k : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ d : ℕ, linearCompressedSensingDimensionValue m k epsilon d := by
  classical
  have hex : ∃ d : ℕ, linearCompressedSensingFeasible m k d epsilon :=
    ⟨m, linearCompressedSensingFeasible_identity m k hepsilon⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · exact Nat.find_spec hex
  · intro d' hd'
    exact Nat.find_min' hex hd'

/--
The paper's minimum dimension `d(m,k,epsilon)` as a noncomputable function.
For nonpositive `epsilon` this returns `0`; all paper-facing uses provide
`0 < epsilon` and use `linearCompressedSensingDimension_spec`.
-/
noncomputable def linearCompressedSensingDimension
    (m k : ℕ) (epsilon : ℝ) : ℕ :=
  by
    classical
    exact
      if h : 0 < epsilon then
        Nat.find (exists_linearCompressedSensingDimensionValue m k h)
      else
        0

theorem linearCompressedSensingDimension_spec
    (m k : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    linearCompressedSensingDimensionValue m k epsilon
      (linearCompressedSensingDimension m k epsilon) := by
  classical
  dsimp [linearCompressedSensingDimension]
  rw [dif_pos hepsilon]
  exact Nat.find_spec (exists_linearCompressedSensingDimensionValue m k hepsilon)

theorem linearCompressedSensingDimensionValue_unique
    {m k d₁ d₂ : ℕ} {epsilon : ℝ}
    (h₁ : linearCompressedSensingDimensionValue m k epsilon d₁)
    (h₂ : linearCompressedSensingDimensionValue m k epsilon d₂) :
    d₁ = d₂ := by
  have h12 : d₁ ≤ d₂ := h₁.2 d₂ h₂.1
  have h21 : d₂ ≤ d₁ := h₂.2 d₁ h₁.1
  omega

/--
Source condition from Theorem Threshold: each row of `B^T A` crosses its
threshold exactly for `k`-sparse Boolean vectors containing that feature.
-/
def thresholdSeparationCondition {m d : ℕ}
    (A B : FeatureMatrix m d) (threshold : Fin m → ℝ) (k : ℕ) : Prop :=
  ThresholdSeparates A B threshold k

/-- Feasibility predicate for Theorem `thm:threshold` at dimension `d`. -/
def thresholdSeparationFeasible (m k d : ℕ) : Prop :=
  ∃ A B : FeatureMatrix m d, ∃ threshold : Fin m → ℝ,
    thresholdSeparationCondition A B threshold k

/--
The minimum-dimension predicate for the binary threshold model.  This is the
threshold analogue of the paper's `d(m,k,epsilon)` predicate for linear
compressed sensing.
-/
def thresholdSeparationDimensionValue (m k d : ℕ) : Prop :=
  thresholdSeparationFeasible m k d ∧
    ∀ d' : ℕ, thresholdSeparationFeasible m k d' → d ≤ d'

/--
Source condition from Corollary `cor:activation-bias`: a monotone activation
with feature-wise bias separates sparse Boolean vectors according to whether
feature `i` is present.
-/
def activationSeparationCondition {m d : ℕ}
    (A W : FeatureMatrix m d) (bias : Fin m → ℝ) (sigma : ℝ → ℝ)
    (k : ℕ) : Prop :=
  ∀ i : Fin m, ∀ z : FeatureVector m, kSparse k z → inZeroOne z →
    (0 < sigma (recoveredCoordinate A W z i + bias i) ↔ z i = 1)

/-- Feasibility predicate for Corollary `cor:activation-bias` at dimension `d`. -/
def activationSeparationFeasible (m k d : ℕ) : Prop :=
  ∃ A W : FeatureMatrix m d, ∃ bias : Fin m → ℝ, ∃ sigma : ℝ → ℝ,
    Monotone sigma ∧ activationSeparationCondition A W bias sigma k

/--
The minimum-dimension predicate for the activation/bias separator model.
-/
def activationSeparationDimensionValue (m k d : ℕ) : Prop :=
  activationSeparationFeasible m k d ∧
    ∀ d' : ℕ, activationSeparationFeasible m k d' → d ≤ d'

theorem thresholdSeparationCondition_identityFeatureMatrix
    (m k : ℕ) :
    thresholdSeparationCondition
      (identityFeatureMatrix m) (identityFeatureMatrix m)
      (fun _ : Fin m => (1 / 2 : ℝ)) k := by
  intro i z _hz_sparse hz_zeroone
  have hprobe :
      linearProbe (identityFeatureMatrix m) (identityFeatureMatrix m) z i =
        z i := by
    simpa [identityFeatureMatrix] using
      (linearProbe_featureIdentityMatrix (Feature := Fin m) z i)
  rw [hprobe]
  constructor
  · intro hlt
    rcases hz_zeroone i with hz0 | hz1
    · linarith
    · exact hz1
  · intro hz1
    rw [hz1]
    norm_num

theorem thresholdSeparationFeasible_identity (m k : ℕ) :
    thresholdSeparationFeasible m k m := by
  exact
    ⟨identityFeatureMatrix m, identityFeatureMatrix m,
      fun _ : Fin m => (1 / 2 : ℝ),
      thresholdSeparationCondition_identityFeatureMatrix m k⟩

theorem exists_thresholdSeparationDimensionValue (m k : ℕ) :
    ∃ d : ℕ, thresholdSeparationDimensionValue m k d := by
  classical
  have hex : ∃ d : ℕ, thresholdSeparationFeasible m k d :=
    ⟨m, thresholdSeparationFeasible_identity m k⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · exact Nat.find_spec hex
  · intro d' hd'
    exact Nat.find_min' hex hd'

/-- The paper's minimum binary-threshold separation dimension. -/
noncomputable def thresholdSeparationDimension (m k : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_thresholdSeparationDimensionValue m k)

theorem thresholdSeparationDimension_spec (m k : ℕ) :
    thresholdSeparationDimensionValue m k
      (thresholdSeparationDimension m k) := by
  classical
  dsimp [thresholdSeparationDimension]
  exact Nat.find_spec (exists_thresholdSeparationDimensionValue m k)

theorem thresholdSeparationDimensionValue_unique
    {m k d₁ d₂ : ℕ}
    (h₁ : thresholdSeparationDimensionValue m k d₁)
    (h₂ : thresholdSeparationDimensionValue m k d₂) :
    d₁ = d₂ := by
  have h12 : d₁ ≤ d₂ := h₁.2 d₂ h₂.1
  have h21 : d₂ ≤ d₁ := h₂.2 d₁ h₁.1
  omega

theorem activationSeparationCondition_identityFeatureMatrix
    (m k : ℕ) :
    activationSeparationCondition
      (identityFeatureMatrix m) (identityFeatureMatrix m)
      (fun _ : Fin m => -(1 / 2 : ℝ)) (fun x : ℝ => x) k := by
  intro i z _hz_sparse hz_zeroone
  have hprobe :
      recoveredCoordinate (identityFeatureMatrix m) (identityFeatureMatrix m) z i =
        z i := by
    simpa [recoveredCoordinate, identityFeatureMatrix] using
      (linearProbe_featureIdentityMatrix (Feature := Fin m) z i)
  rw [hprobe]
  constructor
  · intro hpos
    rcases hz_zeroone i with hz0 | hz1
    · linarith
    · exact hz1
  · intro hz1
    rw [hz1]
    norm_num

theorem activationSeparationFeasible_identity (m k : ℕ) :
    activationSeparationFeasible m k m := by
  exact
    ⟨identityFeatureMatrix m, identityFeatureMatrix m,
      (fun _ : Fin m => -(1 / 2 : ℝ)), (fun x : ℝ => x),
      monotone_id,
      activationSeparationCondition_identityFeatureMatrix m k⟩

theorem exists_activationSeparationDimensionValue (m k : ℕ) :
    ∃ d : ℕ, activationSeparationDimensionValue m k d := by
  classical
  have hex : ∃ d : ℕ, activationSeparationFeasible m k d :=
    ⟨m, activationSeparationFeasible_identity m k⟩
  refine ⟨Nat.find hex, ?_, ?_⟩
  · exact Nat.find_spec hex
  · intro d' hd'
    exact Nat.find_min' hex hd'

/-- The paper's minimum activation/bias separation dimension. -/
noncomputable def activationSeparationDimension (m k : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_activationSeparationDimensionValue m k)

theorem activationSeparationDimension_spec (m k : ℕ) :
    activationSeparationDimensionValue m k
      (activationSeparationDimension m k) := by
  classical
  dsimp [activationSeparationDimension]
  exact Nat.find_spec (exists_activationSeparationDimensionValue m k)

theorem activationSeparationDimensionValue_unique
    {m k d₁ d₂ : ℕ}
    (h₁ : activationSeparationDimensionValue m k d₁)
    (h₂ : activationSeparationDimensionValue m k d₂) :
    d₁ = d₂ := by
  have h12 : d₁ ≤ d₂ := h₁.2 d₂ h₂.1
  have h21 : d₂ ≤ d₁ := h₂.2 d₁ h₁.1
  omega

/-- Paper row normalization for the threshold proof. -/
noncomputable abbrev diagonalNormalizedProbeMatrix {m d : ℕ}
    (A B : FeatureMatrix m d) : FeatureMatrix m d :=
  diagonalNormalizedProbes A B

/-- Thresholds rescaled together with `diagonalNormalizedProbeMatrix`. -/
noncomputable abbrev diagonalNormalizedThresholds {m d : ℕ}
    (A B : FeatureMatrix m d) (threshold : Fin m → ℝ) : Fin m → ℝ :=
  diagonalNormalizedThreshold A B threshold

/--
Thresholds extracted from a monotone activation-and-bias separator by taking
the largest negative-example preactivation score feature by feature.
-/
noncomputable abbrev activationDerivedThresholds {m d : ℕ}
    (A W : FeatureMatrix m d) (bias : Fin m → ℝ) (k : ℕ) : Fin m → ℝ :=
  activationDerivedThreshold A W bias k

/-- Paper definition: `mu`-incoherence with non-strict off-diagonal bounds. -/
abbrev muIncoherent {m d : ℕ} (A : FeatureMatrix m d) (mu : ℝ) : Prop :=
  MuIncoherentLE A mu

theorem geometry1_diag_abs_sub_one_le
    {m d : ℕ} {C : Fin (m + 2) → ColumnVector d} {lambda mu : ℝ}
    (hlambda : 0 ≤ lambda)
    (hC : muIncoherent C mu) (i : Fin m) :
    |inner (geometry1ProbeMatrix C lambda i)
        (geometry1RepresentationMatrix C lambda i) - 1| ≤
      (2 * lambda + lambda ^ 2) * mu := by
  have hia : |inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m))| ≤ mu :=
    hC.offdiag_abs_le (geometry1FeatureIndex_ne_aStar i)
  have hbi : |inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex i))| ≤ mu :=
    hC.offdiag_abs_le (by
      exact (geometry1FeatureIndex_ne_bStar i).symm)
  have hba : |inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| ≤ mu :=
    hC.offdiag_abs_le (by
      exact (geometry1AStar_ne_bStar m).symm)
  have h1 :
      |lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m))| ≤
        lambda * mu := by
    rw [abs_mul, abs_of_nonneg hlambda]
    exact mul_le_mul_of_nonneg_left hia hlambda
  have h2 :
      |lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex i))| ≤
        lambda * mu := by
    rw [abs_mul, abs_of_nonneg hlambda]
    exact mul_le_mul_of_nonneg_left hbi hlambda
  have h3 :
      |lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| ≤
        lambda ^ 2 * mu := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg lambda)]
    exact mul_le_mul_of_nonneg_left hba (sq_nonneg lambda)
  rw [geometry1_probe_representation_inner_eq]
  rw [hC.self_inner]
  calc
    |1 + lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) +
          lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex i)) +
          lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m)) - 1| =
        |lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) +
          lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex i)) +
          lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| := by
          ring_nf
    _ ≤
        |lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m))| +
          |lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex i))| +
          |lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| := by
          calc
            |lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) +
                lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex i)) +
                lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| ≤
                |lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) +
                  lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex i))| +
                  |lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| := by
                  exact abs_add_le _ _
            _ ≤
                |lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m))| +
                  |lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex i))| +
                  |lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| := by
                  nlinarith [abs_add_le
                    (lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)))
                    (lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex i)))]
    _ ≤ (2 * lambda + lambda ^ 2) * mu := by
          nlinarith

theorem geometry1_offdiag_abs_inner_le
    {m d : ℕ} {C : Fin (m + 2) → ColumnVector d} {lambda mu : ℝ}
    (hlambda : 0 ≤ lambda)
    (hC : muIncoherent C mu) {i j : Fin m} (hij : i ≠ j) :
    |inner (geometry1ProbeMatrix C lambda i)
        (geometry1RepresentationMatrix C lambda j)| ≤
      (1 + 2 * lambda + lambda ^ 2) * mu := by
  have hff :
      |inner (C (geometry1FeatureIndex i)) (C (geometry1FeatureIndex j))| ≤ mu :=
    hC.offdiag_abs_le (by
      intro h
      exact hij (geometry1FeatureIndex_injective h))
  have hia : |inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m))| ≤ mu :=
    hC.offdiag_abs_le (geometry1FeatureIndex_ne_aStar i)
  have hbj : |inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex j))| ≤ mu :=
    hC.offdiag_abs_le (by
      exact (geometry1FeatureIndex_ne_bStar j).symm)
  have hba : |inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| ≤ mu :=
    hC.offdiag_abs_le (by
      exact (geometry1AStar_ne_bStar m).symm)
  have h1 :
      |lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m))| ≤
        lambda * mu := by
    rw [abs_mul, abs_of_nonneg hlambda]
    exact mul_le_mul_of_nonneg_left hia hlambda
  have h2 :
      |lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex j))| ≤
        lambda * mu := by
    rw [abs_mul, abs_of_nonneg hlambda]
    exact mul_le_mul_of_nonneg_left hbj hlambda
  have h3 :
      |lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| ≤
        lambda ^ 2 * mu := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg lambda)]
    exact mul_le_mul_of_nonneg_left hba (sq_nonneg lambda)
  rw [geometry1_probe_representation_inner_eq]
  calc
    |inner (C (geometry1FeatureIndex i)) (C (geometry1FeatureIndex j)) +
        lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) +
        lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex j)) +
        lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| ≤
        |inner (C (geometry1FeatureIndex i)) (C (geometry1FeatureIndex j))| +
          |lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m))| +
          |lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex j))| +
          |lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| := by
          calc
            |inner (C (geometry1FeatureIndex i)) (C (geometry1FeatureIndex j)) +
                lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) +
                lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex j)) +
                lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| ≤
                |inner (C (geometry1FeatureIndex i)) (C (geometry1FeatureIndex j)) +
                  lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) +
                  lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex j))| +
                  |lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| := by
                  exact abs_add_le _ _
            _ ≤
                |inner (C (geometry1FeatureIndex i)) (C (geometry1FeatureIndex j)) +
                  lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m))| +
                  |lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex j))| +
                  |lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| := by
                  nlinarith [abs_add_le
                    (inner (C (geometry1FeatureIndex i)) (C (geometry1FeatureIndex j)) +
                      lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)))
                    (lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex j)))]
            _ ≤
                |inner (C (geometry1FeatureIndex i)) (C (geometry1FeatureIndex j))| +
                  |lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m))| +
                  |lambda * inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex j))| +
                  |lambda ^ 2 * inner (C (geometry1BStarIndex m)) (C (geometry1AStarIndex m))| := by
                  nlinarith [abs_add_le
                    (inner (C (geometry1FeatureIndex i)) (C (geometry1FeatureIndex j)))
                    (lambda * inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)))]
    _ ≤ (1 + 2 * lambda + lambda ^ 2) * mu := by
          nlinarith

theorem geometry1_linearRecoveryCondition
    {m d k : ℕ} {epsilon lambda mu : ℝ}
    {C : Fin (m + 2) → ColumnVector d}
    (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu)
    (hC : muIncoherent C mu)
    (hbound :
      (2 * lambda + lambda ^ 2) * mu +
          (k : ℝ) * ((1 + 2 * lambda + lambda ^ 2) * mu) < epsilon) :
    linearRecoveryCondition
      (geometry1RepresentationMatrix C lambda)
      (geometry1ProbeMatrix C lambda) k epsilon := by
  intro z hz_sparse hz_box
  exact
    supErrorLt_of_diag_abs_sub_one_le_offdiag_abs_le
      (A := geometry1RepresentationMatrix C lambda)
      (B := geometry1ProbeMatrix C lambda)
      (z := z) (k := k)
      (ν := (2 * lambda + lambda ^ 2) * mu)
      (μ := (1 + 2 * lambda + lambda ^ 2) * mu)
      (ε := epsilon)
      (by nlinarith [hlambda, hmu, sq_nonneg lambda])
      (by nlinarith [hlambda, hmu, sq_nonneg lambda])
      (geometry1_diag_abs_sub_one_le hlambda hC)
      (fun {i j} hij =>
        geometry1_offdiag_abs_inner_le
          (C := C) (lambda := lambda) (mu := mu)
          hlambda hC (i := i) (j := j) hij)
      hz_sparse hz_box hbound

theorem geometry1_representation_inner_self_eq
    {m d : ℕ} (C : Fin (m + 2) → ColumnVector d) (lambda : ℝ)
    (hself : ∀ t, inner (C t) (C t) = 1) (i : Fin m) :
    inner (geometry1RepresentationMatrix C lambda i)
        (geometry1RepresentationMatrix C lambda i) =
      1 + 2 * lambda *
        inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) +
        lambda ^ 2 := by
  have h :=
    inner_add_smul_add_smul
      (Coord := Fin d) lambda
      (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m))
      (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m))
  change inner
      (fun r => C (geometry1FeatureIndex i) r + lambda * C (geometry1AStarIndex m) r)
      (fun r => C (geometry1FeatureIndex i) r + lambda * C (geometry1AStarIndex m) r) =
    1 + 2 * lambda *
      inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) +
      lambda ^ 2
  rw [h]
  rw [hself (geometry1FeatureIndex i), hself (geometry1AStarIndex m)]
  have hcomm :
      inner (C (geometry1AStarIndex m)) (C (geometry1FeatureIndex i)) =
        inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) := by
    exact inner_comm _ _
  rw [hcomm]
  ring

theorem geometry1_probe_inner_self_eq
    {m d : ℕ} (C : Fin (m + 2) → ColumnVector d) (lambda : ℝ)
    (hself : ∀ t, inner (C t) (C t) = 1) (i : Fin m) :
    inner (geometry1ProbeMatrix C lambda i)
        (geometry1ProbeMatrix C lambda i) =
      1 + 2 * lambda *
        inner (C (geometry1FeatureIndex i)) (C (geometry1BStarIndex m)) +
        lambda ^ 2 := by
  have h :=
    inner_add_smul_add_smul
      (Coord := Fin d) lambda
      (C (geometry1FeatureIndex i)) (C (geometry1BStarIndex m))
      (C (geometry1FeatureIndex i)) (C (geometry1BStarIndex m))
  change inner
      (fun r => C (geometry1FeatureIndex i) r + lambda * C (geometry1BStarIndex m) r)
      (fun r => C (geometry1FeatureIndex i) r + lambda * C (geometry1BStarIndex m) r) =
    1 + 2 * lambda *
      inner (C (geometry1FeatureIndex i)) (C (geometry1BStarIndex m)) +
      lambda ^ 2
  rw [h]
  rw [hself (geometry1FeatureIndex i), hself (geometry1BStarIndex m)]
  have hcomm :
      inner (C (geometry1BStarIndex m)) (C (geometry1FeatureIndex i)) =
        inner (C (geometry1FeatureIndex i)) (C (geometry1BStarIndex m)) := by
    exact inner_comm _ _
  rw [hcomm]
  ring

theorem geometry1_representation_columnNorm_sq_bounds
    {m d : ℕ} {C : Fin (m + 2) → ColumnVector d} {lambda mu : ℝ}
    (hlambda : 0 ≤ lambda) (hC : muIncoherent C mu) (i : Fin m) :
    1 + lambda ^ 2 - 2 * lambda * mu ≤ columnNorm (geometry1RepresentationMatrix C lambda i) ^ 2 ∧
      columnNorm (geometry1RepresentationMatrix C lambda i) ^ 2 ≤
        1 + lambda ^ 2 + 2 * lambda * mu := by
  have hia : |inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m))| ≤ mu :=
    hC.offdiag_abs_le (geometry1FeatureIndex_ne_aStar i)
  have hlow : -mu ≤ inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) :=
    (abs_le.mp hia).1
  have hhigh : inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) ≤ mu :=
    (abs_le.mp hia).2
  have hself :
      inner (geometry1RepresentationMatrix C lambda i)
          (geometry1RepresentationMatrix C lambda i) =
        1 + 2 * lambda *
          inner (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m)) +
          lambda ^ 2 := by
    exact geometry1_representation_inner_self_eq C lambda hC.self_inner i
  rw [vectorNorm_sq_eq_inner_self]
  rw [hself]
  constructor <;> nlinarith

theorem geometry1_probe_columnNorm_sq_bounds
    {m d : ℕ} {C : Fin (m + 2) → ColumnVector d} {lambda mu : ℝ}
    (hlambda : 0 ≤ lambda) (hC : muIncoherent C mu) (i : Fin m) :
    1 + lambda ^ 2 - 2 * lambda * mu ≤ columnNorm (geometry1ProbeMatrix C lambda i) ^ 2 ∧
      columnNorm (geometry1ProbeMatrix C lambda i) ^ 2 ≤
        1 + lambda ^ 2 + 2 * lambda * mu := by
  have hib : |inner (C (geometry1FeatureIndex i)) (C (geometry1BStarIndex m))| ≤ mu :=
    hC.offdiag_abs_le (geometry1FeatureIndex_ne_bStar i)
  have hlow : -mu ≤ inner (C (geometry1FeatureIndex i)) (C (geometry1BStarIndex m)) :=
    (abs_le.mp hib).1
  have hhigh : inner (C (geometry1FeatureIndex i)) (C (geometry1BStarIndex m)) ≤ mu :=
    (abs_le.mp hib).2
  have hself :
      inner (geometry1ProbeMatrix C lambda i)
          (geometry1ProbeMatrix C lambda i) =
        1 + 2 * lambda *
          inner (C (geometry1FeatureIndex i)) (C (geometry1BStarIndex m)) +
          lambda ^ 2 := by
    exact geometry1_probe_inner_self_eq C lambda hC.self_inner i
  rw [vectorNorm_sq_eq_inner_self]
  rw [hself]
  constructor <;> nlinarith

theorem columnNorm_product_ge_of_sq_lower
    {d : ℕ} {x y : ColumnVector d} {s : ℝ}
    (hs : 0 ≤ s) (hx : s ≤ columnNorm x ^ 2)
    (hy : s ≤ columnNorm y ^ 2) :
    s ≤ columnNorm x * columnNorm y := by
  have hsqrt_sq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  have hxle : Real.sqrt s ≤ columnNorm x := by
    have hsq : Real.sqrt s ^ 2 ≤ columnNorm x ^ 2 := by
      simpa [hsqrt_sq] using hx
    exact (sq_le_sq₀ (Real.sqrt_nonneg s) (by
      simpa [columnNorm] using vectorNorm_nonneg x)).mp hsq
  have hyle : Real.sqrt s ≤ columnNorm y := by
    have hsq : Real.sqrt s ^ 2 ≤ columnNorm y ^ 2 := by
      simpa [hsqrt_sq] using hy
    exact (sq_le_sq₀ (Real.sqrt_nonneg s) (by
      simpa [columnNorm] using vectorNorm_nonneg y)).mp hsq
  have hmul :=
    mul_le_mul hxle hyle (Real.sqrt_nonneg s) (by
      simpa [columnNorm] using vectorNorm_nonneg x)
  have hsqrt_mul : Real.sqrt s * Real.sqrt s = s := by
    simpa [pow_two] using hsqrt_sq
  simpa [hsqrt_mul] using hmul

theorem columnNorm_product_le_of_sq_upper
    {d : ℕ} {x y : ColumnVector d} {R : ℝ}
    (hR : 0 ≤ R) (hx : columnNorm x ^ 2 ≤ R)
    (hy : columnNorm y ^ 2 ≤ R) :
    columnNorm x * columnNorm y ≤ R := by
  have hxle : columnNorm x ≤ Real.sqrt R := by
    exact Real.le_sqrt_of_sq_le hx
  have hyle : columnNorm y ≤ Real.sqrt R := by
    exact Real.le_sqrt_of_sq_le hy
  have hmul :=
    mul_le_mul hxle hyle (by
      simpa [columnNorm] using vectorNorm_nonneg y) (by
      exact Real.sqrt_nonneg R)
  have hsqrt_mul : Real.sqrt R * Real.sqrt R = R := by
    simpa [pow_two] using Real.sq_sqrt hR
  simpa [hsqrt_mul] using hmul

theorem geometry1_self_inner_abs_le
    {m d : ℕ} {C : Fin (m + 2) → ColumnVector d} {lambda mu : ℝ}
    (hlambda : 0 ≤ lambda)
    (hC : muIncoherent C mu) (i : Fin m) :
    |inner (geometry1RepresentationMatrix C lambda i)
        (geometry1ProbeMatrix C lambda i)| ≤
      1 + (2 * lambda + lambda ^ 2) * mu := by
  have hdiag :=
    geometry1_diag_abs_sub_one_le
      (C := C) (lambda := lambda) (mu := mu) hlambda hC i
  have hcomm :
      inner (geometry1RepresentationMatrix C lambda i)
          (geometry1ProbeMatrix C lambda i) =
        inner (geometry1ProbeMatrix C lambda i)
          (geometry1RepresentationMatrix C lambda i) := by
    exact inner_comm _ _
  rw [hcomm]
  calc
    |inner (geometry1ProbeMatrix C lambda i)
        (geometry1RepresentationMatrix C lambda i)| =
        |(inner (geometry1ProbeMatrix C lambda i)
          (geometry1RepresentationMatrix C lambda i) - 1) + 1| := by
          ring_nf
    _ ≤
        |inner (geometry1ProbeMatrix C lambda i)
          (geometry1RepresentationMatrix C lambda i) - 1| + |(1 : ℝ)| := by
          exact abs_add_le _ _
    _ ≤ 1 + (2 * lambda + lambda ^ 2) * mu := by
          norm_num
          nlinarith [hdiag]

theorem geometry1_self_columnCorrelation_abs_le
    {m d : ℕ} {C : Fin (m + 2) → ColumnVector d} {lambda mu : ℝ}
    (hlambda : 0 ≤ lambda) (hC : muIncoherent C mu)
    (hs : 0 < 1 + lambda ^ 2 - 2 * lambda * mu) (i : Fin m) :
    |columnCorrelation (geometry1RepresentationMatrix C lambda i)
        (geometry1ProbeMatrix C lambda i)| ≤
      (1 + (2 * lambda + lambda ^ 2) * mu) /
        (1 + lambda ^ 2 - 2 * lambda * mu) := by
  let s : ℝ := 1 + lambda ^ 2 - 2 * lambda * mu
  have hs_pos : 0 < s := by simpa [s] using hs
  have hs_nonneg : 0 ≤ s := le_of_lt hs_pos
  have hAnorm_sq :=
    (geometry1_representation_columnNorm_sq_bounds
      (C := C) (lambda := lambda) (mu := mu) hlambda hC i).1
  have hBnorm_sq :=
    (geometry1_probe_columnNorm_sq_bounds
      (C := C) (lambda := lambda) (mu := mu) hlambda hC i).1
  have hdenom :
      s ≤ columnNorm (geometry1RepresentationMatrix C lambda i) *
        columnNorm (geometry1ProbeMatrix C lambda i) :=
    columnNorm_product_ge_of_sq_lower hs_nonneg
      (by simpa [s] using hAnorm_sq)
      (by simpa [s] using hBnorm_sq)
  have hApos : 0 < columnNorm (geometry1RepresentationMatrix C lambda i) := by
    have hsq_pos :
        0 < columnNorm (geometry1RepresentationMatrix C lambda i) ^ 2 :=
      lt_of_lt_of_le hs_pos (by simpa [s] using hAnorm_sq)
    have hne : columnNorm (geometry1RepresentationMatrix C lambda i) ≠ 0 := by
      intro hzero
      rw [hzero] at hsq_pos
      norm_num at hsq_pos
    exact lt_of_le_of_ne (by
      simpa [columnNorm] using
        vectorNorm_nonneg (geometry1RepresentationMatrix C lambda i)) hne.symm
  have hBpos : 0 < columnNorm (geometry1ProbeMatrix C lambda i) := by
    have hsq_pos :
        0 < columnNorm (geometry1ProbeMatrix C lambda i) ^ 2 :=
      lt_of_lt_of_le hs_pos (by simpa [s] using hBnorm_sq)
    have hne : columnNorm (geometry1ProbeMatrix C lambda i) ≠ 0 := by
      intro hzero
      rw [hzero] at hsq_pos
      norm_num at hsq_pos
    exact lt_of_le_of_ne (by
      simpa [columnNorm] using
        vectorNorm_nonneg (geometry1ProbeMatrix C lambda i)) hne.symm
  have hinner :=
    geometry1_self_inner_abs_le
      (C := C) (lambda := lambda) (mu := mu) hlambda hC i
  exact
    abs_vectorCorrelation_le_of_abs_inner_le_of_norm_product_ge
      (x := geometry1RepresentationMatrix C lambda i)
      (y := geometry1ProbeMatrix C lambda i)
      (N := 1 + (2 * lambda + lambda ^ 2) * mu) (D := s)
      hApos hBpos hinner hdenom hs_pos

theorem geometry1_representation_offdiag_inner_lower
    {m d : ℕ} {C : Fin (m + 2) → ColumnVector d} {lambda mu : ℝ}
    (hlambda : 0 ≤ lambda) (hC : muIncoherent C mu)
    {i j : Fin m} (hij : i ≠ j) :
    lambda ^ 2 - (1 + 2 * lambda) * mu ≤
      inner (geometry1RepresentationMatrix C lambda i)
        (geometry1RepresentationMatrix C lambda j) := by
  have hff :=
    hC.offdiag_abs_le (by
      intro h
      exact hij (geometry1FeatureIndex_injective h))
      (i := geometry1FeatureIndex i) (j := geometry1FeatureIndex j)
  have hia :=
    hC.offdiag_abs_le (geometry1FeatureIndex_ne_aStar i)
      (i := geometry1FeatureIndex i) (j := geometry1AStarIndex m)
  have haj :=
    hC.offdiag_abs_le (by exact (geometry1FeatureIndex_ne_aStar j).symm)
      (i := geometry1AStarIndex m) (j := geometry1FeatureIndex j)
  have hff_low := (abs_le.mp hff).1
  have hia_low := (abs_le.mp hia).1
  have haj_low := (abs_le.mp haj).1
  have h :=
    inner_add_smul_add_smul
      (Coord := Fin d) lambda
      (C (geometry1FeatureIndex i)) (C (geometry1AStarIndex m))
      (C (geometry1FeatureIndex j)) (C (geometry1AStarIndex m))
  change inner
      (fun r => C (geometry1FeatureIndex i) r + lambda * C (geometry1AStarIndex m) r)
      (fun r => C (geometry1FeatureIndex j) r + lambda * C (geometry1AStarIndex m) r) ≥
    lambda ^ 2 - (1 + 2 * lambda) * mu
  rw [h]
  rw [hC.self_inner (geometry1AStarIndex m)]
  nlinarith

theorem geometry1_probe_offdiag_inner_lower
    {m d : ℕ} {C : Fin (m + 2) → ColumnVector d} {lambda mu : ℝ}
    (hlambda : 0 ≤ lambda) (hC : muIncoherent C mu)
    {i j : Fin m} (hij : i ≠ j) :
    lambda ^ 2 - (1 + 2 * lambda) * mu ≤
      inner (geometry1ProbeMatrix C lambda i)
        (geometry1ProbeMatrix C lambda j) := by
  have hff :=
    hC.offdiag_abs_le (by
      intro h
      exact hij (geometry1FeatureIndex_injective h))
      (i := geometry1FeatureIndex i) (j := geometry1FeatureIndex j)
  have hib :=
    hC.offdiag_abs_le (geometry1FeatureIndex_ne_bStar i)
      (i := geometry1FeatureIndex i) (j := geometry1BStarIndex m)
  have hbj :=
    hC.offdiag_abs_le (by exact (geometry1FeatureIndex_ne_bStar j).symm)
      (i := geometry1BStarIndex m) (j := geometry1FeatureIndex j)
  have hff_low := (abs_le.mp hff).1
  have hib_low := (abs_le.mp hib).1
  have hbj_low := (abs_le.mp hbj).1
  have h :=
    inner_add_smul_add_smul
      (Coord := Fin d) lambda
      (C (geometry1FeatureIndex i)) (C (geometry1BStarIndex m))
      (C (geometry1FeatureIndex j)) (C (geometry1BStarIndex m))
  change inner
      (fun r => C (geometry1FeatureIndex i) r + lambda * C (geometry1BStarIndex m) r)
      (fun r => C (geometry1FeatureIndex j) r + lambda * C (geometry1BStarIndex m) r) ≥
    lambda ^ 2 - (1 + 2 * lambda) * mu
  rw [h]
  rw [hC.self_inner (geometry1BStarIndex m)]
  nlinarith

theorem geometry1_representation_columnCorrelation_lower
    {m d : ℕ} {C : Fin (m + 2) → ColumnVector d} {lambda mu : ℝ}
    (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu) (hC : muIncoherent C mu)
    (hs : 0 < 1 + lambda ^ 2 - 2 * lambda * mu)
    (hnum : 0 ≤ lambda ^ 2 - (1 + 2 * lambda) * mu)
    {i j : Fin m} (hij : i ≠ j) :
    (lambda ^ 2 - (1 + 2 * lambda) * mu) /
        (1 + lambda ^ 2 + 2 * lambda * mu) ≤
      columnCorrelation (geometry1RepresentationMatrix C lambda i)
        (geometry1RepresentationMatrix C lambda j) := by
  let s : ℝ := 1 + lambda ^ 2 - 2 * lambda * mu
  let R : ℝ := 1 + lambda ^ 2 + 2 * lambda * mu
  have hs_pos : 0 < s := by simpa [s] using hs
  have hR_pos : 0 < R := by
    have hle : s ≤ R := by
      dsimp [s, R]
      nlinarith [hlambda, hmu]
    exact lt_of_lt_of_le hs_pos hle
  have hR_nonneg : 0 ≤ R := le_of_lt hR_pos
  have hAi_bounds :=
    geometry1_representation_columnNorm_sq_bounds
      (C := C) (lambda := lambda) (mu := mu) hlambda hC i
  have hAj_bounds :=
    geometry1_representation_columnNorm_sq_bounds
      (C := C) (lambda := lambda) (mu := mu) hlambda hC j
  have hprod_upper :
      columnNorm (geometry1RepresentationMatrix C lambda i) *
          columnNorm (geometry1RepresentationMatrix C lambda j) ≤ R :=
    columnNorm_product_le_of_sq_upper hR_nonneg
      (by simpa [R] using hAi_bounds.2)
      (by simpa [R] using hAj_bounds.2)
  have hAipos : 0 < columnNorm (geometry1RepresentationMatrix C lambda i) := by
    have hsq_pos :
        0 < columnNorm (geometry1RepresentationMatrix C lambda i) ^ 2 :=
      lt_of_lt_of_le hs_pos (by simpa [s] using hAi_bounds.1)
    have hne : columnNorm (geometry1RepresentationMatrix C lambda i) ≠ 0 := by
      intro hzero
      rw [hzero] at hsq_pos
      norm_num at hsq_pos
    exact lt_of_le_of_ne (by
      simpa [columnNorm] using
        vectorNorm_nonneg (geometry1RepresentationMatrix C lambda i)) hne.symm
  have hAjpos : 0 < columnNorm (geometry1RepresentationMatrix C lambda j) := by
    have hsq_pos :
        0 < columnNorm (geometry1RepresentationMatrix C lambda j) ^ 2 :=
      lt_of_lt_of_le hs_pos (by simpa [s] using hAj_bounds.1)
    have hne : columnNorm (geometry1RepresentationMatrix C lambda j) ≠ 0 := by
      intro hzero
      rw [hzero] at hsq_pos
      norm_num at hsq_pos
    exact lt_of_le_of_ne (by
      simpa [columnNorm] using
        vectorNorm_nonneg (geometry1RepresentationMatrix C lambda j)) hne.symm
  have hinner :=
    geometry1_representation_offdiag_inner_lower
      (C := C) (lambda := lambda) (mu := mu) hlambda hC hij
  exact
    vectorCorrelation_ge_of_inner_ge_of_norm_product_le
      (x := geometry1RepresentationMatrix C lambda i)
      (y := geometry1RepresentationMatrix C lambda j)
      (N := lambda ^ 2 - (1 + 2 * lambda) * mu) (D := R)
      hAipos hAjpos hinner hnum hprod_upper

theorem geometry1_probe_columnCorrelation_lower
    {m d : ℕ} {C : Fin (m + 2) → ColumnVector d} {lambda mu : ℝ}
    (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu) (hC : muIncoherent C mu)
    (hs : 0 < 1 + lambda ^ 2 - 2 * lambda * mu)
    (hnum : 0 ≤ lambda ^ 2 - (1 + 2 * lambda) * mu)
    {i j : Fin m} (hij : i ≠ j) :
    (lambda ^ 2 - (1 + 2 * lambda) * mu) /
        (1 + lambda ^ 2 + 2 * lambda * mu) ≤
      columnCorrelation (geometry1ProbeMatrix C lambda i)
        (geometry1ProbeMatrix C lambda j) := by
  let s : ℝ := 1 + lambda ^ 2 - 2 * lambda * mu
  let R : ℝ := 1 + lambda ^ 2 + 2 * lambda * mu
  have hs_pos : 0 < s := by simpa [s] using hs
  have hR_pos : 0 < R := by
    have hle : s ≤ R := by
      dsimp [s, R]
      nlinarith [hlambda, hmu]
    exact lt_of_lt_of_le hs_pos hle
  have hR_nonneg : 0 ≤ R := le_of_lt hR_pos
  have hBi_bounds :=
    geometry1_probe_columnNorm_sq_bounds
      (C := C) (lambda := lambda) (mu := mu) hlambda hC i
  have hBj_bounds :=
    geometry1_probe_columnNorm_sq_bounds
      (C := C) (lambda := lambda) (mu := mu) hlambda hC j
  have hprod_upper :
      columnNorm (geometry1ProbeMatrix C lambda i) *
          columnNorm (geometry1ProbeMatrix C lambda j) ≤ R :=
    columnNorm_product_le_of_sq_upper hR_nonneg
      (by simpa [R] using hBi_bounds.2)
      (by simpa [R] using hBj_bounds.2)
  have hBipos : 0 < columnNorm (geometry1ProbeMatrix C lambda i) := by
    have hsq_pos :
        0 < columnNorm (geometry1ProbeMatrix C lambda i) ^ 2 :=
      lt_of_lt_of_le hs_pos (by simpa [s] using hBi_bounds.1)
    have hne : columnNorm (geometry1ProbeMatrix C lambda i) ≠ 0 := by
      intro hzero
      rw [hzero] at hsq_pos
      norm_num at hsq_pos
    exact lt_of_le_of_ne (by
      simpa [columnNorm] using
        vectorNorm_nonneg (geometry1ProbeMatrix C lambda i)) hne.symm
  have hBjpos : 0 < columnNorm (geometry1ProbeMatrix C lambda j) := by
    have hsq_pos :
        0 < columnNorm (geometry1ProbeMatrix C lambda j) ^ 2 :=
      lt_of_lt_of_le hs_pos (by simpa [s] using hBj_bounds.1)
    have hne : columnNorm (geometry1ProbeMatrix C lambda j) ≠ 0 := by
      intro hzero
      rw [hzero] at hsq_pos
      norm_num at hsq_pos
    exact lt_of_le_of_ne (by
      simpa [columnNorm] using
        vectorNorm_nonneg (geometry1ProbeMatrix C lambda j)) hne.symm
  have hinner :=
    geometry1_probe_offdiag_inner_lower
      (C := C) (lambda := lambda) (mu := mu) hlambda hC hij
  exact
    vectorCorrelation_ge_of_inner_ge_of_norm_product_le
      (x := geometry1ProbeMatrix C lambda i)
      (y := geometry1ProbeMatrix C lambda j)
      (N := lambda ^ 2 - (1 + 2 * lambda) * mu) (D := R)
      hBipos hBjpos hinner hnum hprod_upper

/--
Finite upper envelope for same-feature representation/probe correlations in
Geometry Proposition 1.
-/
noncomputable def geometry1SelfCorrelationEnvelope (lambda mu : ℝ) : ℝ :=
  (1 + (2 * lambda + lambda ^ 2) * mu) /
    (1 + lambda ^ 2 - 2 * lambda * mu)

/--
Finite lower envelope for different-feature representation/representation and
probe/probe correlations in Geometry Proposition 1.
-/
noncomputable def geometry1OffdiagCorrelationEnvelope (lambda mu : ℝ) : ℝ :=
  (lambda ^ 2 - (1 + 2 * lambda) * mu) /
    (1 + lambda ^ 2 + 2 * lambda * mu)

/-- The Geometry Proposition 1 source choice `lambda = sqrt(1 / delta - 1)`. -/
noncomputable def geometry1SourceLambda (delta : ℝ) : ℝ :=
  Real.sqrt (1 / delta - 1)

/--
A conservative source-parameter choice for Geometry Proposition 1.

The additional positive factors relative to the paper's displayed `mu` make
all finite recovery and normalized-correlation side conditions simultaneous;
for fixed `epsilon, delta` this remains a constant multiple of `1 / (k + 1)`.
-/
noncomputable def geometry1SourceMu (epsilon delta : ℝ) (k : ℕ) : ℝ :=
  epsilon * geometry1SourceLambda delta ^ 2 /
    (4 * ((k + 1 : ℕ) : ℝ) * (1 + geometry1SourceLambda delta) ^ 2 *
      (1 + geometry1SourceLambda delta ^ 2) *
      (1 + 2 * geometry1SourceLambda delta))

/-- Explicit `epsilon, delta` coefficient in the Geometry Proposition 1 row bound. -/
noncomputable def geometry1SourceDimensionCoefficient (epsilon delta : ℝ) : ℝ :=
  2 *
    (4 * (1 + geometry1SourceLambda delta) ^ 2 *
      (1 + geometry1SourceLambda delta ^ 2) *
      (1 + 2 * geometry1SourceLambda delta) /
      (epsilon * geometry1SourceLambda delta ^ 2)) ^ 2

theorem geometry1SourceLambda_pos {delta : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    0 < geometry1SourceLambda delta := by
  unfold geometry1SourceLambda
  apply Real.sqrt_pos.2
  apply sub_pos.mpr
  exact (lt_div_iff₀ hdelta_pos).mpr (by linarith)

theorem geometry1SourceLambda_sq {delta : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    geometry1SourceLambda delta ^ 2 = 1 / delta - 1 := by
  unfold geometry1SourceLambda
  rw [Real.sq_sqrt]
  exact le_of_lt (sub_pos.mpr
    ((lt_div_iff₀ hdelta_pos).mpr (by linarith)))

theorem geometry1SourceLambda_self_limit_eq_delta {delta : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    1 / (1 + geometry1SourceLambda delta ^ 2) = delta := by
  rw [geometry1SourceLambda_sq hdelta_pos hdelta_lt_one]
  field_simp [ne_of_gt hdelta_pos]
  ring

theorem geometry1SourceLambda_offdiag_limit_eq_one_sub_delta {delta : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    geometry1SourceLambda delta ^ 2 /
        (1 + geometry1SourceLambda delta ^ 2) = 1 - delta := by
  rw [geometry1SourceLambda_sq hdelta_pos hdelta_lt_one]
  field_simp [ne_of_gt hdelta_pos]
  ring

theorem geometry1SourceMu_pos {epsilon delta : ℝ} {k : ℕ}
    (hepsilon_pos : 0 < epsilon)
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    0 < geometry1SourceMu epsilon delta k := by
  have hlambda_pos := geometry1SourceLambda_pos hdelta_pos hdelta_lt_one
  unfold geometry1SourceMu
  positivity

theorem geometry1SourceMu_dimension_coefficient
    {epsilon delta : ℝ} {k : ℕ}
    (hepsilon_pos : 0 < epsilon)
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    2 / geometry1SourceMu epsilon delta k ^ 2 =
      geometry1SourceDimensionCoefficient epsilon delta *
        ((k + 1 : ℕ) : ℝ) ^ 2 := by
  let lambda : ℝ := geometry1SourceLambda delta
  have hlambda_pos : 0 < lambda := by
    simpa [lambda] using geometry1SourceLambda_pos hdelta_pos hdelta_lt_one
  have hepsilon_lambda_sq_pos : 0 < epsilon * lambda ^ 2 := by positivity
  have hk_pos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  unfold geometry1SourceMu geometry1SourceDimensionCoefficient
  change 2 /
      (epsilon * lambda ^ 2 /
        (4 * ((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2 *
          (1 + lambda ^ 2) * (1 + 2 * lambda))) ^ 2 =
    2 *
      (4 * (1 + lambda) ^ 2 * (1 + lambda ^ 2) * (1 + 2 * lambda) /
        (epsilon * lambda ^ 2)) ^ 2 * ((k + 1 : ℕ) : ℝ) ^ 2
  field_simp [ne_of_gt hepsilon_lambda_sq_pos, ne_of_gt hk_pos]

theorem geometry1SourceMu_eq_const_div_succ
    (epsilon delta : ℝ) (k : ℕ)
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    geometry1SourceMu epsilon delta k =
      (epsilon * geometry1SourceLambda delta ^ 2 /
        (4 * (1 + geometry1SourceLambda delta) ^ 2 *
          (1 + geometry1SourceLambda delta ^ 2) *
          (1 + 2 * geometry1SourceLambda delta))) /
        ((k + 1 : ℕ) : ℝ) := by
  let lambda : ℝ := geometry1SourceLambda delta
  have hlambda_pos : 0 < lambda := by
    simpa [lambda] using geometry1SourceLambda_pos hdelta_pos hdelta_lt_one
  have hk_pos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hbase_pos :
      0 < 4 * (1 + lambda) ^ 2 * (1 + lambda ^ 2) *
        (1 + 2 * lambda) := by
    positivity
  have hfull_pos :
      0 < 4 * ((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2 *
        (1 + lambda ^ 2) * (1 + 2 * lambda) := by
    positivity
  unfold geometry1SourceMu
  change epsilon * lambda ^ 2 /
      (4 * ((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2 *
        (1 + lambda ^ 2) * (1 + 2 * lambda)) =
    (epsilon * lambda ^ 2 /
      (4 * (1 + lambda) ^ 2 * (1 + lambda ^ 2) *
        (1 + 2 * lambda))) /
      ((k + 1 : ℕ) : ℝ)
  field_simp [ne_of_gt hk_pos, ne_of_gt hbase_pos, ne_of_gt hfull_pos]

theorem geometry1SourceMu_tendsToZero (epsilon delta : ℝ)
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    AppliedModelingLib.Math.TendsToZero
      (geometry1SourceMu epsilon delta) := by
  rw [AppliedModelingLib.Math.TendsToZero]
  change Tendsto (fun k : ℕ => geometry1SourceMu epsilon delta k) atTop (nhds 0)
  let C : ℝ :=
    epsilon * geometry1SourceLambda delta ^ 2 /
      (4 * (1 + geometry1SourceLambda delta) ^ 2 *
        (1 + geometry1SourceLambda delta ^ 2) *
        (1 + 2 * geometry1SourceLambda delta))
  have hrewrite :
      (fun k : ℕ => geometry1SourceMu epsilon delta k) =
        fun k : ℕ => C / ((k + 1 : ℕ) : ℝ) := by
    funext k
    simpa [C] using
      geometry1SourceMu_eq_const_div_succ epsilon delta k hdelta_pos hdelta_lt_one
  rw [hrewrite]
  have hinv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hconst : Tendsto (fun _k : ℕ => C) atTop (nhds C) :=
    tendsto_const_nhds
  have hmul : Tendsto (fun k : ℕ => C * (1 / ((k : ℝ) + 1)))
      atTop (nhds (C * 0)) := hconst.mul hinv
  simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one,
    mul_comm, mul_left_comm, mul_assoc] using hmul

/-- The chosen source schedule leaves a factor-four recovery margin. -/
theorem geometry1SourceMu_recovery_budget
    {epsilon delta : ℝ} {k : ℕ}
    (hepsilon_pos : 0 < epsilon)
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    (((k + 1 : ℕ) : ℝ) * (1 + geometry1SourceLambda delta) ^ 2) *
        geometry1SourceMu epsilon delta k ≤ epsilon / 4 := by
  let lambda : ℝ := geometry1SourceLambda delta
  have hlambda_pos : 0 < lambda := by
    simpa [lambda] using geometry1SourceLambda_pos hdelta_pos hdelta_lt_one
  have hden_pos :
      0 < 4 * ((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2 *
        (1 + lambda ^ 2) * (1 + 2 * lambda) := by
    positivity
  have hratio_le : lambda ^ 2 ≤ (1 + lambda ^ 2) * (1 + 2 * lambda) := by
    nlinarith [sq_nonneg lambda]
  dsimp [geometry1SourceMu]
  change (((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2) *
      (epsilon * lambda ^ 2 /
        (4 * ((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2 *
          (1 + lambda ^ 2) * (1 + 2 * lambda))) ≤ epsilon / 4
  field_simp [ne_of_gt hden_pos]
  nlinarith

/-- The chosen source schedule also preserves a positive off-diagonal margin. -/
theorem geometry1SourceMu_cross_term_budget
    {epsilon delta : ℝ} {k : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    (1 + 2 * geometry1SourceLambda delta) *
        geometry1SourceMu epsilon delta k <
      geometry1SourceLambda delta ^ 2 := by
  let lambda : ℝ := geometry1SourceLambda delta
  have hlambda_pos : 0 < lambda := by
    simpa [lambda] using geometry1SourceLambda_pos hdelta_pos hdelta_lt_one
  have hden_pos :
      0 < 4 * ((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2 *
        (1 + lambda ^ 2) * (1 + 2 * lambda) := by
    positivity
  have hright_pos : 0 < lambda ^ 2 := sq_pos_of_pos hlambda_pos
  have hk_one : 1 ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hlambda_add_one : 1 ≤ (1 + lambda) ^ 2 := by
    nlinarith [sq_nonneg lambda]
  have hlambda_sq_add_one : 1 ≤ 1 + lambda ^ 2 := by
    nlinarith [sq_nonneg lambda]
  have hproduct_one :
      1 ≤ ((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2 * (1 + lambda ^ 2) := by
    calc
      1 = 1 * 1 * 1 := by norm_num
      _ ≤ ((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2 * (1 + lambda ^ 2) := by
        gcongr
  have hremaining_gt_epsilon :
      epsilon < 4 * ((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2 *
        (1 + lambda ^ 2) := by
    nlinarith
  dsimp [geometry1SourceMu]
  change (1 + 2 * lambda) *
      (epsilon * lambda ^ 2 /
        (4 * ((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2 *
          (1 + lambda ^ 2) * (1 + 2 * lambda))) < lambda ^ 2
  field_simp [ne_of_gt hden_pos, ne_of_gt hright_pos]
  nlinarith [hremaining_gt_epsilon]

/--
The source parameter schedule simultaneously supplies the finite hypotheses of
the Geometry Proposition 1 construction.
-/
theorem geometry1SourceMu_construction_side_conditions
    {epsilon delta : ℝ} {k : ℕ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    let lambda := geometry1SourceLambda delta
    let mu := geometry1SourceMu epsilon delta k
    (2 * lambda + lambda ^ 2) * mu +
        (k : ℝ) * ((1 + 2 * lambda + lambda ^ 2) * mu) < epsilon ∧
      0 < 1 + lambda ^ 2 - 2 * lambda * mu ∧
      0 ≤ lambda ^ 2 - (1 + 2 * lambda) * mu := by
  dsimp
  let lambda : ℝ := geometry1SourceLambda delta
  let mu : ℝ := geometry1SourceMu epsilon delta k
  have hlambda_pos : 0 < lambda := by
    simpa [lambda] using geometry1SourceLambda_pos hdelta_pos hdelta_lt_one
  have hmu_pos : 0 < mu := by
    simpa [mu] using geometry1SourceMu_pos
      (k := k) hepsilon_pos hdelta_pos hdelta_lt_one
  have hbudget :
      (((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2) * mu ≤ epsilon / 4 := by
    simpa [lambda, mu] using geometry1SourceMu_recovery_budget
      (k := k) hepsilon_pos hdelta_pos hdelta_lt_one
  have hcross : (1 + 2 * lambda) * mu < lambda ^ 2 := by
    simpa [lambda, mu] using geometry1SourceMu_cross_term_budget
      (k := k) hepsilon_pos hepsilon_lt_one hdelta_pos hdelta_lt_one
  have hcoefficient :
      (2 * lambda + lambda ^ 2) +
          (k : ℝ) * (1 + 2 * lambda + lambda ^ 2) ≤
        ((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2 := by
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith [sq_nonneg lambda]
  have hconstruction_le :
      (2 * lambda + lambda ^ 2) * mu +
          (k : ℝ) * ((1 + 2 * lambda + lambda ^ 2) * mu) ≤
        (((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2) * mu := by
    rw [show
      (2 * lambda + lambda ^ 2) * mu +
          (k : ℝ) * ((1 + 2 * lambda + lambda ^ 2) * mu) =
        ((2 * lambda + lambda ^ 2) +
          (k : ℝ) * (1 + 2 * lambda + lambda ^ 2)) * mu by ring]
    exact mul_le_mul_of_nonneg_right hcoefficient hmu_pos.le
  have hfirst :
      (2 * lambda + lambda ^ 2) * mu +
          (k : ℝ) * ((1 + 2 * lambda + lambda ^ 2) * mu) < epsilon := by
    calc
      (2 * lambda + lambda ^ 2) * mu +
          (k : ℝ) * ((1 + 2 * lambda + lambda ^ 2) * mu) ≤
          (((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2) * mu := hconstruction_le
      _ ≤ epsilon / 4 := hbudget
      _ < epsilon := by linarith
  have hk_one : 1 ≤ ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hlambda_add_one : 1 ≤ (1 + lambda) ^ 2 := by
    nlinarith [sq_nonneg lambda]
  have hfactor_one : 1 ≤ ((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2 := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ ((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2 := by gcongr
  have hmu_le_epsilon_four : mu ≤ epsilon / 4 := by
    calc
      mu = 1 * mu := by ring
      _ ≤ (((k + 1 : ℕ) : ℝ) * (1 + lambda) ^ 2) * mu :=
        mul_le_mul_of_nonneg_right hfactor_one hmu_pos.le
      _ ≤ epsilon / 4 := hbudget
  have hmu_lt_one : mu < 1 := by linarith
  have htwo_lambda_le : 2 * lambda ≤ 1 + lambda ^ 2 := by
    nlinarith [sq_nonneg (lambda - 1)]
  have htwo_lambda_mu_le : 2 * lambda * mu ≤ (1 + lambda ^ 2) * mu := by
    exact mul_le_mul_of_nonneg_right htwo_lambda_le hmu_pos.le
  have hbase_pos : 0 < 1 + lambda ^ 2 := by positivity
  have hbase_mu_lt : (1 + lambda ^ 2) * mu < 1 + lambda ^ 2 := by
    simpa using mul_lt_mul_of_pos_left hmu_lt_one hbase_pos
  refine ⟨hfirst, ?_, ?_⟩
  · nlinarith
  · linarith

theorem geometry1SelfCorrelationEnvelope_tendsto_of_mu_tendsToZero
    {lambda : ℝ} {mu : ℕ → ℝ}
    (hmu : AppliedModelingLib.Math.TendsToZero mu) :
    Tendsto (fun n => geometry1SelfCorrelationEnvelope lambda (mu n))
      atTop (nhds (1 / (1 + lambda ^ 2))) := by
  rw [AppliedModelingLib.Math.TendsToZero] at hmu
  have hden_ne : 1 + lambda ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg lambda]
  have hnum :
      Tendsto (fun n => 1 + (2 * lambda + lambda ^ 2) * mu n)
        atTop (nhds (1 + (2 * lambda + lambda ^ 2) * 0)) := by
    exact tendsto_const_nhds.add (hmu.const_mul (2 * lambda + lambda ^ 2))
  have hden :
      Tendsto (fun n => 1 + lambda ^ 2 - 2 * lambda * mu n)
        atTop (nhds (1 + lambda ^ 2 - 2 * lambda * 0)) := by
    exact tendsto_const_nhds.sub (hmu.const_mul (2 * lambda))
  have hdiv := hnum.div hden (by simpa using hden_ne)
  simpa [geometry1SelfCorrelationEnvelope, hden_ne] using hdiv

theorem geometry1OffdiagCorrelationEnvelope_tendsto_of_mu_tendsToZero
    {lambda : ℝ} {mu : ℕ → ℝ}
    (hmu : AppliedModelingLib.Math.TendsToZero mu) :
    Tendsto (fun n => geometry1OffdiagCorrelationEnvelope lambda (mu n))
      atTop (nhds (lambda ^ 2 / (1 + lambda ^ 2))) := by
  rw [AppliedModelingLib.Math.TendsToZero] at hmu
  have hden_ne : 1 + lambda ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg lambda]
  have hnum :
      Tendsto (fun n => lambda ^ 2 - (1 + 2 * lambda) * mu n)
        atTop (nhds (lambda ^ 2 - (1 + 2 * lambda) * 0)) := by
    exact tendsto_const_nhds.sub (hmu.const_mul (1 + 2 * lambda))
  have hden :
      Tendsto (fun n => 1 + lambda ^ 2 + 2 * lambda * mu n)
        atTop (nhds (1 + lambda ^ 2 + 2 * lambda * 0)) := by
    exact tendsto_const_nhds.add (hmu.const_mul (2 * lambda))
  have hdiv := hnum.div hden (by simpa using hden_ne)
  simpa [geometry1OffdiagCorrelationEnvelope, hden_ne] using hdiv

theorem geometry1SelfCorrelationError_tendsToZero_of_mu_tendsToZero
    {lambda : ℝ} {mu : ℕ → ℝ}
    (hmu : AppliedModelingLib.Math.TendsToZero mu) :
    AppliedModelingLib.Math.TendsToZero
      (fun n =>
        geometry1SelfCorrelationEnvelope lambda (mu n) -
          1 / (1 + lambda ^ 2)) := by
  rw [AppliedModelingLib.Math.TendsToZero]
  have h := geometry1SelfCorrelationEnvelope_tendsto_of_mu_tendsToZero
    (lambda := lambda) hmu
  have hc :
      Tendsto (fun _n : ℕ => 1 / (1 + lambda ^ 2))
        atTop (nhds (1 / (1 + lambda ^ 2))) :=
    tendsto_const_nhds
  simpa using h.sub hc

theorem geometry1OffdiagCorrelationError_tendsToZero_of_mu_tendsToZero
    {lambda : ℝ} {mu : ℕ → ℝ}
    (hmu : AppliedModelingLib.Math.TendsToZero mu) :
    AppliedModelingLib.Math.TendsToZero
      (fun n =>
        lambda ^ 2 / (1 + lambda ^ 2) -
          geometry1OffdiagCorrelationEnvelope lambda (mu n)) := by
  rw [AppliedModelingLib.Math.TendsToZero]
  have h := geometry1OffdiagCorrelationEnvelope_tendsto_of_mu_tendsToZero
    (lambda := lambda) hmu
  have hc :
      Tendsto (fun _n : ℕ => lambda ^ 2 / (1 + lambda ^ 2))
        atTop (nhds (lambda ^ 2 / (1 + lambda ^ 2))) :=
    tendsto_const_nhds
  simpa using hc.sub h

/--
With the source parameter schedule, the two Geometry Proposition 1 finite
correlation envelopes converge to the displayed `delta` and `1-delta` limits.
-/
theorem geometry1Source_correlation_errors_tendToZero
    {epsilon delta : ℝ}
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    AppliedModelingLib.Math.TendsToZero
      (fun k =>
        geometry1SelfCorrelationEnvelope
          (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k) - delta) ∧
      AppliedModelingLib.Math.TendsToZero
        (fun k =>
          (1 - delta) - geometry1OffdiagCorrelationEnvelope
            (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k)) := by
  have hmu := geometry1SourceMu_tendsToZero epsilon delta hdelta_pos hdelta_lt_one
  have hself := geometry1SelfCorrelationError_tendsToZero_of_mu_tendsToZero
    (lambda := geometry1SourceLambda delta) hmu
  have hoff := geometry1OffdiagCorrelationError_tendsToZero_of_mu_tendsToZero
    (lambda := geometry1SourceLambda delta) hmu
  rw [geometry1SourceLambda_self_limit_eq_delta hdelta_pos hdelta_lt_one] at hself
  rw [geometry1SourceLambda_offdiag_limit_eq_one_sub_delta hdelta_pos hdelta_lt_one] at hoff
  exact ⟨hself, hoff⟩

/--
Deterministic core of the upper-bound proof: if the columns are `mu`-incoherent
and `k * mu < epsilon`, then taking `B = A` satisfies the paper's linear
recovery condition for all `k`-sparse vectors in `[-1,1]^m`.
-/
theorem incoherent_self_linearRecoveryCondition
    {m d k : ℕ} {epsilon mu : ℝ} {A : FeatureMatrix m d}
    (hmu_nonneg : 0 ≤ mu) (hA : muIncoherent A mu)
    (hbound : (k : ℝ) * mu < epsilon) :
    linearRecoveryCondition A A k epsilon := by
  intro z hz_sparse hz_box
  exact
    supErrorLt_of_muIncoherentLE_self
      (A := A) (z := z) (k := k) (μ := mu) (ε := epsilon)
      hmu_nonneg hA hz_sparse hz_box hbound

/--
Feasibility consequence used by the paper's upper-bound construction once an
incoherent matrix with the desired dimension has been supplied.
-/
theorem linearCompressedSensingFeasible_of_muIncoherent
    {m d k : ℕ} {epsilon mu : ℝ} {A : FeatureMatrix m d}
    (hmu_nonneg : 0 ≤ mu) (hA : muIncoherent A mu)
    (hbound : (k : ℝ) * mu < epsilon) :
    linearCompressedSensingFeasible m k d epsilon := by
  exact ⟨A, A, incoherent_self_linearRecoveryCondition hmu_nonneg hA hbound⟩

/--
Finite random-construction endpoint behind Lemma `prop:incoherent`: if the
explicit union-bound failure probability is below one, a scaled Rademacher
matrix supplies a `mu`-incoherent representation matrix.
-/
theorem rademacher_strict_incoherence_probability_ge_one_sub_union_bound
    {m d : ℕ} (hd : 0 < d) {mu : ℝ} (hmu_nonneg : 0 ≤ mu) :
    AppliedModelingLib.measureProb (rowsMeasure (Fin m) (Fin d))
        (fun ω =>
          ∀ ⦃i j : Fin m⦄, i ≠ j →
            |inner (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i)
              (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω j)| < mu) ≥
      1 - ((offdiagPairFinset (Feature := Fin m)).card : ℝ) *
          fixedPairTailBound (Fin d) mu := by
  have hd' : 0 < Fintype.card (Fin d) := by
    simpa using hd
  exact
    measure_forall_offdiag_abs_inner_scaledMatrix_lt_ge_one_sub_union_bound
      (Feature := Fin m) (Coord := Fin d) hd' hmu_nonneg

/--
Same high-probability Rademacher incoherence endpoint with the fixed-pair tail
simplified to the source form `2 * exp (-(d * mu^2) / 2)`.
-/
theorem rademacher_strict_incoherence_probability_ge_one_sub_source_tail
    {m d : ℕ} (hd : 0 < d) {mu : ℝ} (hmu_nonneg : 0 ≤ mu) :
    AppliedModelingLib.measureProb (rowsMeasure (Fin m) (Fin d))
        (fun ω =>
          ∀ ⦃i j : Fin m⦄, i ≠ j →
            |inner (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i)
              (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω j)| < mu) ≥
      1 - ((offdiagPairFinset (Feature := Fin m)).card : ℝ) *
          (2 * Real.exp (-((d : ℝ) * mu ^ 2) / 2)) := by
  simpa [fixedPairTailBound_eq] using
    rademacher_strict_incoherence_probability_ge_one_sub_union_bound
      (m := m) (d := d) hd hmu_nonneg

/--
High-probability Rademacher incoherence endpoint in the source asymptotic
form: if the row dimension satisfies the logarithmic `delta` tail condition,
then all off-diagonal inner products are below `mu` with probability at least
`1 - delta`.
-/
theorem rademacher_strict_incoherence_probability_ge_one_sub_delta_of_log_div_le
    {m d : ℕ} (hd : 0 < d) {mu delta : ℝ}
    (hmu_nonneg : 0 ≤ mu)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ))
    (hdelta_pos : 0 < delta)
    (hlog :
      Real.log
          ((2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta) ≤
        ((d : ℝ) * mu ^ 2) / 2) :
    AppliedModelingLib.measureProb (rowsMeasure (Fin m) (Fin d))
        (fun ω =>
          ∀ ⦃i j : Fin m⦄, i ≠ j →
            |inner (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i)
              (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω j)| < mu) ≥
      1 - delta := by
  have hd' : 0 < Fintype.card (Fin d) := by
    simpa using hd
  have hlog' :
      Real.log
          ((2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta) ≤
        ((Fintype.card (Fin d) : ℝ) * mu ^ 2) / 2 := by
    simpa [Fintype.card_fin] using hlog
  simpa [Fintype.card_fin] using
    measure_forall_offdiag_abs_inner_scaledMatrix_lt_ge_one_sub_delta_of_log_div_le
      (Feature := Fin m) (Coord := Fin d) hd' hmu_nonneg
      hpair_pos hdelta_pos hlog'

/--
Finite random-construction endpoint behind Lemma `prop:incoherent`: if the
explicit union-bound failure probability is below one, a scaled Rademacher
matrix supplies a `mu`-incoherent representation matrix.
-/
theorem exists_muIncoherent_of_rademacher_union_bound_lt_one
    {m d : ℕ} (hd : 0 < d) {mu : ℝ} (hmu_nonneg : 0 ≤ mu)
    (hbad_lt_one :
      ((offdiagPairFinset (Feature := Fin m)).card : ℝ) *
          fixedPairTailBound (Fin d) mu < 1) :
    ∃ A : FeatureMatrix m d, muIncoherent A mu := by
  have hd' : 0 < Fintype.card (Fin d) := by
    simpa using hd
  exact
    exists_scaledMatrix_muIncoherentLE_of_union_bound_lt_one
      (Feature := Fin m) (Coord := Fin d) hd' hmu_nonneg hbad_lt_one

/--
Same finite random-construction endpoint with the fixed-pair tail simplified to
the source form `2 * exp (-(d * mu^2) / 2)`.
-/
theorem exists_muIncoherent_of_rademacher_source_tail_lt_one
    {m d : ℕ} (hd : 0 < d) {mu : ℝ} (hmu_nonneg : 0 ≤ mu)
    (hbad_lt_one :
      ((offdiagPairFinset (Feature := Fin m)).card : ℝ) *
          (2 * Real.exp (-((d : ℝ) * mu ^ 2) / 2)) < 1) :
    ∃ A : FeatureMatrix m d, muIncoherent A mu := by
  refine exists_muIncoherent_of_rademacher_union_bound_lt_one
    (m := m) (d := d) hd hmu_nonneg ?_
  simpa [fixedPairTailBound_eq] using hbad_lt_one

/--
Coherence-scale basis-pursuit witness from the same finite Rademacher
source-tail bound.  This closes the probabilistic and optimization steps for
the mutual-incoherence route to exact recovery.
-/
theorem exists_basisPursuitExactRecovery_of_rademacher_source_tail_lt_one
    {m d k : ℕ} (hd : 0 < d) {mu : ℝ} (hmu_nonneg : 0 ≤ mu)
    (hbad_lt_one :
      ((offdiagPairFinset (Feature := Fin m)).card : ℝ) *
          (2 * Real.exp (-((d : ℝ) * mu ^ 2) / 2)) < 1)
    (hbound : (k : ℝ) * mu < 1 / 2) :
    ∃ A : FeatureMatrix m d, basisPursuitExactRecovery A k := by
  rcases exists_muIncoherent_of_rademacher_source_tail_lt_one
    (m := m) (d := d) hd hmu_nonneg hbad_lt_one with ⟨A, hA⟩
  exact ⟨A, basisPursuitExactRecovery_of_muIncoherent hmu_nonneg hA hbound⟩

/--
Upper-bound finite witness: the scaled-Rademacher construction plus the
deterministic incoherence recovery bound gives linear compressed-sensing
feasibility.
-/
theorem linearCompressedSensingFeasible_of_rademacher_union_bound_lt_one
    {m d k : ℕ} {epsilon mu : ℝ}
    (hd : 0 < d) (hmu_nonneg : 0 ≤ mu)
    (hbad_lt_one :
      ((offdiagPairFinset (Feature := Fin m)).card : ℝ) *
          fixedPairTailBound (Fin d) mu < 1)
    (hbound : (k : ℝ) * mu < epsilon) :
    linearCompressedSensingFeasible m k d epsilon := by
  rcases exists_muIncoherent_of_rademacher_union_bound_lt_one
    (m := m) (d := d) hd hmu_nonneg hbad_lt_one with ⟨A, hA⟩
  exact linearCompressedSensingFeasible_of_muIncoherent hmu_nonneg hA hbound

/-- Source-tail version of the finite upper-bound witness. -/
theorem linearCompressedSensingFeasible_of_rademacher_source_tail_lt_one
    {m d k : ℕ} {epsilon mu : ℝ}
    (hd : 0 < d) (hmu_nonneg : 0 ≤ mu)
    (hbad_lt_one :
      ((offdiagPairFinset (Feature := Fin m)).card : ℝ) *
          (2 * Real.exp (-((d : ℝ) * mu ^ 2) / 2)) < 1)
    (hbound : (k : ℝ) * mu < epsilon) :
    linearCompressedSensingFeasible m k d epsilon := by
  rcases exists_muIncoherent_of_rademacher_source_tail_lt_one
    (m := m) (d := d) hd hmu_nonneg hbad_lt_one with ⟨A, hA⟩
  exact linearCompressedSensingFeasible_of_muIncoherent hmu_nonneg hA hbound

/--
Logarithmic finite upper-bound witness: the source-tail Rademacher bound is
below one whenever the number of rows beats the log ordered-pair threshold.
-/
theorem linearCompressedSensingFeasible_of_rademacher_log_tail
    {m d k : ℕ} {epsilon mu : ℝ}
    (hd : 0 < d) (hmu_nonneg : 0 ≤ mu)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ))
    (hlog :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) <
        ((Fintype.card (Fin d) : ℝ) * mu ^ 2) / 2)
    (hbound : (k : ℝ) * mu < epsilon) :
    linearCompressedSensingFeasible m k d epsilon := by
  have hbad_lt_one :
      ((offdiagPairFinset (Feature := Fin m)).card : ℝ) *
          (2 * Real.exp (-((d : ℝ) * mu ^ 2) / 2)) < 1 := by
    have htail :=
      pair_count_mul_fixedPairTailBound_lt_one_of_log_lt
        (Coord := Fin d)
        (pairCount := ((offdiagPairFinset (Feature := Fin m)).card : ℝ))
        (μ := mu) hpair_pos hlog
    simpa [fixedPairTailBound_eq] using htail
  exact
    linearCompressedSensingFeasible_of_rademacher_source_tail_lt_one
      (m := m) (d := d) (k := k) (epsilon := epsilon) (mu := mu)
      hd hmu_nonneg hbad_lt_one hbound

/--
Source-specialized logarithmic finite upper-bound witness with
`mu = epsilon / (2k)`.
-/
theorem linearCompressedSensingFeasible_of_rademacher_log_tail_epsilon_over_two_k
    {m d k : ℕ} {epsilon : ℝ}
    (hd : 0 < d) (hk : 0 < k) (hepsilon : 0 < epsilon)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ))
    (hlog :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) <
        ((Fintype.card (Fin d) : ℝ) * (epsilon / (2 * (k : ℝ))) ^ 2) / 2) :
    linearCompressedSensingFeasible m k d epsilon := by
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hden_pos : 0 < 2 * (k : ℝ) := by positivity
  have hmu_nonneg : 0 ≤ epsilon / (2 * (k : ℝ)) :=
    div_nonneg hepsilon.le hden_pos.le
  have hbound : (k : ℝ) * (epsilon / (2 * (k : ℝ))) < epsilon := by
    field_simp [ne_of_gt hk_real_pos]
    linarith
  exact
    linearCompressedSensingFeasible_of_rademacher_log_tail
      (m := m) (d := d) (k := k) (epsilon := epsilon)
      (mu := epsilon / (2 * (k : ℝ)))
      hd hmu_nonneg hpair_pos hlog hbound

/--
Existential finite upper-bound endpoint: for the source choice
`mu = epsilon / (2k)`, some finite row dimension satisfies the logarithmic
Rademacher tail condition and hence gives a recovery witness.
-/
theorem exists_linearCompressedSensingFeasible_of_rademacher_log_tail_epsilon_over_two_k
    {m k : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hepsilon : 0 < epsilon)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) :
    ∃ d : ℕ, linearCompressedSensingFeasible m k d epsilon := by
  let pairCount : ℝ := ((offdiagPairFinset (Feature := Fin m)).card : ℝ)
  let mu : ℝ := epsilon / (2 * (k : ℝ))
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hden_pos : 0 < 2 * (k : ℝ) := by positivity
  have hmu_pos : 0 < mu := by
    dsimp [mu]
    exact div_pos hepsilon hden_pos
  have ha_pos : 0 < mu ^ 2 / 2 := by positivity
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (Real.log (2 * pairCount) / (mu ^ 2 / 2))
  let d : ℕ := N + 1
  have hd : 0 < d := by simp [d]
  have hN_to_d : (N : ℝ) < (d : ℝ) := by
    simp [d]
  have hthreshold_lt_d :
      Real.log (2 * pairCount) / (mu ^ 2 / 2) < (d : ℝ) :=
    lt_trans hN hN_to_d
  have hlog_mu :
      Real.log (2 * pairCount) < (d : ℝ) * (mu ^ 2 / 2) :=
    (div_lt_iff₀ ha_pos).mp hthreshold_lt_d
  have hlog :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) <
        ((Fintype.card (Fin d) : ℝ) *
          (epsilon / (2 * (k : ℝ))) ^ 2) / 2 := by
    simpa [pairCount, mu, mul_div_assoc, Fintype.card_fin] using hlog_mu
  exact ⟨d,
    linearCompressedSensingFeasible_of_rademacher_log_tail_epsilon_over_two_k
      (m := m) (d := d) (k := k) (epsilon := epsilon)
      hd hk hepsilon hpair_pos hlog⟩

theorem real_lt_natCeil_add_one (x : ℝ) :
    x < ((Nat.ceil x + 1 : ℕ) : ℝ) := by
  exact lt_of_le_of_lt (Nat.le_ceil x) (by norm_num)

/--
Concrete dimension at which the Rademacher construction produces a
`mu`-incoherent family of `m` columns.
-/
noncomputable def rademacherIncoherentDimension
    (m : ℕ) (mu : ℝ) : ℕ :=
  Nat.ceil
      (Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) /
        ((mu ^ 2) / 2)) + 1

/--
Concrete Rademacher dimension for a prescribed confidence budget `delta`.

The ceiling is taken over the exact ordered-pair union-bound threshold.  Thus
the later source-facing theorem gives an actual dimension choice rather than
leaving the logarithmic condition as an additional premise.
-/
noncomputable def rademacherIncoherentDimensionAtConfidence
    (m : ℕ) (mu delta : ℝ) : ℕ :=
  Nat.ceil
      (Real.log
          ((2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta) /
        ((mu ^ 2) / 2)) + 1

/--
Concrete source-style dimension used by the Rademacher upper-bound proof with
`mu = epsilon / (2k)`.  This is the ceiling of the exact logarithmic tail
threshold plus one, so it directly satisfies the strict finite tail inequality.
-/
noncomputable def rademacherUpperDimension
    (m k : ℕ) (epsilon : ℝ) : ℕ :=
  Nat.ceil
      (Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) /
        (((epsilon / (2 * (k : ℝ))) ^ 2) / 2)) + 1

theorem offdiagPairFinset_fin_card_pos_of_two_le {m : ℕ} (hm : 2 ≤ m) :
    0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ) := by
  classical
  have hmem :
      ((⟨0, by omega⟩ : Fin m), (⟨1, by omega⟩ : Fin m)) ∈
        offdiagPairFinset (Feature := Fin m) := by
    rw [mem_offdiagPairFinset]
    intro h
    have hval : (0 : ℕ) = 1 := by
      exact congrArg Fin.val h
    omega
  have hcard_pos :
      0 < (offdiagPairFinset (Feature := Fin m)).card :=
    Finset.card_pos.mpr
      ⟨((⟨0, by omega⟩ : Fin m), (⟨1, by omega⟩ : Fin m)), hmem⟩
  exact_mod_cast hcard_pos

theorem one_le_offdiagPairFinset_fin_card_of_two_le {m : ℕ} (hm : 2 ≤ m) :
    1 ≤ ((offdiagPairFinset (Feature := Fin m)).card : ℝ) := by
  have hpos_nat : 0 < (offdiagPairFinset (Feature := Fin m)).card := by
    exact_mod_cast offdiagPairFinset_fin_card_pos_of_two_le hm
  exact_mod_cast Nat.succ_le_of_lt hpos_nat

theorem offdiagPairFinset_fin_card_le_sq (m : ℕ) :
    ((offdiagPairFinset (Feature := Fin m)).card : ℝ) ≤ (m : ℝ) ^ 2 := by
  classical
  have hcard :
      (offdiagPairFinset (Feature := Fin m)).card ≤
        (((Finset.univ : Finset (Fin m)).product
          (Finset.univ : Finset (Fin m))).card) := by
    simpa [offdiagPairFinset] using
      (Finset.card_filter_le
        (s := (Finset.univ : Finset (Fin m)).product
          (Finset.univ : Finset (Fin m)))
        (p := fun p : Fin m × Fin m => p.1 ≠ p.2))
  have hprod :
      (((Finset.univ : Finset (Fin m)).product
        (Finset.univ : Finset (Fin m))).card) = m * m := by
    simp
  have hcard' :
      (offdiagPairFinset (Feature := Fin m)).card ≤ m * m := by
    simpa [hprod] using hcard
  have hreal :
      ((offdiagPairFinset (Feature := Fin m)).card : ℝ) ≤
        ((m * m : ℕ) : ℝ) := by
    exact_mod_cast hcard'
  simpa [pow_two] using hreal

theorem rademacherUpperDimension_cast_le_log_tail_add_two
    {m k : ℕ} {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    (rademacherUpperDimension m k epsilon : ℝ) ≤
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) /
          (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) + 2 := by
  let x : ℝ :=
    Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) /
      (((epsilon / (2 * (k : ℝ))) ^ 2) / 2)
  have hpair_one : 1 ≤ ((offdiagPairFinset (Feature := Fin m)).card : ℝ) :=
    one_le_offdiagPairFinset_fin_card_of_two_le hm
  have hlog_arg_one :
      1 ≤ 2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ) := by
    nlinarith
  have hlog_nonneg :
      0 ≤ Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) :=
    Real.log_nonneg hlog_arg_one
  have hden_pos :
      0 < (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) := by
    have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
    positivity
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg hlog_nonneg hden_pos.le
  have hceil :
      (Nat.ceil x : ℝ) < x + 1 :=
    Nat.ceil_lt_add_one hx_nonneg
  have hD :
      (rademacherUpperDimension m k epsilon : ℝ) =
        (Nat.ceil x : ℝ) + 1 := by
    simp [rademacherUpperDimension, x]
  rw [hD]
  change (Nat.ceil x : ℝ) + 1 ≤ x + 2
  linarith

theorem rademacherUpperDimension_cast_le_log_m_sq_tail_add_two
    {m k : ℕ} {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    (rademacherUpperDimension m k epsilon : ℝ) ≤
      Real.log (2 * (m : ℝ) ^ 2) /
      (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) + 2 := by
  have hbase :=
    rademacherUpperDimension_cast_le_log_tail_add_two
      (m := m) (k := k) (epsilon := epsilon) hm hk hepsilon
  have hpair_one : 1 ≤ ((offdiagPairFinset (Feature := Fin m)).card : ℝ) :=
    one_le_offdiagPairFinset_fin_card_of_two_le hm
  have hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ) := by
    linarith
  have hm_real_pos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm)
  have harg_pos :
      0 < 2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ) := by
    positivity
  have harg_le : 2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ) ≤
      2 * (m : ℝ) ^ 2 := by
    nlinarith [offdiagPairFinset_fin_card_le_sq m]
  have hlog_le :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) ≤
        Real.log (2 * (m : ℝ) ^ 2) :=
    Real.log_le_log harg_pos harg_le
  have hden_pos :
      0 < (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) := by
    have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
    positivity
  have hfrac_le :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) /
          (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) ≤
        Real.log (2 * (m : ℝ) ^ 2) /
          (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) := by
    exact div_le_div_of_nonneg_right hlog_le hden_pos.le
  linarith

/--
Concrete incoherent Rademacher dimension bounded by its exact ordered-pair
logarithmic threshold plus the ceiling slack.
-/
theorem rademacherIncoherentDimension_cast_le_log_tail_add_two
    {m : ℕ} {mu : ℝ} (hm : 2 ≤ m) (hmu : 0 < mu) :
    (rademacherIncoherentDimension m mu : ℝ) ≤
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) /
          ((mu ^ 2) / 2) + 2 := by
  let x : ℝ :=
    Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) /
      ((mu ^ 2) / 2)
  have hpair_one : 1 ≤ ((offdiagPairFinset (Feature := Fin m)).card : ℝ) :=
    one_le_offdiagPairFinset_fin_card_of_two_le hm
  have hlog_arg_one :
      1 ≤ 2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ) := by
    nlinarith
  have hlog_nonneg :
      0 ≤ Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) :=
    Real.log_nonneg hlog_arg_one
  have hden_pos : 0 < (mu ^ 2) / 2 := by positivity
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg hlog_nonneg hden_pos.le
  have hceil :
      (Nat.ceil x : ℝ) < x + 1 :=
    Nat.ceil_lt_add_one hx_nonneg
  have hD :
      (rademacherIncoherentDimension m mu : ℝ) =
        (Nat.ceil x : ℝ) + 1 := by
    simp [rademacherIncoherentDimension, x]
  rw [hD]
  change (Nat.ceil x : ℝ) + 1 ≤ x + 2
  linarith

/--
Concrete incoherent Rademacher dimension bounded in the source-readable
`log m / mu^2` scale using the elementary ordered-pair estimate.
-/
theorem rademacherIncoherentDimension_cast_le_log_m_sq_tail_add_two
    {m : ℕ} {mu : ℝ} (hm : 2 ≤ m) (hmu : 0 < mu) :
    (rademacherIncoherentDimension m mu : ℝ) ≤
      Real.log (2 * (m : ℝ) ^ 2) / ((mu ^ 2) / 2) + 2 := by
  have hbase :=
    rademacherIncoherentDimension_cast_le_log_tail_add_two
      (m := m) (mu := mu) hm hmu
  have hpair_one : 1 ≤ ((offdiagPairFinset (Feature := Fin m)).card : ℝ) :=
    one_le_offdiagPairFinset_fin_card_of_two_le hm
  have harg_pos :
      0 < 2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ) := by
    positivity
  have harg_le : 2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ) ≤
      2 * (m : ℝ) ^ 2 := by
    nlinarith [offdiagPairFinset_fin_card_le_sq m]
  have hlog_le :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) ≤
        Real.log (2 * (m : ℝ) ^ 2) :=
    Real.log_le_log harg_pos harg_le
  have hden_pos : 0 < (mu ^ 2) / 2 := by positivity
  have hfrac_le :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) /
          ((mu ^ 2) / 2) ≤
        Real.log (2 * (m : ℝ) ^ 2) / ((mu ^ 2) / 2) := by
    exact div_le_div_of_nonneg_right hlog_le hden_pos.le
  linarith

/--
Concrete incoherent Rademacher dimension with the hidden
`O((log m) / mu^2)` constant made explicit.
-/
theorem rademacherIncoherentDimension_cast_le_bigO_envelope
    {m : ℕ} {mu : ℝ} (hm : 2 ≤ m) (hmu : 0 < mu) :
    (rademacherIncoherentDimension m mu : ℝ) ≤
      (2 / mu ^ 2) * Real.log (2 * (m : ℝ) ^ 2) + 2 := by
  have hbound :=
    rademacherIncoherentDimension_cast_le_log_m_sq_tail_add_two
      (m := m) (mu := mu) hm hmu
  have hmu_ne : mu ≠ 0 := ne_of_gt hmu
  have hrewrite :
      Real.log (2 * (m : ℝ) ^ 2) / ((mu ^ 2) / 2) + 2 =
        (2 / mu ^ 2) * Real.log (2 * (m : ℝ) ^ 2) + 2 := by
    field_simp [hmu_ne]
  simpa [hrewrite] using hbound

/--
The confidence-aware Rademacher dimension is at most the source's explicit
`log(m^2 / delta) / mu^2` envelope, up to the one-integer ceiling slack.
-/
theorem rademacherIncoherentDimensionAtConfidence_cast_le_log_m_sq_tail_add_two
    {m : ℕ} {mu delta : ℝ}
    (hm : 2 ≤ m) (hmu : 0 < mu)
    (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    (rademacherIncoherentDimensionAtConfidence m mu delta : ℝ) ≤
      Real.log (2 * (m : ℝ) ^ 2 / delta) / ((mu ^ 2) / 2) + 2 := by
  let x : ℝ :=
    Real.log
        ((2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta) /
      ((mu ^ 2) / 2)
  have hpair_one : 1 ≤ ((offdiagPairFinset (Feature := Fin m)).card : ℝ) :=
    one_le_offdiagPairFinset_fin_card_of_two_le hm
  have hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ) := by
    linarith
  have hsource_arg_one :
      1 ≤ (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta := by
    apply (le_div_iff₀ hdelta).mpr
    nlinarith
  have hsource_log_nonneg :
      0 ≤ Real.log
        ((2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta) :=
    Real.log_nonneg hsource_arg_one
  have hden_pos : 0 < (mu ^ 2) / 2 := by positivity
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg hsource_log_nonneg hden_pos.le
  have hceil : (Nat.ceil x : ℝ) < x + 1 :=
    Nat.ceil_lt_add_one hx_nonneg
  have hD :
      (rademacherIncoherentDimensionAtConfidence m mu delta : ℝ) =
        (Nat.ceil x : ℝ) + 1 := by
    simp [rademacherIncoherentDimensionAtConfidence, x]
  have hsource_arg_pos :
      0 < (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta := by
    positivity
  have hsource_arg_le :
      (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta ≤
        2 * (m : ℝ) ^ 2 / delta := by
    apply div_le_div_of_nonneg_right _ hdelta.le
    nlinarith [offdiagPairFinset_fin_card_le_sq m]
  have hlog_le :
      Real.log
          ((2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta) ≤
        Real.log (2 * (m : ℝ) ^ 2 / delta) :=
    Real.log_le_log hsource_arg_pos hsource_arg_le
  have hfrac_le : x ≤ Real.log (2 * (m : ℝ) ^ 2 / delta) / ((mu ^ 2) / 2) := by
    dsimp [x]
    exact div_le_div_of_nonneg_right hlog_le hden_pos.le
  rw [hD]
  linarith

/--
Source-facing random-matrix construction for Lemma `prop:incoherent`: in the
standard nondegenerate confidence regime, an explicit rounded logarithmic
dimension makes an i.i.d. scaled-Rademacher matrix `mu`-incoherent with
probability at least `1 - delta`.
-/
theorem exists_rademacher_strict_incoherence_at_explicit_logarithmic_dimension
    {m : ℕ} {mu delta : ℝ}
    (hm : 2 ≤ m) (hmu : 0 < mu)
    (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1) :
    ∃ d : ℕ, 0 < d ∧
      (d : ℝ) ≤ Real.log (2 * (m : ℝ) ^ 2 / delta) / ((mu ^ 2) / 2) + 2 ∧
      (AppliedModelingLib.measureProb (rowsMeasure (Fin m) (Fin d))
          (fun ω =>
            ∀ ⦃i j : Fin m⦄, i ≠ j →
              |inner (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i)
                (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω j)| < mu) ≥
        1 - delta) ∧
      (∀ (ω : Fin d → Fin m → Bool) (i : Fin m),
        inner (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i)
          (scaledMatrix (Feature := Fin m) (Coord := Fin d) ω i) = 1) := by
  let D : ℕ := rademacherIncoherentDimensionAtConfidence m mu delta
  have hD_pos : 0 < D := by
    dsimp [D, rademacherIncoherentDimensionAtConfidence]
    omega
  have hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ) :=
    offdiagPairFinset_fin_card_pos_of_two_le hm
  have hden_pos : 0 < (mu ^ 2) / 2 := by positivity
  have hthreshold_lt_D :
      Real.log
          ((2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta) /
          ((mu ^ 2) / 2) < (D : ℝ) := by
    simpa [D, rademacherIncoherentDimensionAtConfidence] using
      real_lt_natCeil_add_one
        (Real.log
          ((2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta) /
          ((mu ^ 2) / 2))
  have hlog_mu :
      Real.log
          ((2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta) <
        (D : ℝ) * ((mu ^ 2) / 2) :=
    (div_lt_iff₀ hden_pos).mp hthreshold_lt_D
  have hlog :
      Real.log
          ((2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) / delta) ≤
        ((D : ℝ) * mu ^ 2) / 2 := by
    nlinarith
  refine ⟨D, hD_pos, ?_, ?_, ?_⟩
  · exact
      rademacherIncoherentDimensionAtConfidence_cast_le_log_m_sq_tail_add_two
        (m := m) (mu := mu) (delta := delta) hm hmu hdelta hdelta_le_one
  · exact rademacher_strict_incoherence_probability_ge_one_sub_delta_of_log_div_le
      hD_pos hmu.le hpair_pos hdelta hlog
  · intro omega i
    have hcard : 0 < Fintype.card (Fin D) := by
      simpa using hD_pos
    exact inner_scaledMatrix_self (Feature := Fin m) (Coord := Fin D) hcard omega i

/--
Finite Rademacher incoherent-matrix existence at the explicit rounded
dimension.
-/
theorem exists_muIncoherent_rademacherIncoherentDimension_of_two_le
    {m : ℕ} {mu : ℝ} (hm : 2 ≤ m) (hmu : 0 < mu) :
    ∃ A : FeatureMatrix m (rademacherIncoherentDimension m mu),
      muIncoherent A mu := by
  let D : ℕ := rademacherIncoherentDimension m mu
  have hD_pos : 0 < D := by
    dsimp [D, rademacherIncoherentDimension]
    omega
  have hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ) :=
    offdiagPairFinset_fin_card_pos_of_two_le hm
  have htail_den_pos : 0 < (mu ^ 2) / 2 := by
    positivity
  have hthreshold_lt_D :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) /
          ((mu ^ 2) / 2) < (D : ℝ) := by
    simpa [D, rademacherIncoherentDimension] using
      real_lt_natCeil_add_one
        (Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) /
          ((mu ^ 2) / 2))
  have hlog_mu :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) <
        (D : ℝ) * ((mu ^ 2) / 2) :=
    (div_lt_iff₀ htail_den_pos).mp hthreshold_lt_D
  have hlog :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) <
        ((Fintype.card (Fin D) : ℝ) * mu ^ 2) / 2 := by
    simpa [Fintype.card_fin, mul_div_assoc] using hlog_mu
  have hbad_lt_one :
      ((offdiagPairFinset (Feature := Fin m)).card : ℝ) *
          (2 * Real.exp (-((D : ℝ) * mu ^ 2) / 2)) < 1 := by
    have htail :=
      pair_count_mul_fixedPairTailBound_lt_one_of_log_lt
        (Coord := Fin D)
        (pairCount := ((offdiagPairFinset (Feature := Fin m)).card : ℝ))
        (μ := mu) hpair_pos hlog
    simpa [fixedPairTailBound_eq] using htail
  exact
    exists_muIncoherent_of_rademacher_source_tail_lt_one
      (m := m) (d := D) hD_pos hmu.le hbad_lt_one

/--
Rounded-dimension Rademacher exact-recovery witness at any coherence level
small enough for the deterministic basis-pursuit theorem.
-/
theorem exists_basisPursuitExactRecovery_rademacherIncoherentDimension_of_two_le
    {m k : ℕ} {mu : ℝ} (hm : 2 ≤ m) (hmu : 0 < mu)
    (hbound : (k : ℝ) * mu < 1 / 2) :
    ∃ A : FeatureMatrix m (rademacherIncoherentDimension m mu),
      basisPursuitExactRecovery A k := by
  rcases exists_muIncoherent_rademacherIncoherentDimension_of_two_le
    (m := m) (mu := mu) hm hmu with ⟨A, hA⟩
  exact ⟨A, basisPursuitExactRecovery_of_muIncoherent hmu.le hA hbound⟩

/--
Explicit coherence-scale basis-pursuit recovery witness.  Taking
`mu = 1/(4k)` gives exact recovery in a rounded Rademacher dimension bounded by
`O(k^2 log m)`.  This is intentionally weaker than the recalled classical
compressed-sensing `O(k log(m/k))` theorem.
-/
theorem exists_basisPursuitExactRecovery_coherence_scale
    {m k : ℕ} (hm : 2 ≤ m) (hk : 0 < k) :
    ∃ d : ℕ, ∃ A : FeatureMatrix m d,
      (d : ℝ) ≤ 32 * (k : ℝ) ^ 2 * Real.log (2 * (m : ℝ) ^ 2) + 2 ∧
        basisPursuitExactRecovery A k := by
  let mu : ℝ := 1 / (4 * (k : ℝ))
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hk_real_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_real_pos
  have hmu_pos : 0 < mu := by
    dsimp [mu]
    positivity
  have hbound : (k : ℝ) * mu < 1 / 2 := by
    have hmul : (k : ℝ) * mu = 1 / 4 := by
      dsimp [mu]
      field_simp [hk_real_ne]
    rw [hmul]
    norm_num
  rcases exists_basisPursuitExactRecovery_rademacherIncoherentDimension_of_two_le
    (m := m) (k := k) (mu := mu) hm hmu_pos hbound with ⟨A, hA⟩
  have hdim :=
    rademacherIncoherentDimension_cast_le_bigO_envelope
      (m := m) (mu := mu) hm hmu_pos
  have hcoef : 2 / mu ^ 2 = 32 * (k : ℝ) ^ 2 := by
    dsimp [mu]
    field_simp [hk_real_ne]
    ring
  refine ⟨rademacherIncoherentDimension m mu, A, ?_, hA⟩
  simpa [hcoef, mul_assoc] using hdim

/--
Finite existential Geometry Proposition 1 construction.  The Rademacher
incoherent family supplies the auxiliary columns `c_i, a*, b*`; the source
construction then gives representation/probe matrices satisfying recovery and
the three displayed finite correlation bounds.
-/
theorem exists_geometry1_constructed_matrices_rademacherIncoherentDimension
    {m k : ℕ} {epsilon lambda mu : ℝ}
    (hlambda : 0 ≤ lambda) (hmu : 0 < mu)
    (hbound :
      (2 * lambda + lambda ^ 2) * mu +
          (k : ℝ) * ((1 + 2 * lambda + lambda ^ 2) * mu) < epsilon)
    (hs : 0 < 1 + lambda ^ 2 - 2 * lambda * mu)
    (hnum : 0 ≤ lambda ^ 2 - (1 + 2 * lambda) * mu) :
    ∃ A B : FeatureMatrix m
        (rademacherIncoherentDimension (m + 2) mu),
      linearRecoveryCondition A B k epsilon ∧
        (∀ i : Fin m,
          |columnCorrelation (A i) (B i)| ≤
            (1 + (2 * lambda + lambda ^ 2) * mu) /
              (1 + lambda ^ 2 - 2 * lambda * mu)) ∧
        (∀ ⦃i j : Fin m⦄, i ≠ j →
          (lambda ^ 2 - (1 + 2 * lambda) * mu) /
              (1 + lambda ^ 2 + 2 * lambda * mu) ≤
            columnCorrelation (A i) (A j)) ∧
        (∀ ⦃i j : Fin m⦄, i ≠ j →
          (lambda ^ 2 - (1 + 2 * lambda) * mu) /
              (1 + lambda ^ 2 + 2 * lambda * mu) ≤
            columnCorrelation (B i) (B j)) := by
  rcases exists_muIncoherent_rademacherIncoherentDimension_of_two_le
      (m := m + 2) (mu := mu) (by omega) hmu with
    ⟨C, hC⟩
  refine ⟨geometry1RepresentationMatrix C lambda,
    geometry1ProbeMatrix C lambda, ?_, ?_, ?_, ?_⟩
  · exact geometry1_linearRecoveryCondition
      (C := C) (lambda := lambda) (mu := mu)
      hlambda hmu.le hC hbound
  · intro i
    exact geometry1_self_columnCorrelation_abs_le
      (C := C) (lambda := lambda) (mu := mu) hlambda hC hs i
  · intro i j hij
    exact geometry1_representation_columnCorrelation_lower
      (C := C) (lambda := lambda) (mu := mu)
      hlambda hmu.le hC hs hnum hij
  · intro i j hij
    exact geometry1_probe_columnCorrelation_lower
      (C := C) (lambda := lambda) (mu := mu)
      hlambda hmu.le hC hs hnum hij

/--
Finite source-parameter realization of Geometry Proposition 1.  This fixes
the paper's `epsilon, delta` parameters, uses its prescribed `lambda`, and
supplies the simultaneous recovery and three correlation envelopes.
-/
theorem exists_geometry1_source_parameter_construction
    {m k : ℕ} {epsilon delta : ℝ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_lt_one : epsilon < 1)
    (hdelta_pos : 0 < delta) (hdelta_lt_one : delta < 1) :
    ∃ D : ℕ,
      (D : ℝ) ≤
          geometry1SourceDimensionCoefficient epsilon delta *
            ((k + 1 : ℕ) : ℝ) ^ 2 *
            Real.log (2 * ((m + 2 : ℕ) : ℝ) ^ 2) + 2 ∧
        ∃ A B : FeatureMatrix m D,
          linearRecoveryCondition A B k epsilon ∧
            (∀ i : Fin m,
              |columnCorrelation (A i) (B i)| ≤
                geometry1SelfCorrelationEnvelope
                  (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k)) ∧
            (∀ ⦃i j : Fin m⦄, i ≠ j →
              geometry1OffdiagCorrelationEnvelope
                (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k) ≤
                columnCorrelation (A i) (A j)) ∧
            (∀ ⦃i j : Fin m⦄, i ≠ j →
              geometry1OffdiagCorrelationEnvelope
                (geometry1SourceLambda delta) (geometry1SourceMu epsilon delta k) ≤
                columnCorrelation (B i) (B j)) := by
  let lambda : ℝ := geometry1SourceLambda delta
  let mu : ℝ := geometry1SourceMu epsilon delta k
  have hlambda_pos : 0 < lambda := by
    simpa [lambda] using geometry1SourceLambda_pos hdelta_pos hdelta_lt_one
  have hmu_pos : 0 < mu := by
    simpa [mu] using geometry1SourceMu_pos
      (k := k) hepsilon_pos hdelta_pos hdelta_lt_one
  have hconditions := geometry1SourceMu_construction_side_conditions
    (k := k) hepsilon_pos hepsilon_lt_one hdelta_pos hdelta_lt_one
  change
    (2 * lambda + lambda ^ 2) * mu +
        (k : ℝ) * ((1 + 2 * lambda + lambda ^ 2) * mu) < epsilon ∧
      0 < 1 + lambda ^ 2 - 2 * lambda * mu ∧
      0 ≤ lambda ^ 2 - (1 + 2 * lambda) * mu at hconditions
  rcases hconditions with ⟨hbound, hs, hnum⟩
  refine ⟨rademacherIncoherentDimension (m + 2) mu, ?_, ?_⟩
  · rw [← geometry1SourceMu_dimension_coefficient
      (k := k) hepsilon_pos hdelta_pos hdelta_lt_one]
    exact rademacherIncoherentDimension_cast_le_bigO_envelope
      (m := m + 2) (mu := mu) (by omega) hmu_pos
  · rcases exists_geometry1_constructed_matrices_rademacherIncoherentDimension
      (m := m) (k := k) (epsilon := epsilon) (lambda := lambda) (mu := mu)
      hlambda_pos.le hmu_pos hbound hs hnum with ⟨A, B, hrec, hself, hA, hB⟩
    refine ⟨A, B, hrec, ?_, ?_, ?_⟩
    · simpa [geometry1SelfCorrelationEnvelope] using hself
    · simpa [geometry1OffdiagCorrelationEnvelope] using hA
    · simpa [geometry1OffdiagCorrelationEnvelope] using hB

/--
Explicit finite upper-bound witness behind `d(m,k,epsilon) =
O_epsilon(k^2 log m)`: the concrete logarithmic Rademacher dimension satisfies
linear compressed-sensing feasibility.
-/
theorem linearCompressedSensingFeasible_rademacherUpperDimension
    {m k : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hepsilon : 0 < epsilon)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) :
    linearCompressedSensingFeasible m k
      (rademacherUpperDimension m k epsilon) epsilon := by
  let D : ℕ := rademacherUpperDimension m k epsilon
  have hD_pos : 0 < D := by
    dsimp [D, rademacherUpperDimension]
    omega
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hden_pos : 0 < 2 * (k : ℝ) := by positivity
  have hmu_pos : 0 < epsilon / (2 * (k : ℝ)) := by
    exact div_pos hepsilon hden_pos
  have htail_den_pos :
      0 < ((epsilon / (2 * (k : ℝ))) ^ 2) / 2 := by
    positivity
  have hthreshold_lt_D :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) /
          (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) <
        (D : ℝ) := by
    simpa [D, rademacherUpperDimension] using
      real_lt_natCeil_add_one
        (Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) /
          (((epsilon / (2 * (k : ℝ))) ^ 2) / 2))
  have hlog_mu :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) <
        (D : ℝ) * (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) :=
    (div_lt_iff₀ htail_den_pos).mp hthreshold_lt_D
  have hlog :
      Real.log (2 * ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) <
        ((Fintype.card (Fin D) : ℝ) *
          (epsilon / (2 * (k : ℝ))) ^ 2) / 2 := by
    simpa [Fintype.card_fin, mul_div_assoc] using hlog_mu
  exact
    linearCompressedSensingFeasible_of_rademacher_log_tail_epsilon_over_two_k
      (m := m) (d := D) (k := k) (epsilon := epsilon)
      hD_pos hk hepsilon hpair_pos hlog

/--
Minimum-dimension upper bound obtained from the explicit Rademacher
construction.
-/
theorem exists_linearCompressedSensingDimensionValue_le_rademacherUpperDimension
    (m k : ℕ) {epsilon : ℝ}
    (hk : 0 < k) (hepsilon : 0 < epsilon)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Fin m)).card : ℝ)) :
    ∃ d : ℕ, linearCompressedSensingDimensionValue m k epsilon d ∧
      d ≤ rademacherUpperDimension m k epsilon := by
  rcases exists_linearCompressedSensingDimensionValue m k hepsilon with
    ⟨d, hd⟩
  have hfeas :
      linearCompressedSensingFeasible m k
        (rademacherUpperDimension m k epsilon) epsilon :=
    linearCompressedSensingFeasible_rademacherUpperDimension
      (m := m) (k := k) (epsilon := epsilon) hk hepsilon hpair_pos
  exact ⟨d, hd, hd.2 _ hfeas⟩

theorem linearCompressedSensingFeasible_rademacherUpperDimension_of_two_le
    {m k : ℕ} {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    linearCompressedSensingFeasible m k
      (rademacherUpperDimension m k epsilon) epsilon :=
  linearCompressedSensingFeasible_rademacherUpperDimension
    (m := m) (k := k) (epsilon := epsilon)
    hk hepsilon (offdiagPairFinset_fin_card_pos_of_two_le hm)

theorem exists_linearCompressedSensingDimensionValue_le_rademacherUpperDimension_of_two_le
    (m k : ℕ) {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    ∃ d : ℕ, linearCompressedSensingDimensionValue m k epsilon d ∧
      d ≤ rademacherUpperDimension m k epsilon :=
  exists_linearCompressedSensingDimensionValue_le_rademacherUpperDimension
    m k hk hepsilon (offdiagPairFinset_fin_card_pos_of_two_le hm)

/--
Minimum-dimension upper bound in the same logarithmic scale as the concrete
Rademacher witness.  This is the finite form of the paper's
`O_epsilon(k^2 log m)` upper bound for `d(m,k,epsilon)`.
-/
theorem exists_linearCompressedSensingDimensionValue_real_le_log_m_sq_tail_add_two
    (m k : ℕ) {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    ∃ d : ℕ,
      linearCompressedSensingDimensionValue m k epsilon d ∧
        (d : ℝ) ≤
          Real.log (2 * (m : ℝ) ^ 2) /
              (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) + 2 := by
  rcases
    exists_linearCompressedSensingDimensionValue_le_rademacherUpperDimension_of_two_le
      m k hm hk hepsilon with
    ⟨d, hvalue, hd_le_upper⟩
  have hupper :
      (rademacherUpperDimension m k epsilon : ℝ) ≤
        Real.log (2 * (m : ℝ) ^ 2) /
            (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) + 2 :=
    rademacherUpperDimension_cast_le_log_m_sq_tail_add_two
      (m := m) (k := k) (epsilon := epsilon) hm hk hepsilon
  have hd_le_upper_real :
      (d : ℝ) ≤ (rademacherUpperDimension m k epsilon : ℝ) := by
    exact_mod_cast hd_le_upper
  exact ⟨d, hvalue, hd_le_upper_real.trans hupper⟩

/--
Minimum-dimension upper bound with the logarithmic Rademacher tail written as
an explicit `O_epsilon(k^2 log m)` envelope.
-/
theorem exists_linearCompressedSensingDimensionValue_real_le_upper_bigO_envelope
    (m k : ℕ) {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    ∃ d : ℕ,
      linearCompressedSensingDimensionValue m k epsilon d ∧
        (d : ℝ) ≤
          (8 * (k : ℝ) ^ 2 / epsilon ^ 2) *
              Real.log (2 * (m : ℝ) ^ 2) + 2 := by
  rcases
    exists_linearCompressedSensingDimensionValue_real_le_log_m_sq_tail_add_two
      m k hm hk hepsilon with
    ⟨d, hvalue, hbound⟩
  have hk_ne : (k : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hk
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon
  have hrewrite :
      Real.log (2 * (m : ℝ) ^ 2) /
            (((epsilon / (2 * (k : ℝ))) ^ 2) / 2) + 2 =
        (8 * (k : ℝ) ^ 2 / epsilon ^ 2) *
            Real.log (2 * (m : ℝ) ^ 2) + 2 := by
    field_simp [hk_ne, hepsilon_ne]
    ring
  exact ⟨d, hvalue, by simpa [hrewrite] using hbound⟩

/--
Minimum-dimension upper bound with the `log(2m^2) + 2` finite tail absorbed
into a single `k^2 log m` envelope.  This is a source-readable explicit
Big-O witness for fixed positive `epsilon`.
-/
theorem exists_linearCompressedSensingDimensionValue_real_le_upper_log_m_envelope
    (m k : ℕ) {epsilon : ℝ}
    (hm : 2 ≤ m) (hk : 0 < k) (hepsilon : 0 < epsilon) :
    ∃ d : ℕ,
      linearCompressedSensingDimensionValue m k epsilon d ∧
        (d : ℝ) ≤
          ((24 / epsilon ^ 2) + 2 / Real.log 2) *
            (k : ℝ) ^ 2 * Real.log (m : ℝ) := by
  rcases
    exists_linearCompressedSensingDimensionValue_real_le_upper_bigO_envelope
      m k hm hk hepsilon with
    ⟨d, hvalue, hbound⟩
  have hm_one : 1 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hm)
  have hm_pos : 0 < (m : ℝ) := lt_trans (by norm_num : (0 : ℝ) < 1) hm_one
  have hlog_m_pos : 0 < Real.log (m : ℝ) := Real.log_pos hm_one
  have hlog_two_pos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog_two_le_log_m : Real.log (2 : ℝ) ≤ Real.log (m : ℝ) := by
    exact Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast hm)
  have hlog_sq :
      Real.log (2 * (m : ℝ) ^ 2) =
        Real.log (2 : ℝ) + 2 * Real.log (m : ℝ) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 hm_pos.ne')]
    rw [Real.log_pow]
    ring
  have hlog_bound :
      Real.log (2 * (m : ℝ) ^ 2) ≤ 3 * Real.log (m : ℝ) := by
    rw [hlog_sq]
    linarith
  have hepsilon_sq_pos : 0 < epsilon ^ 2 := sq_pos_of_ne_zero hepsilon.ne'
  have hcoef_nonneg : 0 ≤ 8 * (k : ℝ) ^ 2 / epsilon ^ 2 := by
    positivity
  have hterm1 :
      (8 * (k : ℝ) ^ 2 / epsilon ^ 2) *
          Real.log (2 * (m : ℝ) ^ 2) ≤
        (24 / epsilon ^ 2) * (k : ℝ) ^ 2 * Real.log (m : ℝ) := by
    calc
      (8 * (k : ℝ) ^ 2 / epsilon ^ 2) *
          Real.log (2 * (m : ℝ) ^ 2)
          ≤ (8 * (k : ℝ) ^ 2 / epsilon ^ 2) *
              (3 * Real.log (m : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog_bound hcoef_nonneg
      _ = (24 / epsilon ^ 2) * (k : ℝ) ^ 2 * Real.log (m : ℝ) := by
            ring
  have hk_sq_ge_one : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have hk_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith
  have hlog_product :
      Real.log (2 : ℝ) ≤ (k : ℝ) ^ 2 * Real.log (m : ℝ) := by
    calc
      Real.log (2 : ℝ) = 1 * Real.log (2 : ℝ) := by ring
      _ ≤ (k : ℝ) ^ 2 * Real.log (m : ℝ) :=
        mul_le_mul hk_sq_ge_one hlog_two_le_log_m hlog_two_pos.le
          (by norm_num)
  have hterm2 :
      (2 : ℝ) ≤ (2 / Real.log 2) *
          (k : ℝ) ^ 2 * Real.log (m : ℝ) := by
    calc
      (2 : ℝ) = (2 / Real.log 2) * Real.log (2 : ℝ) := by
        field_simp [hlog_two_pos.ne']
      _ ≤ (2 / Real.log 2) * ((k : ℝ) ^ 2 * Real.log (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog_product (by positivity)
      _ = (2 / Real.log 2) * (k : ℝ) ^ 2 * Real.log (m : ℝ) := by
        ring
  refine ⟨d, hvalue, ?_⟩
  calc
    (d : ℝ)
        ≤ (8 * (k : ℝ) ^ 2 / epsilon ^ 2) *
            Real.log (2 * (m : ℝ) ^ 2) + 2 := hbound
    _ ≤ (24 / epsilon ^ 2) * (k : ℝ) ^ 2 * Real.log (m : ℝ) +
          (2 / Real.log 2) * (k : ℝ) ^ 2 * Real.log (m : ℝ) :=
        add_le_add hterm1 hterm2
    _ = ((24 / epsilon ^ 2) + 2 / Real.log 2) *
          (k : ℝ) ^ 2 * Real.log (m : ℝ) := by
        ring

/--
Theorem `thm:upper`, genuine paper-style Big-O wrapper for the minimum
dimension function.  The hidden constant is the explicit epsilon-dependent
constant from `exists_linearCompressedSensingDimensionValue_real_le_upper_log_m_envelope`.
-/
theorem linearCompressedSensingDimension_isBigO_upper_log_m
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Asymptotics.IsBigO (Filter.atTop : Filter (ℕ × ℕ))
      (fun p : ℕ × ℕ =>
        (linearCompressedSensingDimension p.1 p.2 epsilon : ℝ))
      (fun p : ℕ × ℕ => (p.2 : ℝ) ^ 2 * Real.log (p.1 : ℝ)) := by
  let C : ℝ := (24 / epsilon ^ 2) + 2 / Real.log 2
  have hC_nonneg : 0 ≤ C := by
    have heps_sq_pos : 0 < epsilon ^ 2 := sq_pos_of_ne_zero (ne_of_gt hepsilon)
    have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  refine AppliedModelingLib.Math.isBigO_of_eventually_nonneg_le_const_mul
    (C := C) hC_nonneg ?_ ?_ ?_
  · filter_upwards with p
    exact Nat.cast_nonneg _
  · refine eventually_atTop.2 ⟨(2, 0), ?_⟩
    intro p hp
    have hm : 1 ≤ p.1 := le_trans (by norm_num : 1 ≤ (2 : ℕ)) hp.1
    have hlog_nonneg : 0 ≤ Real.log (p.1 : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hm)
    exact mul_nonneg (sq_nonneg _) hlog_nonneg
  · refine eventually_atTop.2 ⟨(2, 1), ?_⟩
    intro p hp
    have hm : 2 ≤ p.1 := hp.1
    have hk : 0 < p.2 := Nat.succ_le_iff.mp hp.2
    rcases exists_linearCompressedSensingDimensionValue_real_le_upper_log_m_envelope
        (m := p.1) (k := p.2) (epsilon := epsilon) hm hk hepsilon with
      ⟨d, hvalue, hbound⟩
    have hdim_value :
        linearCompressedSensingDimensionValue p.1 p.2 epsilon
          (linearCompressedSensingDimension p.1 p.2 epsilon) :=
      linearCompressedSensingDimension_spec p.1 p.2 hepsilon
    have hdim_eq :
        linearCompressedSensingDimension p.1 p.2 epsilon = d :=
      linearCompressedSensingDimensionValue_unique hdim_value hvalue
    simpa [C, hdim_eq, mul_assoc] using hbound

/--
Restricted source regime for the lower-bound asymptotic theorem.  The paper's
condition `epsilon > sqrt(5) k^(3/2) / sqrt(m)` is represented by the squared
inequality `5 k^3 < epsilon^2 m`; the final conjunct is the large-`k`
side condition used by the finite rank/Turán proof.
-/
def linearCompressedSensingLowerSourceRegime
    (epsilon : ℝ) (p : ℕ × ℕ) : Prop :=
  2 ≤ p.2 ∧
    0 ≤ epsilon ∧
    epsilon < 1 ∧
    5 * (p.2 : ℝ) ^ 3 < epsilon ^ 2 * (p.1 : ℝ)

/--
The restricted-at-infinity filter for the source lower-bound regime.  This is
the natural formal counterpart of a conditional `Omega_epsilon` statement:
asymptotics are taken along problem sizes satisfying the theorem's source
growth assumptions.
-/
noncomputable def linearCompressedSensingLowerSourceFilter
    (epsilon : ℝ) : Filter (ℕ × ℕ) :=
  Filter.atTop ⊓
    Filter.principal
      {p : ℕ × ℕ | linearCompressedSensingLowerSourceRegime epsilon p}

/--
The floor-log scale delivered directly by the finite rank/Turán proof:
`k^2 log floor(m/(4k+1)) / log k`.
-/
noncomputable def linearCompressedSensingLowerFloorLogScale
    (p : ℕ × ℕ) : ℝ :=
  (p.2 : ℝ) ^ 2 *
    (Real.log
        (Nat.floor ((p.1 : ℝ) / ((4 * p.2 + 1 : ℕ) : ℝ)) : ℝ) /
      Real.log (p.2 : ℝ))

/--
The printed source scale in Theorem `thm:lower`:
`(k^2 / log k) * log(m/k)`.
-/
noncomputable def linearCompressedSensingLowerSourceLogScale
    (p : ℕ × ℕ) : ℝ :=
  (p.2 : ℝ) ^ 2 *
    (Real.log ((p.1 : ℝ) / (p.2 : ℝ)) / Real.log (p.2 : ℝ))

/-- Source rank observation: `rank(B^T A) <= d`. -/
theorem interferenceMatrix_rank_le_d
    {m d : ℕ} (A B : FeatureMatrix m d) :
    (interferenceMatrix A B).rank ≤ d := by
  simpa using
    crossInnerMatrix_rank_le_card_coord
      (Feature := Fin m) (Coord := Fin d) A B

/-- Source rank observation for principal submatrices of `B^T A`. -/
theorem interferenceMatrix_principalSubmatrix_rank_le_d
    {m d : ℕ} {Sub : Type*} [Fintype Sub]
    (A B : FeatureMatrix m d) (select : Sub → Fin m) :
    ((interferenceMatrix A B).submatrix select select).rank ≤ d := by
  simpa using
    crossInnerMatrix_principalSubmatrix_rank_le_card_coord
      (Feature := Fin m) (Coord := Fin d) A B select

/--
Source equation `eq:leek`: testing the recovery condition on a singleton
feature vector shows that each diagonal entry of `B^T A` is within `epsilon`
of `1`.
-/
theorem diagonal_abs_sub_one_lt_of_linearRecoveryCondition
    {m d k : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hk : 1 ≤ k) (hrec : linearRecoveryCondition A B k epsilon)
    (i : Fin m) :
    |inner (B i) (A i) - 1| < epsilon := by
  exact
    diag_abs_sub_one_lt_of_linearRecovery
      (A := A) (B := B) (k := k) (ε := epsilon) hk hrec i

/--
Lower diagonal form used to feed the Alon-rank corollary after setting
`gamma = 1 - epsilon`.
-/
theorem one_sub_epsilon_lt_diagonal_of_linearRecoveryCondition
    {m d k : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hk : 1 ≤ k) (hrec : linearRecoveryCondition A B k epsilon)
    (i : Fin m) :
    1 - epsilon < inner (B i) (A i) := by
  exact
    one_sub_lt_diag_of_linearRecovery
      (A := A) (B := B) (k := k) (ε := epsilon) hk hrec i

/--
Source equation `eq:fennel`: testing the recovery condition on a `{0,1}`
indicator set disjoint from row `i` bounds the corresponding row sum.
-/
theorem row_sum_abs_lt_of_linearRecoveryCondition_finset_not_mem
    {m d k : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    {T : Finset (Fin m)} {i : Fin m} (hT : T.card ≤ k) (hi : i ∉ T) :
    |∑ j ∈ T, inner (B i) (A j)| < epsilon := by
  exact
    abs_row_sum_lt_of_linearRecovery_finsetIndicator_not_mem
      (A := A) (B := B) (k := k) (ε := epsilon) hrec hT hi

/--
Testing recovery on a singleton feature distinct from row `i` bounds one
off-diagonal entry of `B^T A`.
-/
theorem offdiag_abs_lt_of_linearRecoveryCondition
    {m d k : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hk : 1 ≤ k) (hrec : linearRecoveryCondition A B k epsilon)
    {i j : Fin m} (hij : i ≠ j) :
    |inner (B i) (A j)| < epsilon := by
  exact
    offdiag_abs_lt_of_linearRecovery
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (k := k) (ε := epsilon) hk hrec hij

theorem geometry2_probe_columnNorm_pos
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : FeatureMatrix m d}
    (hk : 1 ≤ k) (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, columnNorm (A i) ≤ gamma)
    (i : Fin m) :
    0 < columnNorm (B i) := by
  let t : ℝ := 1 - epsilon
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have hdiag : t < inner (B i) (A i) := by
    simpa [t] using
      one_sub_epsilon_lt_diagonal_of_linearRecoveryCondition
        (A := A) (B := B) (k := k) (epsilon := epsilon) hk hrec i
  have hlower :
      t / gamma < columnNorm (B i) :=
    vectorNorm_lower_bound_of_inner_gt_of_vectorNorm_le
      (Coord := Fin d) (x := B i) (y := A i)
      (t := t) (gamma := gamma) ht hdiag (hAnorm i) hgamma
  exact lt_of_lt_of_le (div_pos ht hgamma) (le_of_lt hlower)

theorem geometry2_representation_columnNorm_pos
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : FeatureMatrix m d}
    (hk : 1 ≤ k) (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hBnorm : ∀ i : Fin m, columnNorm (B i) ≤ gamma)
    (i : Fin m) :
    0 < columnNorm (A i) := by
  let t : ℝ := 1 - epsilon
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have hdiag : t < inner (B i) (A i) := by
    simpa [t] using
      one_sub_epsilon_lt_diagonal_of_linearRecoveryCondition
        (A := A) (B := B) (k := k) (epsilon := epsilon) hk hrec i
  have hdiag_comm : t < inner (A i) (B i) := by
    simpa [inner_comm] using hdiag
  have hlower :
      t / gamma < columnNorm (A i) :=
    vectorNorm_lower_bound_of_inner_gt_of_vectorNorm_le
      (Coord := Fin d) (x := A i) (y := B i)
      (t := t) (gamma := gamma) ht hdiag_comm (hBnorm i) hgamma
  exact lt_of_lt_of_le (div_pos ht hgamma) (le_of_lt hlower)

/--
Geometry Proposition 2(i), finite deterministic form: if recovery works and
both representation and probe columns have norm at most `gamma`, then each
feature's normalized probe and representation directions are aligned by at
least `(1 - epsilon) / gamma^2`.
-/
theorem geometry2_self_columnCorrelation_lower
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : FeatureMatrix m d}
    (hk : 1 ≤ k) (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, columnNorm (A i) ≤ gamma)
    (hBnorm : ∀ i : Fin m, columnNorm (B i) ≤ gamma)
    (i : Fin m) :
    (1 - epsilon) / gamma ^ 2 < columnCorrelation (B i) (A i) := by
  let t : ℝ := 1 - epsilon
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have hdiag : t < inner (B i) (A i) := by
    simpa [t] using
      one_sub_epsilon_lt_diagonal_of_linearRecoveryCondition
        (A := A) (B := B) (k := k) (epsilon := epsilon) hk hrec i
  have hBpos : 0 < columnNorm (B i) := by
    have hlower :
        t / gamma < columnNorm (B i) :=
      vectorNorm_lower_bound_of_inner_gt_of_vectorNorm_le
        (Coord := Fin d) (x := B i) (y := A i)
        (t := t) (gamma := gamma) ht hdiag (hAnorm i) hgamma
    exact lt_of_lt_of_le (div_pos ht hgamma)
      (le_of_lt hlower)
  have hdiag_comm : t < inner (A i) (B i) := by
    have hcomm : inner (A i) (B i) = inner (B i) (A i) := by
      simp [AppliedModelingLib.Math.LinearCompressedSensing.inner, mul_comm]
    simpa [hcomm] using hdiag
  have hApos : 0 < columnNorm (A i) := by
    have hlower :
        t / gamma < columnNorm (A i) :=
      vectorNorm_lower_bound_of_inner_gt_of_vectorNorm_le
        (Coord := Fin d) (x := A i) (y := B i)
        (t := t) (gamma := gamma) ht hdiag_comm (hBnorm i) hgamma
    exact lt_of_lt_of_le (div_pos ht hgamma)
      (le_of_lt hlower)
  let denom : ℝ := columnNorm (B i) * columnNorm (A i)
  have hdenom_pos : 0 < denom := by
    dsimp [denom]
    exact mul_pos hBpos hApos
  have hgamma_sq_pos : 0 < gamma ^ 2 := sq_pos_of_ne_zero hgamma.ne'
  have hdenom_le : denom ≤ gamma ^ 2 := by
    dsimp [denom]
    have h :=
      mul_le_mul (hBnorm i) (hAnorm i)
        (vectorNorm_nonneg (A i)) (le_of_lt hgamma)
    simpa [pow_two] using h
  have hmul_lt : t * denom < inner (B i) (A i) * gamma ^ 2 := by
    have hleft : t * denom ≤ t * gamma ^ 2 :=
      mul_le_mul_of_nonneg_left hdenom_le ht.le
    have hright : t * gamma ^ 2 < inner (B i) (A i) * gamma ^ 2 :=
      mul_lt_mul_of_pos_right hdiag hgamma_sq_pos
    exact lt_of_le_of_lt hleft hright
  have hdiv : t / gamma ^ 2 < inner (B i) (A i) / denom := by
    field_simp [ne_of_gt hgamma_sq_pos, ne_of_gt hdenom_pos]
    nlinarith
  have hcorr :
      columnCorrelation (B i) (A i) = inner (B i) (A i) / denom := by
    dsimp [columnCorrelation, denom, columnNorm]
    rw [vectorCorrelation_eq_inv_mul_inv_mul_inner]
    field_simp [ne_of_gt hBpos, ne_of_gt hApos]
  rwa [hcorr]

/--
Geometry Proposition 2 cross-term bound, finite deterministic form.  The
normalization denominator is obtained from the diagonal recovery lower bounds
on both columns, giving the corrected factor `(1 - epsilon)^2`.
-/
theorem geometry2_cross_columnCorrelation_abs_lt
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : FeatureMatrix m d}
    (hk : 1 ≤ k) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, columnNorm (A i) ≤ gamma)
    (hBnorm : ∀ i : Fin m, columnNorm (B i) ≤ gamma)
    {i j : Fin m} (hij : i ≠ j) :
    |columnCorrelation (B i) (A j)| <
      epsilon * gamma ^ 2 / (1 - epsilon) ^ 2 := by
  let t : ℝ := 1 - epsilon
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have hdiag_i : t < inner (B i) (A i) := by
    simpa [t] using
      one_sub_epsilon_lt_diagonal_of_linearRecoveryCondition
        (A := A) (B := B) (k := k) (epsilon := epsilon) hk hrec i
  have hB_lower :
      t / gamma < columnNorm (B i) :=
    vectorNorm_lower_bound_of_inner_gt_of_vectorNorm_le
      (Coord := Fin d) (x := B i) (y := A i)
      (t := t) (gamma := gamma) ht hdiag_i (hAnorm i) hgamma
  have hBpos : 0 < columnNorm (B i) :=
    lt_of_lt_of_le (div_pos ht hgamma) (le_of_lt hB_lower)
  have hdiag_j : t < inner (B j) (A j) := by
    simpa [t] using
      one_sub_epsilon_lt_diagonal_of_linearRecoveryCondition
        (A := A) (B := B) (k := k) (epsilon := epsilon) hk hrec j
  have hdiag_j_comm : t < inner (A j) (B j) := by
    have hcomm : inner (A j) (B j) = inner (B j) (A j) := by
      simp [AppliedModelingLib.Math.LinearCompressedSensing.inner, mul_comm]
    simpa [hcomm] using hdiag_j
  have hA_lower :
      t / gamma < columnNorm (A j) :=
    vectorNorm_lower_bound_of_inner_gt_of_vectorNorm_le
      (Coord := Fin d) (x := A j) (y := B j)
      (t := t) (gamma := gamma) ht hdiag_j_comm (hBnorm j) hgamma
  have hApos : 0 < columnNorm (A j) :=
    lt_of_lt_of_le (div_pos ht hgamma) (le_of_lt hA_lower)
  have hinner_abs :
      |inner (B i) (A j)| < epsilon :=
    offdiag_abs_lt_of_linearRecoveryCondition
      (A := A) (B := B) (k := k) (epsilon := epsilon) hk hrec hij
  have hcorr_abs :
      |columnCorrelation (B i) (A j)| =
        (columnNorm (B i))⁻¹ * (columnNorm (A j))⁻¹ *
          |inner (B i) (A j)| := by
    dsimp [columnCorrelation, columnNorm]
    rw [vectorCorrelation_eq_inv_mul_inv_mul_inner]
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hBpos),
      abs_of_pos (inv_pos.mpr hApos)]
  have hcoef_pos :
      0 < (columnNorm (B i))⁻¹ * (columnNorm (A j))⁻¹ :=
    mul_pos (inv_pos.mpr hBpos) (inv_pos.mpr hApos)
  have hcoef_times :
      (columnNorm (B i))⁻¹ * (columnNorm (A j))⁻¹ *
          |inner (B i) (A j)| <
        (columnNorm (B i))⁻¹ * (columnNorm (A j))⁻¹ * epsilon :=
    mul_lt_mul_of_pos_left hinner_abs hcoef_pos
  have htgamma : 0 < t / gamma := div_pos ht hgamma
  have hinvB : (columnNorm (B i))⁻¹ < gamma / t := by
    have h :=
      (inv_lt_inv₀ hBpos htgamma).2 hB_lower
    have hinv_tgamma : (t / gamma)⁻¹ = gamma / t := by
      field_simp [ne_of_gt ht, ne_of_gt hgamma]
    simpa [hinv_tgamma] using h
  have hinvA : (columnNorm (A j))⁻¹ < gamma / t := by
    have h :=
      (inv_lt_inv₀ hApos htgamma).2 hA_lower
    have hinv_tgamma : (t / gamma)⁻¹ = gamma / t := by
      field_simp [ne_of_gt ht, ne_of_gt hgamma]
    simpa [hinv_tgamma] using h
  have hcoef_lt :
      (columnNorm (B i))⁻¹ * (columnNorm (A j))⁻¹ <
        (gamma / t) ^ 2 := by
    have hposA : 0 < (columnNorm (A j))⁻¹ := inv_pos.mpr hApos
    have hgamma_t_pos : 0 < gamma / t := div_pos hgamma ht
    have hmul :=
      mul_lt_mul_of_pos' hinvB hinvA hposA hgamma_t_pos
    simpa [pow_two] using hmul
  have hcoef_epsilon_lt :
      (columnNorm (B i))⁻¹ * (columnNorm (A j))⁻¹ * epsilon <
        epsilon * gamma ^ 2 / t ^ 2 := by
    calc
      (columnNorm (B i))⁻¹ * (columnNorm (A j))⁻¹ * epsilon <
          (gamma / t) ^ 2 * epsilon := by
        exact mul_lt_mul_of_pos_right hcoef_lt hepsilon_pos
      _ = epsilon * gamma ^ 2 / t ^ 2 := by
        field_simp [ne_of_gt ht]
  rw [hcorr_abs]
  exact lt_trans hcoef_times hcoef_epsilon_lt

/--
Geometry Proposition 2(ii), finite deterministic form with the corrected
cross-normalization factor `(1 - epsilon)^2`.
-/
theorem geometry2_representation_columnCorrelation_le
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : FeatureMatrix m d}
    (hk : 1 ≤ k) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, columnNorm (A i) ≤ gamma)
    (hBnorm : ∀ i : Fin m, columnNorm (B i) ≤ gamma)
    {i j : Fin m} (hij : i ≠ j) :
    columnCorrelation (A i) (A j) ≤
      epsilon * gamma ^ 2 / (1 - epsilon) ^ 2 +
        Real.sqrt (1 - ((1 - epsilon) / gamma ^ 2) ^ 2) := by
  let alpha : ℝ := (1 - epsilon) / gamma ^ 2
  let beta : ℝ := epsilon * gamma ^ 2 / (1 - epsilon) ^ 2
  have hAipos : 0 < columnNorm (A i) :=
    geometry2_representation_columnNorm_pos
      (A := A) (B := B) (k := k) (epsilon := epsilon)
      (gamma := gamma) hk hepsilon_lt_one hgamma hrec hBnorm i
  have hAjpos : 0 < columnNorm (A j) :=
    geometry2_representation_columnNorm_pos
      (A := A) (B := B) (k := k) (epsilon := epsilon)
      (gamma := gamma) hk hepsilon_lt_one hgamma hrec hBnorm j
  have hBipos : 0 < columnNorm (B i) :=
    geometry2_probe_columnNorm_pos
      (A := A) (B := B) (k := k) (epsilon := epsilon)
      (gamma := gamma) hk hepsilon_lt_one hgamma hrec hAnorm i
  have hAu : AppliedModelingLib.FiniteDimensionalNorms.l2 (normalizedColumn (A i)) = 1 := by
    simpa [columnNorm, normalizedColumn] using
      vectorNorm_normalizedVector_eq_one_of_pos
        (Coord := Fin d) (x := A i) hAipos
  have hAv : AppliedModelingLib.FiniteDimensionalNorms.l2 (normalizedColumn (A j)) = 1 := by
    simpa [columnNorm, normalizedColumn] using
      vectorNorm_normalizedVector_eq_one_of_pos
        (Coord := Fin d) (x := A j) hAjpos
  have hBw : AppliedModelingLib.FiniteDimensionalNorms.l2 (normalizedColumn (B i)) = 1 := by
    simpa [columnNorm, normalizedColumn] using
      vectorNorm_normalizedVector_eq_one_of_pos
        (Coord := Fin d) (x := B i) hBipos
  have hself_lt :
      alpha < columnCorrelation (A i) (B i) := by
    have h :=
      geometry2_self_columnCorrelation_lower
        (A := A) (B := B) (k := k) (epsilon := epsilon)
        (gamma := gamma) hk hepsilon_lt_one hgamma hrec hAnorm hBnorm i
    simpa [alpha, columnCorrelation_comm] using h
  have halpha :
      alpha ≤ AppliedModelingLib.FiniteDimensionalNorms.dot
        (normalizedColumn (A i)) (normalizedColumn (B i)) := by
    simpa [columnCorrelation_eq_dot_normalized] using (le_of_lt hself_lt)
  have hcross_lt :
      |columnCorrelation (A j) (B i)| < beta := by
    have h :=
      geometry2_cross_columnCorrelation_abs_lt
        (A := A) (B := B) (k := k) (epsilon := epsilon)
        (gamma := gamma) hk hepsilon_pos hepsilon_lt_one hgamma
        hrec hAnorm hBnorm hij
    simpa [beta, columnCorrelation_comm] using h
  have hcross :
      |AppliedModelingLib.FiniteDimensionalNorms.dot
        (normalizedColumn (A j)) (normalizedColumn (B i))| ≤ beta := by
    simpa [columnCorrelation_eq_dot_normalized] using (le_of_lt hcross_lt)
  have halpha_nonneg : 0 ≤ alpha := by
    dsimp [alpha]
    exact div_nonneg (by linarith) (sq_nonneg gamma)
  have h :=
    AppliedModelingLib.FiniteDimensionalNorms.dot_le_abs_cross_add_sqrt_one_sub_sq_of_l2_unit
      (u := normalizedColumn (A i)) (v := normalizedColumn (A j))
      (w := normalizedColumn (B i))
      (alpha := alpha) (beta := beta)
      hAu hAv hBw halpha halpha_nonneg hcross
  simpa [alpha, beta, columnCorrelation_eq_dot_normalized] using h

/--
Geometry Proposition 2(iii), finite deterministic form with the corrected
cross-normalization factor `(1 - epsilon)^2`.
-/
theorem geometry2_probe_columnCorrelation_le
    {m d k : ℕ} {epsilon gamma : ℝ} {A B : FeatureMatrix m d}
    (hk : 1 ≤ k) (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma)
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAnorm : ∀ i : Fin m, columnNorm (A i) ≤ gamma)
    (hBnorm : ∀ i : Fin m, columnNorm (B i) ≤ gamma)
    {i j : Fin m} (hij : i ≠ j) :
    columnCorrelation (B i) (B j) ≤
      epsilon * gamma ^ 2 / (1 - epsilon) ^ 2 +
        Real.sqrt (1 - ((1 - epsilon) / gamma ^ 2) ^ 2) := by
  let alpha : ℝ := (1 - epsilon) / gamma ^ 2
  let beta : ℝ := epsilon * gamma ^ 2 / (1 - epsilon) ^ 2
  have hBipos : 0 < columnNorm (B i) :=
    geometry2_probe_columnNorm_pos
      (A := A) (B := B) (k := k) (epsilon := epsilon)
      (gamma := gamma) hk hepsilon_lt_one hgamma hrec hAnorm i
  have hBjpos : 0 < columnNorm (B j) :=
    geometry2_probe_columnNorm_pos
      (A := A) (B := B) (k := k) (epsilon := epsilon)
      (gamma := gamma) hk hepsilon_lt_one hgamma hrec hAnorm j
  have hAipos : 0 < columnNorm (A i) :=
    geometry2_representation_columnNorm_pos
      (A := A) (B := B) (k := k) (epsilon := epsilon)
      (gamma := gamma) hk hepsilon_lt_one hgamma hrec hBnorm i
  have hBu : AppliedModelingLib.FiniteDimensionalNorms.l2 (normalizedColumn (B i)) = 1 := by
    simpa [columnNorm, normalizedColumn] using
      vectorNorm_normalizedVector_eq_one_of_pos
        (Coord := Fin d) (x := B i) hBipos
  have hBv : AppliedModelingLib.FiniteDimensionalNorms.l2 (normalizedColumn (B j)) = 1 := by
    simpa [columnNorm, normalizedColumn] using
      vectorNorm_normalizedVector_eq_one_of_pos
        (Coord := Fin d) (x := B j) hBjpos
  have hAw : AppliedModelingLib.FiniteDimensionalNorms.l2 (normalizedColumn (A i)) = 1 := by
    simpa [columnNorm, normalizedColumn] using
      vectorNorm_normalizedVector_eq_one_of_pos
        (Coord := Fin d) (x := A i) hAipos
  have hself_lt :
      alpha < columnCorrelation (B i) (A i) := by
    simpa [alpha] using
      geometry2_self_columnCorrelation_lower
        (A := A) (B := B) (k := k) (epsilon := epsilon)
        (gamma := gamma) hk hepsilon_lt_one hgamma hrec hAnorm hBnorm i
  have halpha :
      alpha ≤ AppliedModelingLib.FiniteDimensionalNorms.dot
        (normalizedColumn (B i)) (normalizedColumn (A i)) := by
    simpa [columnCorrelation_eq_dot_normalized] using (le_of_lt hself_lt)
  have hji : j ≠ i := fun h => hij h.symm
  have hcross_lt :
      |columnCorrelation (B j) (A i)| < beta := by
    have h :=
      geometry2_cross_columnCorrelation_abs_lt
        (A := A) (B := B) (k := k) (epsilon := epsilon)
        (gamma := gamma) hk hepsilon_pos hepsilon_lt_one hgamma
        hrec hAnorm hBnorm hji
    simpa [beta] using h
  have hcross :
      |AppliedModelingLib.FiniteDimensionalNorms.dot
        (normalizedColumn (B j)) (normalizedColumn (A i))| ≤ beta := by
    simpa [columnCorrelation_eq_dot_normalized] using (le_of_lt hcross_lt)
  have halpha_nonneg : 0 ≤ alpha := by
    dsimp [alpha]
    exact div_nonneg (by linarith) (sq_nonneg gamma)
  have h :=
    AppliedModelingLib.FiniteDimensionalNorms.dot_le_abs_cross_add_sqrt_one_sub_sq_of_l2_unit
      (u := normalizedColumn (B i)) (v := normalizedColumn (B j))
      (w := normalizedColumn (A i))
      (alpha := alpha) (beta := beta)
      hBu hBv hAw halpha halpha_nonneg hcross
  simpa [alpha, beta, columnCorrelation_eq_dot_normalized] using h

/--
Pigeonhole seam for the lower-bound proofs: if there are more than `m * q`
ordered large off-diagonal entries, then some probe row has more than `q` such
entries.
-/
theorem exists_largeInterferenceRow_card_gt_of_m_mul_lt_pairFinset_card
    {m d q : ℕ} {eta : ℝ} {A B : FeatureMatrix m d}
    (h : m * q < (largeInterferencePairFinset A B eta).card) :
    ∃ i : Fin m, q < (largeInterferenceRowFinset A B eta i).card := by
  have h' :
      Fintype.card (Fin m) * q < (largeOffdiagPairFinset A B eta).card := by
    simpa using h
  simpa [largeInterferencePairFinset, largeInterferenceRowFinset] using
    exists_largeOffdiagRow_card_gt_of_card_mul_lt_pairFinset_card
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (η := eta) (q := q) h'

/--
Source sign-pigeonhole step: a row with more than `2k` large interferences
contains `k` same-sign entries whose row sum has absolute value larger than
`k * eta`.
-/
theorem exists_finset_card_eq_abs_row_sum_gt_of_two_mul_lt_largeInterferenceRow_card
    {m d k : ℕ} {eta : ℝ} {A B : FeatureMatrix m d} {i : Fin m}
    (heta : 0 ≤ eta) (hk : 0 < k)
    (hrow : 2 * k < (largeInterferenceRowFinset A B eta i).card) :
    ∃ T : Finset (Fin m),
      T.card = k ∧ i ∉ T ∧ (k : ℝ) * eta < |∑ j ∈ T, inner (B i) (A j)| := by
  simpa [largeInterferenceRowFinset] using
    exists_finset_card_eq_abs_row_sum_gt_of_two_mul_lt_largeOffdiagRow_card
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (η := eta) (k := k) (i := i) heta hk hrow

/--
Source contradiction step: linear recovery cannot coexist with a row having
more than `2k` entries above threshold `eta` when `epsilon <= k * eta`.
-/
theorem false_of_linearRecoveryCondition_and_two_mul_lt_largeInterferenceRow_card
    {m d k : ℕ} {eta epsilon : ℝ} {A B : FeatureMatrix m d} {i : Fin m}
    (hrec : linearRecoveryCondition A B k epsilon)
    (heta : 0 ≤ eta) (hk : 0 < k) (hepsilon_le : epsilon ≤ (k : ℝ) * eta)
    (hrow : 2 * k < (largeInterferenceRowFinset A B eta i).card) :
    False := by
  exact
    false_of_linearRecovery_and_two_mul_lt_largeOffdiagRow_card
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (η := eta) (ε := epsilon) (k := k) (i := i)
      hrec heta hk hepsilon_le hrow

/--
Paper notation for the Turán step: if every `s`-feature set contains an edge
of the large-interference graph, then there are at least the corresponding
complement-Turán number of ordered large-interference entries.
-/
theorem largeInterferencePairFinset_card_ge_choose_sub_turanBound_of_every_subset_has_edge
    {m d s : ℕ} {eta : ℝ} {A B : FeatureMatrix m d}
    (hs : 0 < s)
    (hgraph : ∀ t : Finset (Fin m), t.card = s →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ (largeInterferenceGraph A B eta).Adj i j) :
    let r := s - 1
    m.choose 2 -
      ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2) ≤
        (largeInterferencePairFinset A B eta).card := by
  classical
  have h :
      let n := Fintype.card (Fin m)
      let r := s - 1
      n.choose 2 -
        ((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2) ≤
          (largeOffdiagPairFinset A B eta).card :=
    largeOffdiagPairFinset_card_ge_choose_sub_turanBound_of_forall_finset_exists_graph_adj
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (η := eta) hs hgraph
  simpa [largeInterferencePairFinset] using h

/--
Paper notation for the Turán-plus-pigeonhole step: if the complement-Turán
lower bound beats `m * q`, then one row of `B^T A` has more than `q` large
off-diagonal entries.
-/
theorem exists_largeInterferenceRow_card_gt_of_m_mul_lt_turanBound_of_every_subset_has_edge
    {m d s q : ℕ} {eta : ℝ} {A B : FeatureMatrix m d}
    (hs : 0 < s)
    (hgraph : ∀ t : Finset (Fin m), t.card = s →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ (largeInterferenceGraph A B eta).Adj i j)
    (havg :
      m * q <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    ∃ i : Fin m, q < (largeInterferenceRowFinset A B eta i).card := by
  classical
  have havg' :
      Fintype.card (Fin m) * q <
        (let n := Fintype.card (Fin m)
         let r := s - 1
         n.choose 2 -
          ((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2)) := by
    simpa using havg
  simpa [largeInterferenceRowFinset] using
    exists_largeOffdiagRow_card_gt_of_card_mul_lt_turanBound_of_forall_finset_exists_graph_adj
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (η := eta) (s := s) (q := q) hs hgraph havg'

/--
Paper-facing lower-bound bridge after the Alon/rank step: once every
`s`-feature set contains a large-interference edge and the Turán lower bound
forces more than `m * 2k` directed large entries, linear recovery is
contradictory.
-/
theorem false_of_linearRecoveryCondition_and_turan_every_subset_has_edge
    {m d s k : ℕ} {eta epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (heta : 0 ≤ eta) (hk : 0 < k) (hepsilon_le : epsilon ≤ (k : ℝ) * eta)
    (hs : 0 < s)
    (hgraph : ∀ t : Finset (Fin m), t.card = s →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ (largeInterferenceGraph A B eta).Adj i j)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  classical
  have havg' :
      Fintype.card (Fin m) * (2 * k) <
        (let n := Fintype.card (Fin m)
         let r := s - 1
         n.choose 2 -
          ((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2)) := by
    simpa using havg
  exact
    false_of_linearRecovery_and_card_mul_two_mul_lt_turanBound_of_forall_finset_exists_graph_adj
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (η := eta) (ε := epsilon) (s := s) (k := k)
      hrec heta hk hepsilon_le hs hgraph havg'

/--
Paper-facing bridge in the natural output form of the Alon/rank corollary:
each `s`-feature principal submatrix has a large off-diagonal entry.
-/
theorem every_subset_has_largeInterference_edge_of_every_principalSubmatrix_has_largeOffdiag
    {m d s : ℕ} {eta : ℝ} {A B : FeatureMatrix m d}
    (hoffdiag : ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y|) :
    ∀ t : Finset (Fin m), t.card = s →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ (largeInterferenceGraph A B eta).Adj i j := by
  have hoffdiag' : ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((crossInnerMatrix A B).submatrix Subtype.val Subtype.val) x y| := by
    simpa [interferenceMatrix] using hoffdiag
  exact
    forall_finset_exists_largeOffdiagGraph_adj_of_forall_principalSubmatrix_exists_largeOffdiag
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (η := eta) (s := s) hoffdiag'

/--
Alon-rank bridge for the lower-bound proof: once the scaled Alon rank theorem
is available, any principal submatrix whose rank is below the Alon lower bound
contains a large off-diagonal entry.
-/
theorem every_principalSubmatrix_has_largeOffdiag_of_alonScaledRankBound
    {m d s : ℕ} {gamma eta c : ℝ} {A B : FeatureMatrix m d}
    (hAlon : ∀ t : Finset (Fin m), t.card = s →
      ∀ (D : Matrix {j // j ∈ t} {j // j ∈ t} ℝ) {γ η : ℝ},
        0 < γ →
        γ ≤ 1 →
        γ / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < η →
        η < γ / 2 →
        (∀ i, γ ≤ D i i) →
        (∀ ⦃i j⦄, i ≠ j → |D i j| ≤ η) →
        alonScaledRankBound (Fintype.card {j // j ∈ t}) γ η c ≤ (D.rank : ℝ))
    (hgamma_pos : 0 < gamma)
    (hgamma_le_one : gamma ≤ 1)
    (heta_low : ∀ t : Finset (Fin m), t.card = s →
      gamma / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < eta)
    (heta_high : eta < gamma / 2)
    (hdiag : ∀ i : Fin m, gamma ≤ inner (B i) (A i))
    (hrank : ∀ t : Finset (Fin m), t.card = s →
      (((interferenceMatrix A B).submatrix Subtype.val Subtype.val :
          Matrix {j // j ∈ t} {j // j ∈ t} ℝ).rank : ℝ) <
        alonScaledRankBound (Fintype.card {j // j ∈ t}) gamma eta c) :
    ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y| := by
  classical
  intro t ht
  let C : Matrix {j // j ∈ t} {j // j ∈ t} ℝ :=
    (interferenceMatrix A B).submatrix Subtype.val Subtype.val
  have hdiagC : ∀ i : {j // j ∈ t}, gamma ≤ C i i := by
    intro i
    exact hdiag i.1
  have hoff :=
    exists_offdiag_gt_of_rank_lt_alonScaledRankBound
      (ι := {j // j ∈ t}) (c := c) (hAlon t ht) C
      hgamma_pos hgamma_le_one (heta_low t ht) heta_high hdiagC (hrank t ht)
  simpa [C]
    using hoff

/--
Alon-rank bridge using the normalized diagonal-one theorem directly.  This
packages the row-scaling corollary in the shared rank library, so LRH does not
need a separate scaled-Alon certificate.
-/
theorem every_principalSubmatrix_has_largeOffdiag_of_alonNormalizedRankBound
    {m d s : ℕ} {gamma eta c : ℝ} {A B : FeatureMatrix m d}
    (hAlon : ∀ t : Finset (Fin m), t.card = s →
      ∀ (D : Matrix {j // j ∈ t} {j // j ∈ t} ℝ) {epsilon : ℝ},
        1 / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < epsilon →
        epsilon < 1 / 2 →
        (∀ i, D i i = 1) →
        (∀ ⦃i j⦄, i ≠ j → |D i j| ≤ epsilon) →
        alonNormalizedRankBound (Fintype.card {j // j ∈ t}) epsilon c ≤ (D.rank : ℝ))
    (hgamma_pos : 0 < gamma)
    (heta_low : ∀ t : Finset (Fin m), t.card = s →
      gamma / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < eta)
    (heta_high : eta < gamma / 2)
    (hdiag : ∀ i : Fin m, gamma ≤ inner (B i) (A i))
    (hrank : ∀ t : Finset (Fin m), t.card = s →
      (((interferenceMatrix A B).submatrix Subtype.val Subtype.val :
          Matrix {j // j ∈ t} {j // j ∈ t} ℝ).rank : ℝ) <
        alonScaledRankBound (Fintype.card {j // j ∈ t}) gamma eta c) :
    ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y| := by
  classical
  intro t ht
  let C : Matrix {j // j ∈ t} {j // j ∈ t} ℝ :=
    (interferenceMatrix A B).submatrix Subtype.val Subtype.val
  have hdiagC : ∀ i : {j // j ∈ t}, gamma ≤ C i i := by
    intro i
    exact hdiag i.1
  have hoff :=
    exists_offdiag_gt_of_rank_lt_scaledRankBound_of_normalized
      (ι := {j // j ∈ t}) (c := c)
      (hnormalized := hAlon t ht)
      C hgamma_pos (heta_low t ht) heta_high hdiagC (hrank t ht)
  simpa [C] using hoff

/--
Polynomial-method bridge for the normalized threshold setting: if every
`s`-feature principal symmetrized interference matrix has too few symmetric
monomial coordinates for degree `power`, then each such feature set contains a
large directed interference entry.
-/
theorem every_principalSubmatrix_has_largeOffdiag_of_symmetricPower_obstruction
    {m d s power : ℕ} {eta : ℝ} {A B : FeatureMatrix m d}
    (hdiag : ∀ i : Fin m, inner (B i) (A i) = 1)
    (heta_nonneg : 0 ≤ eta)
    (hsmall : ∀ t : Finset (Fin m), t.card = s →
      (Fintype.card {j // j ∈ t} : ℝ) * eta ^ (2 * power) ≤ 1)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      2 * (Fintype.card (Sym (Sum (Fin d) (Fin d)) power) : ℝ) <
        (Fintype.card {j // j ∈ t} : ℝ)) :
    ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y| := by
  classical
  intro t ht
  let H : Matrix {j // j ∈ t} {j // j ∈ t} ℝ :=
    (symmetrizedInterferenceMatrix A B).submatrix Subtype.val Subtype.val
  have hH_factor :
      ∀ x y : {j // j ∈ t},
        H x y =
          ∑ r : Sum (Fin d) (Fin d),
            (match r with
              | Sum.inl a => B x.1 a / 2
              | Sum.inr a => A x.1 a / 2) *
            (match r with
              | Sum.inl a => A y.1 a
              | Sum.inr a => B y.1 a) := by
    simpa [H] using
      symmetrizedInterferenceMatrix_submatrix_dot_factorization A B t
  have hH_sym : ∀ x y : {j // j ∈ t}, H x y = H y x := by
    intro x y
    simpa [H] using symmetrizedInterferenceMatrix_symmetric A B x.1 y.1
  have hH_diag : ∀ x : {j // j ∈ t}, H x x = 1 := by
    intro x
    simpa [H] using
      symmetrizedInterferenceMatrix_diag_eq (A := A) (B := B) hdiag x.1
  obtain ⟨x, y, hxy, hlargeH⟩ :=
    exists_offdiag_gt_of_symmetric_dot_factorization_diag_one
      (M := H)
      (X := fun x r =>
        match r with
        | Sum.inl a => B x.1 a / 2
        | Sum.inr a => A x.1 a / 2)
      (Y := fun y r =>
        match r with
        | Sum.inl a => A y.1 a
        | Sum.inr a => B y.1 a)
      hH_factor hH_sym hH_diag heta_nonneg power (hsmall t ht) (hdim t ht)
  let C : Matrix {j // j ∈ t} {j // j ∈ t} ℝ :=
    (interferenceMatrix A B).submatrix Subtype.val Subtype.val
  have hH_eq : H x y = (C x y + C y x) / 2 := by
    simp [H, C, symmetrizedInterferenceMatrix, interferenceMatrix]
  by_cases hdir : eta < |C x y|
  · exact ⟨x, y, hxy, by simpa [C] using hdir⟩
  · have hrev : eta < |C y x| := by
      by_contra hnot_rev
      have hxy_le : |C x y| ≤ eta := le_of_not_gt hdir
      have hyx_le : |C y x| ≤ eta := le_of_not_gt hnot_rev
      have havg_le : |(C x y + C y x) / 2| ≤ eta := by
        calc
          |(C x y + C y x) / 2|
              = |C x y + C y x| / 2 := by norm_num [abs_div]
          _ ≤ (|C x y| + |C y x|) / 2 := by
              exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
          _ ≤ (eta + eta) / 2 := by
              exact div_le_div_of_nonneg_right
                (add_le_add hxy_le hyx_le) (by norm_num)
          _ = eta := by ring
      exact not_lt_of_ge (by simpa [hH_eq] using havg_le) hlargeH
    exact ⟨y, x, hxy.symm, by simpa [C] using hrev⟩

/--
Polynomial-method bridge with diagonal lower and upper bounds.  This is the
finite replacement for the scaled Alon-rank step in the linear lower-bound
proof, specialized to the symmetrized interference matrix.
-/
theorem every_principalSubmatrix_has_largeOffdiag_of_symmetricPower_diag_bounds_obstruction
    {m d s power : ℕ} {gamma beta eta : ℝ} {A B : FeatureMatrix m d}
    (hgamma_nonneg : 0 ≤ gamma) (hbeta_nonneg : 0 ≤ beta)
    (hdiag_lower : ∀ i : Fin m, gamma ≤ inner (B i) (A i))
    (hdiag_abs_upper : ∀ i : Fin m, |inner (B i) (A i)| ≤ beta)
    (heta_nonneg : 0 ≤ eta)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (Fintype.card (Sym (Sum (Fin d) (Fin d)) power) : ℝ) *
          ((Fintype.card {j // j ∈ t} : ℝ) * beta ^ (2 * power) +
            (Fintype.card {j // j ∈ t} : ℝ) *
              (Fintype.card {j // j ∈ t} : ℝ) * eta ^ (2 * power)) <
        (Fintype.card {j // j ∈ t} : ℝ) ^ 2 * gamma ^ (2 * power)) :
    ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y| := by
  classical
  intro t ht
  let H : Matrix {j // j ∈ t} {j // j ∈ t} ℝ :=
    (symmetrizedInterferenceMatrix A B).submatrix Subtype.val Subtype.val
  have hH_factor :
      ∀ x y : {j // j ∈ t},
        H x y =
          ∑ r : Sum (Fin d) (Fin d),
            (match r with
              | Sum.inl a => B x.1 a / 2
              | Sum.inr a => A x.1 a / 2) *
            (match r with
              | Sum.inl a => A y.1 a
              | Sum.inr a => B y.1 a) := by
    simpa [H] using
      symmetrizedInterferenceMatrix_submatrix_dot_factorization A B t
  have hH_sym : ∀ x y : {j // j ∈ t}, H x y = H y x := by
    intro x y
    simpa [H] using symmetrizedInterferenceMatrix_symmetric A B x.1 y.1
  have hH_diag_lower : ∀ x : {j // j ∈ t}, gamma ≤ H x x := by
    intro x
    simpa [H, symmetrizedInterferenceMatrix] using hdiag_lower x.1
  have hH_diag_abs_upper : ∀ x : {j // j ∈ t}, |H x x| ≤ beta := by
    intro x
    simpa [H, symmetrizedInterferenceMatrix] using hdiag_abs_upper x.1
  obtain ⟨x, y, hxy, hlargeH⟩ :=
    exists_offdiag_gt_of_symmetric_dot_factorization_diag_bounds
      (M := H)
      (X := fun x r =>
        match r with
        | Sum.inl a => B x.1 a / 2
        | Sum.inr a => A x.1 a / 2)
      (Y := fun y r =>
        match r with
        | Sum.inl a => A y.1 a
        | Sum.inr a => B y.1 a)
      hH_factor hH_sym hgamma_nonneg hbeta_nonneg
      hH_diag_lower hH_diag_abs_upper heta_nonneg power (hdim t ht)
  let C : Matrix {j // j ∈ t} {j // j ∈ t} ℝ :=
    (interferenceMatrix A B).submatrix Subtype.val Subtype.val
  have hH_eq : H x y = (C x y + C y x) / 2 := by
    simp [H, C, symmetrizedInterferenceMatrix, interferenceMatrix]
  by_cases hdir : eta < |C x y|
  · exact ⟨x, y, hxy, by simpa [C] using hdir⟩
  · have hrev : eta < |C y x| := by
      by_contra hnot_rev
      have hxy_le : |C x y| ≤ eta := le_of_not_gt hdir
      have hyx_le : |C y x| ≤ eta := le_of_not_gt hnot_rev
      have havg_le : |(C x y + C y x) / 2| ≤ eta := by
        calc
          |(C x y + C y x) / 2|
              = |C x y + C y x| / 2 := by norm_num [abs_div]
          _ ≤ (|C x y| + |C y x|) / 2 := by
              exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
          _ ≤ (eta + eta) / 2 := by
              exact div_le_div_of_nonneg_right
                (add_le_add hxy_le hyx_le) (by norm_num)
          _ = eta := by ring
      exact not_lt_of_ge (by simpa [hH_eq] using havg_le) hlargeH
    exact ⟨y, x, hxy.symm, by simpa [C] using hrev⟩

/--
Paper-facing lower-bound bridge after the Alon/rank step, stated directly in
principal-submatrix language.
-/
theorem false_of_linearRecoveryCondition_and_turan_principalSubmatrix_largeOffdiag
    {m d s k : ℕ} {eta epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (heta : 0 ≤ eta) (hk : 0 < k) (hepsilon_le : epsilon ≤ (k : ℝ) * eta)
    (hs : 0 < s)
    (hoffdiag : ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y|)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  classical
  have havg' :
      Fintype.card (Fin m) * (2 * k) <
        (let n := Fintype.card (Fin m)
         let r := s - 1
         n.choose 2 -
          ((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2)) := by
    simpa using havg
  have hoffdiag' : ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((crossInnerMatrix A B).submatrix Subtype.val Subtype.val) x y| := by
    simpa [interferenceMatrix] using hoffdiag
  exact
    false_of_linearRecovery_and_card_mul_two_mul_lt_turanBound_of_forall_principalSubmatrix_exists_largeOffdiag
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (η := eta) (ε := epsilon) (s := s) (k := k)
      hrec heta hk hepsilon_le hs hoffdiag' havg'

/--
Paper-facing bridge in the natural output form of the rank obstruction, using
the source's coarse Turán estimate `m^2/(2r) - m/2` instead of the exact
complement-Turán expression.
-/
theorem false_of_linearRecoveryCondition_and_coarse_turan_principalSubmatrix_largeOffdiag
    {m d s k : ℕ} {eta epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (heta : 0 ≤ eta) (hk : 0 < k) (hepsilon_le : epsilon ≤ (k : ℝ) * eta)
    (hs : 1 < s)
    (hoffdiag : ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y|)
    (havg :
      (m : ℝ) * ((2 * k : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False := by
  classical
  have hoffdiag' : ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((crossInnerMatrix A B).submatrix Subtype.val Subtype.val) x y| := by
    simpa [interferenceMatrix] using hoffdiag
  have havg' :
      let n := Fintype.card (Fin m)
      let r := s - 1
      (n : ℝ) * ((2 * k : ℕ) : ℝ) <
        (n : ℝ) ^ 2 / (2 * (r : ℝ)) - (n : ℝ) / 2 := by
    simpa using havg
  exact
    false_of_linearRecovery_and_real_card_mul_two_mul_lt_coarse_turan_of_forall_principalSubmatrix_exists_largeOffdiag
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (η := eta) (ε := epsilon) (s := s) (k := k)
      hrec heta hk hepsilon_le hs hoffdiag' havg'

/--
Finite lower-bound closeout using the explicit symmetric-power polynomial
obstruction in place of the scaled Alon rank theorem.
-/
theorem false_of_linearRecoveryCondition_and_symmetricPower_dimension_turan
    {m d s k power : ℕ} {gamma beta eta epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hgamma_nonneg : 0 ≤ gamma) (hbeta_nonneg : 0 ≤ beta)
    (hdiag_lower : ∀ i : Fin m, gamma ≤ inner (B i) (A i))
    (hdiag_abs_upper : ∀ i : Fin m, |inner (B i) (A i)| ≤ beta)
    (heta : 0 ≤ eta)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (Fintype.card (Sym (Sum (Fin d) (Fin d)) power) : ℝ) *
          ((Fintype.card {j // j ∈ t} : ℝ) * beta ^ (2 * power) +
            (Fintype.card {j // j ∈ t} : ℝ) *
              (Fintype.card {j // j ∈ t} : ℝ) * eta ^ (2 * power)) <
        (Fintype.card {j // j ∈ t} : ℝ) ^ 2 * gamma ^ (2 * power))
    (hk : 0 < k) (hepsilon_le : epsilon ≤ (k : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  classical
  have hprincipal :
      ∀ t : Finset (Fin m), t.card = s →
        ∃ x y : {j // j ∈ t},
          x ≠ y ∧
            eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y| :=
    every_principalSubmatrix_has_largeOffdiag_of_symmetricPower_diag_bounds_obstruction
      (A := A) (B := B) hgamma_nonneg hbeta_nonneg
      hdiag_lower hdiag_abs_upper heta hdim
  exact
    false_of_linearRecoveryCondition_and_turan_principalSubmatrix_largeOffdiag
      (A := A) (B := B) (eta := eta) (epsilon := epsilon)
      (s := s) (k := k) hrec heta hk hepsilon_le hs hprincipal havg

/--
Finite lower-bound closeout using the explicit symmetric-power polynomial
obstruction and the source's coarse Turán estimate.
-/
theorem false_of_linearRecoveryCondition_and_symmetricPower_dimension_coarse_turan
    {m d s k power : ℕ} {gamma beta eta epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hgamma_nonneg : 0 ≤ gamma) (hbeta_nonneg : 0 ≤ beta)
    (hdiag_lower : ∀ i : Fin m, gamma ≤ inner (B i) (A i))
    (hdiag_abs_upper : ∀ i : Fin m, |inner (B i) (A i)| ≤ beta)
    (heta : 0 ≤ eta)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (Fintype.card (Sym (Sum (Fin d) (Fin d)) power) : ℝ) *
          ((Fintype.card {j // j ∈ t} : ℝ) * beta ^ (2 * power) +
            (Fintype.card {j // j ∈ t} : ℝ) *
              (Fintype.card {j // j ∈ t} : ℝ) * eta ^ (2 * power)) <
        (Fintype.card {j // j ∈ t} : ℝ) ^ 2 * gamma ^ (2 * power))
    (hk : 0 < k) (hepsilon_le : epsilon ≤ (k : ℝ) * eta)
    (hs : 1 < s)
    (havg :
      (m : ℝ) * ((2 * k : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False := by
  classical
  have hprincipal :
      ∀ t : Finset (Fin m), t.card = s →
        ∃ x y : {j // j ∈ t},
          x ≠ y ∧
            eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y| :=
    every_principalSubmatrix_has_largeOffdiag_of_symmetricPower_diag_bounds_obstruction
      (A := A) (B := B) hgamma_nonneg hbeta_nonneg
      hdiag_lower hdiag_abs_upper heta hdim
  exact
    false_of_linearRecoveryCondition_and_coarse_turan_principalSubmatrix_largeOffdiag
      (A := A) (B := B) (eta := eta) (epsilon := epsilon)
      (s := s) (k := k) hrec heta hk hepsilon_le hs hprincipal havg

/--
Finite lower-bound closeout bridge: normalized Alon, the rank observation
`rank(B^T A)_R <= d`, Turán, and the row-sum contradiction together rule out
linear recovery under the displayed finite inequalities.
-/
theorem false_of_linearRecoveryCondition_and_alonNormalizedRankBound_dimension_turan
    {m d s k : ℕ} {gamma eta epsilon c : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hAlon : ∀ t : Finset (Fin m), t.card = s →
      ∀ (D : Matrix {j // j ∈ t} {j // j ∈ t} ℝ) {epsilon : ℝ},
        1 / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < epsilon →
        epsilon < 1 / 2 →
        (∀ i, D i i = 1) →
        (∀ ⦃i j⦄, i ≠ j → |D i j| ≤ epsilon) →
        alonNormalizedRankBound (Fintype.card {j // j ∈ t}) epsilon c ≤ (D.rank : ℝ))
    (hgamma_pos : 0 < gamma)
    (heta_low : ∀ t : Finset (Fin m), t.card = s →
      gamma / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < eta)
    (heta_high : eta < gamma / 2)
    (hdiag : ∀ i : Fin m, gamma ≤ inner (B i) (A i))
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (d : ℝ) < alonScaledRankBound (Fintype.card {j // j ∈ t}) gamma eta c)
    (heta : 0 ≤ eta) (hk : 0 < k) (hepsilon_le : epsilon ≤ (k : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  classical
  have hprincipal :
      ∀ t : Finset (Fin m), t.card = s →
        ∃ x y : {j // j ∈ t},
          x ≠ y ∧
            eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y| :=
    every_principalSubmatrix_has_largeOffdiag_of_alonNormalizedRankBound
      (A := A) (B := B) (c := c) hAlon hgamma_pos heta_low heta_high hdiag
      (hrank := by
        intro t ht
        have hle_nat :
            (((interferenceMatrix A B).submatrix Subtype.val Subtype.val :
                Matrix {j // j ∈ t} {j // j ∈ t} ℝ).rank) ≤ d :=
          interferenceMatrix_principalSubmatrix_rank_le_d
            (A := A) (B := B)
            (select := (Subtype.val : {j // j ∈ t} → Fin m))
        have hle_real :
            (((interferenceMatrix A B).submatrix Subtype.val Subtype.val :
                Matrix {j // j ∈ t} {j // j ∈ t} ℝ).rank : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast hle_nat
        exact lt_of_le_of_lt hle_real (hdim t ht))
  exact
    false_of_linearRecoveryCondition_and_turan_principalSubmatrix_largeOffdiag
      (A := A) (B := B) (eta := eta) (epsilon := epsilon)
      (s := s) (k := k) hrec heta hk hepsilon_le hs hprincipal havg

/--
Finite lower-bound closeout with the source parameter substitution
`gamma = 1 - epsilon` and `eta = epsilon / k`.  The diagonal lower bound is
derived from linear recovery on singleton feature vectors.
-/
theorem false_of_linearRecoveryCondition_and_alonNormalizedRankBound_source_parameters
    {m d s k : ℕ} {epsilon c : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hAlon : ∀ t : Finset (Fin m), t.card = s →
      ∀ (D : Matrix {j // j ∈ t} {j // j ∈ t} ℝ) {epsilon : ℝ},
        1 / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < epsilon →
        epsilon < 1 / 2 →
        (∀ i, D i i = 1) →
        (∀ ⦃i j⦄, i ≠ j → |D i j| ≤ epsilon) →
        alonNormalizedRankBound (Fintype.card {j // j ∈ t}) epsilon c ≤ (D.rank : ℝ))
    (heta_low : ∀ t : Finset (Fin m), t.card = s →
      (1 - epsilon) / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) <
        epsilon / (k : ℝ))
    (heta_high : epsilon / (k : ℝ) < (1 - epsilon) / 2)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (d : ℝ) <
        alonScaledRankBound (Fintype.card {j // j ∈ t})
          (1 - epsilon) (epsilon / (k : ℝ)) c)
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hk_one : 1 ≤ k := Nat.succ_le_of_lt hk
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hgamma_pos : 0 < 1 - epsilon := by linarith
  have hdiag : ∀ i : Fin m, 1 - epsilon ≤ inner (B i) (A i) := by
    intro i
    exact le_of_lt
      (one_sub_epsilon_lt_diagonal_of_linearRecoveryCondition
        (A := A) (B := B) (k := k) (epsilon := epsilon)
        hk_one hrec i)
  have heta_nonneg : 0 ≤ epsilon / (k : ℝ) :=
    div_nonneg hepsilon_nonneg hk_real_pos.le
  have hepsilon_le : epsilon ≤ (k : ℝ) * (epsilon / (k : ℝ)) := by
    field_simp [ne_of_gt hk_real_pos]
    exact le_rfl
  exact
    false_of_linearRecoveryCondition_and_alonNormalizedRankBound_dimension_turan
      (A := A) (B := B) (gamma := 1 - epsilon)
      (eta := epsilon / (k : ℝ)) (epsilon := epsilon) (c := c)
      (s := s) (k := k)
      hrec hAlon hgamma_pos heta_low heta_high hdiag hdim
      heta_nonneg hk hepsilon_le hs havg

/--
Finite lower-bound closeout with the source parameter substitution, using the
explicit symmetric-power obstruction rather than an external Alon theorem.
-/
theorem false_of_linearRecoveryCondition_and_symmetricPower_source_parameters
    {m d s k power : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (Fintype.card (Sym (Sum (Fin d) (Fin d)) power) : ℝ) *
          ((Fintype.card {j // j ∈ t} : ℝ) * (1 + epsilon) ^ (2 * power) +
            (Fintype.card {j // j ∈ t} : ℝ) *
              (Fintype.card {j // j ∈ t} : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (Fintype.card {j // j ∈ t} : ℝ) ^ 2 *
          (1 - epsilon) ^ (2 * power))
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hk_one : 1 ≤ k := Nat.succ_le_of_lt hk
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hgamma_nonneg : 0 ≤ 1 - epsilon := by linarith
  have hbeta_nonneg : 0 ≤ 1 + epsilon := by linarith
  have hdiag_lower : ∀ i : Fin m, 1 - epsilon ≤ inner (B i) (A i) := by
    intro i
    exact le_of_lt
      (one_sub_epsilon_lt_diagonal_of_linearRecoveryCondition
        (A := A) (B := B) (k := k) (epsilon := epsilon)
        hk_one hrec i)
  have hdiag_abs_upper : ∀ i : Fin m, |inner (B i) (A i)| ≤ 1 + epsilon := by
    intro i
    have hclose :
        |inner (B i) (A i) - 1| < epsilon :=
      diagonal_abs_sub_one_lt_of_linearRecoveryCondition
        (A := A) (B := B) (k := k) (epsilon := epsilon)
        hk_one hrec i
    have htri :
        |inner (B i) (A i)| ≤ |inner (B i) (A i) - 1| + 1 := by
      calc
        |inner (B i) (A i)|
            = |(inner (B i) (A i) - 1) + 1| := by ring_nf
        _ ≤ |inner (B i) (A i) - 1| + |(1 : ℝ)| := abs_add_le _ _
        _ = |inner (B i) (A i) - 1| + 1 := by simp
    have hlt : |inner (B i) (A i)| < epsilon + 1 := by
      linarith [htri, hclose]
    linarith
  have heta_nonneg : 0 ≤ epsilon / (k : ℝ) :=
    div_nonneg hepsilon_nonneg hk_real_pos.le
  have hepsilon_le : epsilon ≤ (k : ℝ) * (epsilon / (k : ℝ)) := by
    field_simp [ne_of_gt hk_real_pos]
    exact le_rfl
  exact
    false_of_linearRecoveryCondition_and_symmetricPower_dimension_turan
      (A := A) (B := B) (gamma := 1 - epsilon)
      (beta := 1 + epsilon) (eta := epsilon / (k : ℝ))
      (epsilon := epsilon) (s := s) (k := k) (power := power)
      hrec hgamma_nonneg hbeta_nonneg hdiag_lower hdiag_abs_upper
      heta_nonneg hdim hk hepsilon_le hs havg

/--
Finite lower-bound closeout with the source parameter substitution, using the
source's coarse Turán average estimate.
-/
theorem false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_coarse_turan
    {m d s k power : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (Fintype.card (Sym (Sum (Fin d) (Fin d)) power) : ℝ) *
          ((Fintype.card {j // j ∈ t} : ℝ) * (1 + epsilon) ^ (2 * power) +
            (Fintype.card {j // j ∈ t} : ℝ) *
              (Fintype.card {j // j ∈ t} : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (Fintype.card {j // j ∈ t} : ℝ) ^ 2 *
          (1 - epsilon) ^ (2 * power))
    (hs : 1 < s)
    (havg :
      (m : ℝ) * ((2 * k : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False := by
  have hk_one : 1 ≤ k := Nat.succ_le_of_lt hk
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hgamma_nonneg : 0 ≤ 1 - epsilon := by linarith
  have hbeta_nonneg : 0 ≤ 1 + epsilon := by linarith
  have hdiag_lower : ∀ i : Fin m, 1 - epsilon ≤ inner (B i) (A i) := by
    intro i
    exact le_of_lt
      (one_sub_epsilon_lt_diagonal_of_linearRecoveryCondition
        (A := A) (B := B) (k := k) (epsilon := epsilon)
        hk_one hrec i)
  have hdiag_abs_upper : ∀ i : Fin m, |inner (B i) (A i)| ≤ 1 + epsilon := by
    intro i
    have hclose :
        |inner (B i) (A i) - 1| < epsilon :=
      diagonal_abs_sub_one_lt_of_linearRecoveryCondition
        (A := A) (B := B) (k := k) (epsilon := epsilon)
        hk_one hrec i
    have htri :
        |inner (B i) (A i)| ≤ |inner (B i) (A i) - 1| + 1 := by
      calc
        |inner (B i) (A i)|
            = |(inner (B i) (A i) - 1) + 1| := by ring_nf
        _ ≤ |inner (B i) (A i) - 1| + |(1 : ℝ)| := abs_add_le _ _
        _ = |inner (B i) (A i) - 1| + 1 := by simp
    have hlt : |inner (B i) (A i)| < epsilon + 1 := by
      linarith [htri, hclose]
    linarith
  have heta_nonneg : 0 ≤ epsilon / (k : ℝ) :=
    div_nonneg hepsilon_nonneg hk_real_pos.le
  have hepsilon_le : epsilon ≤ (k : ℝ) * (epsilon / (k : ℝ)) := by
    field_simp [ne_of_gt hk_real_pos]
    exact le_rfl
  exact
    false_of_linearRecoveryCondition_and_symmetricPower_dimension_coarse_turan
      (A := A) (B := B) (gamma := 1 - epsilon)
      (beta := 1 + epsilon) (eta := epsilon / (k : ℝ))
      (epsilon := epsilon) (s := s) (k := k) (power := power)
      hrec hgamma_nonneg hbeta_nonneg hdiag_lower hdiag_abs_upper
      heta_nonneg hdim hk hepsilon_le hs havg

/--
Source-parameter finite closeout with the symmetric-power coordinate count
written by stars-and-bars as `choose (2d + power - 1) power`.
-/
theorem false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_choose
    {m d s k power : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      ((2 * d + power - 1).choose power : ℝ) *
          ((Fintype.card {j // j ∈ t} : ℝ) * (1 + epsilon) ^ (2 * power) +
            (Fintype.card {j // j ∈ t} : ℝ) *
              (Fintype.card {j // j ∈ t} : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (Fintype.card {j // j ∈ t} : ℝ) ^ 2 *
          (1 - epsilon) ^ (2 * power))
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False :=
  false_of_linearRecoveryCondition_and_symmetricPower_source_parameters
    (A := A) (B := B) (s := s) (k := k) (power := power)
    hrec hk hepsilon_nonneg hepsilon_lt_one
    (by
      intro t ht
      simpa [card_sym_sum_fin_eq_choose] using hdim t ht)
    hs havg

/--
Source-parameter finite closeout with stars-and-bars coordinates and the
source's coarse Turán average estimate.
-/
theorem false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_choose_coarse_turan
    {m d s k power : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      ((2 * d + power - 1).choose power : ℝ) *
          ((Fintype.card {j // j ∈ t} : ℝ) * (1 + epsilon) ^ (2 * power) +
            (Fintype.card {j // j ∈ t} : ℝ) *
              (Fintype.card {j // j ∈ t} : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (Fintype.card {j // j ∈ t} : ℝ) ^ 2 *
          (1 - epsilon) ^ (2 * power))
    (hs : 1 < s)
    (havg :
      (m : ℝ) * ((2 * k : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False :=
  false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_coarse_turan
    (A := A) (B := B) (s := s) (k := k) (power := power)
    hrec hk hepsilon_nonneg hepsilon_lt_one
    (by
      intro t ht
      simpa [card_sym_sum_fin_eq_choose] using hdim t ht)
    hs havg

/--
Source-parameter finite closeout with both finite-cardinality normalizations
made explicit: the symmetric-power coordinate space is counted by
stars-and-bars, and every aligned source subset has cardinality `s`.
-/
theorem false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_choose_card
    {m d s k power : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim :
      ((2 * d + power - 1).choose power : ℝ) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False :=
  false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_choose
    (A := A) (B := B) (s := s) (k := k) (power := power)
    hrec hk hepsilon_nonneg hepsilon_lt_one
    (by
      intro t ht
      simpa [Fintype.card_coe, ht] using hdim)
    hs havg

/--
Source-parameter finite closeout with source subset cardinality written as
`s`, and the source's coarse Turán average estimate.
-/
theorem false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_choose_card_coarse_turan
    {m d s k power : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim :
      ((2 * d + power - 1).choose power : ℝ) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 1 < s)
    (havg :
      (m : ℝ) * ((2 * k : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False :=
  false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_choose_coarse_turan
    (A := A) (B := B) (s := s) (k := k) (power := power)
    hrec hk hepsilon_nonneg hepsilon_lt_one
    (by
      intro t ht
      simpa [Fintype.card_coe, ht] using hdim)
    hs havg

/--
Source-parameter finite closeout with the binomial coordinate count replaced
by the factorial-normalized power envelope.  This is the finite form that
retains the logarithmic factor in the source asymptotic lower bound.
-/
theorem false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_factorial_card
    {m d s k power : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim :
      ((((2 * d + power - 1) ^ power : ℕ) : ℝ) / (power.factorial : ℝ)) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hchoose_real := choose_sum_fin_le_pow_div_factorial d power
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hbeta_nonneg : 0 ≤ 1 + epsilon := by linarith
  have heta_nonneg : 0 ≤ epsilon / (k : ℝ) :=
    div_nonneg hepsilon_nonneg hk_real_pos.le
  have hterm_nonneg :
      0 ≤
        (s : ℝ) * (1 + epsilon) ^ (2 * power) +
          (s : ℝ) * (s : ℝ) *
            (epsilon / (k : ℝ)) ^ (2 * power) := by
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hbeta_nonneg _))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (pow_nonneg heta_nonneg _))
  have hdim_choose :
      ((2 * d + power - 1).choose power : ℝ) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hchoose_real hterm_nonneg) hdim
  exact
    false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_choose_card
      (A := A) (B := B) (s := s) (k := k) (power := power)
      hrec hk hepsilon_nonneg hepsilon_lt_one hdim_choose hs havg

/--
Source-parameter finite closeout with the factorial-normalized coordinate
envelope and the source's coarse Turán average estimate.
-/
theorem false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_factorial_card_coarse_turan
    {m d s k power : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim :
      ((((2 * d + power - 1) ^ power : ℕ) : ℝ) / (power.factorial : ℝ)) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 1 < s)
    (havg :
      (m : ℝ) * ((2 * k : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False := by
  have hchoose_real := choose_sum_fin_le_pow_div_factorial d power
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hbeta_nonneg : 0 ≤ 1 + epsilon := by linarith
  have heta_nonneg : 0 ≤ epsilon / (k : ℝ) :=
    div_nonneg hepsilon_nonneg hk_real_pos.le
  have hterm_nonneg :
      0 ≤
        (s : ℝ) * (1 + epsilon) ^ (2 * power) +
          (s : ℝ) * (s : ℝ) *
            (epsilon / (k : ℝ)) ^ (2 * power) := by
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hbeta_nonneg _))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (pow_nonneg heta_nonneg _))
  have hdim_choose :
      ((2 * d + power - 1).choose power : ℝ) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hchoose_real hterm_nonneg) hdim
  exact
    false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_choose_card_coarse_turan
      (A := A) (B := B) (s := s) (k := k) (power := power)
      hrec hk hepsilon_nonneg hepsilon_lt_one hdim_choose hs havg

/--
Source-parameter finite closeout with the Stirling-style source-scale
coordinate envelope and the source's coarse Turán average estimate.
-/
theorem false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_exp_card_coarse_turan
    {m d s k power : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hpower : 0 < power)
    (hdim :
      (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 1 < s)
    (havg :
      (m : ℝ) * ((2 * k : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False := by
  have hpow_le :=
    pow_div_factorial_le_exp_mul_div_pow (N := 2 * d + power - 1) hpower
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hbeta_nonneg : 0 ≤ 1 + epsilon := by linarith
  have heta_nonneg : 0 ≤ epsilon / (k : ℝ) :=
    div_nonneg hepsilon_nonneg hk_real_pos.le
  have hterm_nonneg :
      0 ≤
        (s : ℝ) * (1 + epsilon) ^ (2 * power) +
          (s : ℝ) * (s : ℝ) *
            (epsilon / (k : ℝ)) ^ (2 * power) := by
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hbeta_nonneg _))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (pow_nonneg heta_nonneg _))
  have hdim_factorial :
      ((((2 * d + power - 1) ^ power : ℕ) : ℝ) / (power.factorial : ℝ)) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power) :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hpow_le hterm_nonneg) hdim
  exact
    false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_factorial_card_coarse_turan
      (A := A) (B := B) (s := s) (k := k) (power := power)
      hrec hk hepsilon_nonneg hepsilon_lt_one hdim_factorial hs havg

/--
Source-parameter finite closeout with the binomial coordinate count replaced
by the simpler sufficient power envelope `(2d + power)^power`.
-/
theorem false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_pow_card
    {m d s k power : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim :
      ((((2 * d + power) ^ power : ℕ) : ℝ)) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hchoose_nat :
      (2 * d + power - 1).choose power ≤ (2 * d + power) ^ power := by
    calc
      (2 * d + power - 1).choose power ≤ (2 * d + power - 1) ^ power :=
        Nat.choose_le_pow _ _
      _ ≤ (2 * d + power) ^ power :=
        Nat.pow_le_pow_left (Nat.sub_le _ _) _
  have hchoose_real :
      ((2 * d + power - 1).choose power : ℝ) ≤
        ((((2 * d + power) ^ power : ℕ) : ℝ)) := by
    exact_mod_cast hchoose_nat
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hbeta_nonneg : 0 ≤ 1 + epsilon := by linarith
  have heta_nonneg : 0 ≤ epsilon / (k : ℝ) :=
    div_nonneg hepsilon_nonneg hk_real_pos.le
  have hterm_nonneg :
      0 ≤
        (s : ℝ) * (1 + epsilon) ^ (2 * power) +
          (s : ℝ) * (s : ℝ) *
            (epsilon / (k : ℝ)) ^ (2 * power) := by
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hbeta_nonneg _))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (pow_nonneg heta_nonneg _))
  have hdim_choose :
      ((2 * d + power - 1).choose power : ℝ) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hchoose_real hterm_nonneg) hdim
  exact
    false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_choose_card
      (A := A) (B := B) (s := s) (k := k) (power := power)
      hrec hk hepsilon_nonneg hepsilon_lt_one hdim_choose hs havg

theorem linearCompressedSensingDimensionValue_gt_of_not_feasible_dimension
    {m k d D : ℕ} {epsilon : ℝ}
    (hvalue : linearCompressedSensingDimensionValue m k epsilon d)
    (himpossible : ¬ linearCompressedSensingFeasible m k D epsilon) :
    D < d := by
  by_contra hnot
  have hd_le_D : d ≤ D := Nat.le_of_not_gt hnot
  exact himpossible
    (linearCompressedSensingFeasible_mono_dimension hd_le_D hvalue.1)

/--
Minimum-dimension lower-bound form of the finite symmetric-power proof: if a
candidate dimension `D` satisfies the displayed symmetric-power and Turán
arithmetic hypotheses, then the paper's exact minimum dimension is larger than
`D`.
-/
theorem linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters
    {m D s k power : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (Fintype.card (Sym (Sum (Fin D) (Fin D)) power) : ℝ) *
          ((Fintype.card {j // j ∈ t} : ℝ) * (1 + epsilon) ^ (2 * power) +
            (Fintype.card {j // j ∈ t} : ℝ) *
              (Fintype.card {j // j ∈ t} : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (Fintype.card {j // j ∈ t} : ℝ) ^ 2 *
          (1 - epsilon) ^ (2 * power))
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2)))
    {dmin : ℕ}
    (hvalue : linearCompressedSensingDimensionValue m k epsilon dmin) :
    D < dmin := by
  refine linearCompressedSensingDimensionValue_gt_of_not_feasible_dimension hvalue ?_
  intro hfeas
  rcases hfeas with ⟨A, B, hrec⟩
  exact
    false_of_linearRecoveryCondition_and_symmetricPower_source_parameters
      (A := A) (B := B) (s := s) (k := k) (power := power)
      hrec hk hepsilon_nonneg hepsilon_lt_one hdim hs havg

/--
Minimum-dimension finite lower-bound form with the symmetric-power coordinate
count rewritten as `choose (2D + power - 1) power`.
-/
theorem linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_choose
    {m D s k power : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      ((2 * D + power - 1).choose power : ℝ) *
          ((Fintype.card {j // j ∈ t} : ℝ) * (1 + epsilon) ^ (2 * power) +
            (Fintype.card {j // j ∈ t} : ℝ) *
              (Fintype.card {j // j ∈ t} : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (Fintype.card {j // j ∈ t} : ℝ) ^ 2 *
          (1 - epsilon) ^ (2 * power))
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2)))
    {dmin : ℕ}
    (hvalue : linearCompressedSensingDimensionValue m k epsilon dmin) :
    D < dmin :=
  linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters
    (m := m) (D := D) (s := s) (k := k) (power := power)
    hk hepsilon_nonneg hepsilon_lt_one
    (by
      intro t ht
      simpa [card_sym_sum_fin_eq_choose] using hdim t ht)
    hs havg hvalue

/--
Minimum-dimension finite lower-bound form with both finite-cardinality
normalizations made explicit: the symmetric-power coordinate count is the
stars-and-bars binomial coefficient, and every source subset has cardinality
`s`.
-/
theorem linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_choose_card
    {m D s k power : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim :
      ((2 * D + power - 1).choose power : ℝ) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2)))
    {dmin : ℕ}
    (hvalue : linearCompressedSensingDimensionValue m k epsilon dmin) :
    D < dmin :=
  linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_choose
    (m := m) (D := D) (s := s) (k := k) (power := power)
    hk hepsilon_nonneg hepsilon_lt_one
    (by
      intro t ht
      simpa [Fintype.card_coe, ht] using hdim)
    hs havg hvalue

/--
Minimum-dimension finite lower-bound form with the binomial coordinate count
bounded by the factorial-normalized power envelope.  This preserves the
source logarithmic factor in later asymptotic packaging.
-/
theorem linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_factorial_card
    {m D s k power : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim :
      ((((2 * D + power - 1) ^ power : ℕ) : ℝ) / (power.factorial : ℝ)) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2)))
    {dmin : ℕ}
    (hvalue : linearCompressedSensingDimensionValue m k epsilon dmin) :
    D < dmin := by
  have hchoose_real := choose_sum_fin_le_pow_div_factorial D power
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hbeta_nonneg : 0 ≤ 1 + epsilon := by linarith
  have heta_nonneg : 0 ≤ epsilon / (k : ℝ) :=
    div_nonneg hepsilon_nonneg hk_real_pos.le
  have hterm_nonneg :
      0 ≤
        (s : ℝ) * (1 + epsilon) ^ (2 * power) +
          (s : ℝ) * (s : ℝ) *
            (epsilon / (k : ℝ)) ^ (2 * power) := by
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hbeta_nonneg _))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (pow_nonneg heta_nonneg _))
  have hdim_choose :
      ((2 * D + power - 1).choose power : ℝ) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hchoose_real hterm_nonneg) hdim
  exact
    linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_choose_card
      (m := m) (D := D) (s := s) (k := k) (power := power)
      hk hepsilon_nonneg hepsilon_lt_one hdim_choose hs havg hvalue

/--
Minimum-dimension finite lower-bound form with the binomial coordinate count
replaced by the simpler sufficient power envelope `(2D + power)^power`.
-/
theorem linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_pow_card
    {m D s k power : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hdim :
      ((((2 * D + power) ^ power : ℕ) : ℝ)) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 0 < s)
    (havg :
      m * (2 * k) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2)))
    {dmin : ℕ}
    (hvalue : linearCompressedSensingDimensionValue m k epsilon dmin) :
    D < dmin := by
  have hchoose_nat :
      (2 * D + power - 1).choose power ≤ (2 * D + power) ^ power := by
    calc
      (2 * D + power - 1).choose power ≤ (2 * D + power - 1) ^ power :=
        Nat.choose_le_pow _ _
      _ ≤ (2 * D + power) ^ power :=
        Nat.pow_le_pow_left (Nat.sub_le _ _) _
  have hchoose_real :
      ((2 * D + power - 1).choose power : ℝ) ≤
        ((((2 * D + power) ^ power : ℕ) : ℝ)) := by
    exact_mod_cast hchoose_nat
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hbeta_nonneg : 0 ≤ 1 + epsilon := by linarith
  have heta_nonneg : 0 ≤ epsilon / (k : ℝ) :=
    div_nonneg hepsilon_nonneg hk_real_pos.le
  have hterm_nonneg :
      0 ≤
        (s : ℝ) * (1 + epsilon) ^ (2 * power) +
          (s : ℝ) * (s : ℝ) *
            (epsilon / (k : ℝ)) ^ (2 * power) := by
    exact add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hbeta_nonneg _))
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (pow_nonneg heta_nonneg _))
  have hdim_choose :
      ((2 * D + power - 1).choose power : ℝ) *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hchoose_real hterm_nonneg) hdim
  exact
    linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_choose_card
      (m := m) (D := D) (s := s) (k := k) (power := power)
      hk hepsilon_nonneg hepsilon_lt_one hdim_choose hs havg hvalue

/--
The threshold proof also uses the zero vector and singleton vector to place the
threshold between `0` and the diagonal entry.
-/
theorem threshold_nonneg_of_thresholdSeparationCondition
    {m d k : ℕ} {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hsep : thresholdSeparationCondition A B threshold k) (i : Fin m) :
    0 ≤ threshold i := by
  exact
    threshold_nonneg_of_thresholdSeparates
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (threshold := threshold) (k := k) hsep i

/-- Singleton positive examples put the threshold below the diagonal entry. -/
theorem threshold_lt_diagonal_of_thresholdSeparationCondition
    {m d k : ℕ} {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk : 1 ≤ k) (hsep : thresholdSeparationCondition A B threshold k)
    (i : Fin m) :
    threshold i < inner (B i) (A i) := by
  exact
    threshold_lt_diag_of_thresholdSeparates
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (threshold := threshold) (k := k) hk hsep i

/-- Threshold separation implies each diagonal response is positive. -/
theorem diagonal_pos_of_thresholdSeparationCondition
    {m d k : ℕ} {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk : 1 ≤ k) (hsep : thresholdSeparationCondition A B threshold k)
    (i : Fin m) :
    0 < inner (B i) (A i) := by
  exact
    diag_pos_of_thresholdSeparates
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (threshold := threshold) (k := k) hk hsep i

/--
Source normalization step for Theorem Threshold: rescaling each probe row and
threshold by the positive diagonal response preserves the separator and makes
the diagonal entries of `B^T A` equal to `1`.
-/
theorem thresholdSeparationCondition_diagonalNormalized
    {m d k : ℕ} {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk : 1 ≤ k) (hsep : thresholdSeparationCondition A B threshold k) :
    thresholdSeparationCondition A (diagonalNormalizedProbeMatrix A B)
      (diagonalNormalizedThresholds A B threshold) k := by
  exact
    thresholdSeparates_diagonalNormalized
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (threshold := threshold) (k := k) hk hsep

/-- The normalized threshold model has diagonal response `1`. -/
theorem diagonalNormalizedProbeMatrix_diag_eq_one_of_thresholdSeparationCondition
    {m d k : ℕ} {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk : 1 ≤ k) (hsep : thresholdSeparationCondition A B threshold k)
    (i : Fin m) :
    inner (diagonalNormalizedProbeMatrix A B i) (A i) = 1 := by
  exact
    diagonalNormalizedProbes_diag_eq_one_of_thresholdSeparates
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (threshold := threshold) (k := k) hk hsep i

/--
Activation-bias bridge: a monotone activation separator supplies the linear
threshold separator used by Theorem Threshold.
-/
theorem thresholdSeparationCondition_of_monotone_activationSeparationCondition
    {m d k : ℕ} {A W : FeatureMatrix m d} {bias : Fin m → ℝ}
    {sigma : ℝ → ℝ}
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k) :
    thresholdSeparationCondition A W (activationDerivedThresholds A W bias k) k := by
  exact
    thresholdSeparates_of_monotone_activation
      (Feature := Fin m) (Coord := Fin d) (A := A) (W := W)
      (bias := bias) (σ := sigma) (k := k) hmono hact

/-!
## Complementary trace/Frobenius bound for the printed threshold regime

The source's Alon--Turán proof gives the logarithmic refinement once `m` is
large enough relative to `k^3`.  The lemmas below derive a uniform
`Omega(k^2)` bound directly from threshold separation.  This supplies the
intermediate range `k^2 < m = O(k^3)` and permits the two proof routes to be
combined on the source's original `k < sqrt(m)` regime.
-/

/-- The off-diagonal part of row `i` of `B^T A`. -/
noncomputable def thresholdOffdiagRow {m d : ℕ}
    (A B : FeatureMatrix m d) (i : Fin m) : Fin m → ℝ :=
  fun j => if j = i then 0 else inner (B i) (A j)

theorem row_sum_le_threshold_of_thresholdSeparationCondition
    {m d k : ℕ} {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hsep : thresholdSeparationCondition A B threshold k)
    (i : Fin m) {T : Finset (Fin m)} (hiT : i ∉ T) (hTcard : T.card ≤ k) :
    (∑ j ∈ T, inner (B i) (A j)) ≤ threshold i := by
  classical
  have hiff := hsep i (finsetIndicator T)
    (kSparse_finsetIndicator_of_card_le (T := T) hTcard)
    (inZeroOne_finsetIndicator T)
  have hzi : finsetIndicator T i = 0 :=
    finsetIndicator_apply_not_mem hiT
  have hnot : ¬ threshold i < linearProbe A B (finsetIndicator T) i := by
    intro hcross
    have hbad := hiff.mp hcross
    norm_num [hzi] at hbad
  have hprobe :
      linearProbe A B (finsetIndicator T) i =
        ∑ j ∈ T, inner (B i) (A j) :=
    linearProbe_finsetIndicator A B T i
  exact not_lt.mp (by simpa [hprobe] using hnot)

theorem threshold_lt_diag_add_row_sum_of_thresholdSeparationCondition
    {m d k : ℕ} {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hsep : thresholdSeparationCondition A B threshold k)
    (i : Fin m) {T : Finset (Fin m)} (hiT : i ∉ T)
    (hTcard : T.card + 1 ≤ k) :
    threshold i < inner (B i) (A i) + ∑ j ∈ T, inner (B i) (A j) := by
  classical
  let U : Finset (Fin m) := insert i T
  have hUcard : U.card ≤ k := by
    simpa [U, hiT] using hTcard
  have hiff := hsep i (finsetIndicator U)
    (kSparse_finsetIndicator_of_card_le (T := U) hUcard)
    (inZeroOne_finsetIndicator U)
  have hzi : finsetIndicator U i = 1 := by simp [U]
  have hcross : threshold i < linearProbe A B (finsetIndicator U) i :=
    hiff.mpr hzi
  have hprobe :
      linearProbe A B (finsetIndicator U) i =
        inner (B i) (A i) + ∑ j ∈ T, inner (B i) (A j) := by
    rw [linearProbe_finsetIndicator]
    simp [U, hiT]
  simpa [hprobe] using hcross

theorem l1On_thresholdOffdiagRow_le_two
    {m d k q : ℕ} {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hsep : thresholdSeparationCondition A B threshold k)
    (hdiag : ∀ i : Fin m, inner (B i) (A i) = 1)
    (hqk : q + 1 ≤ k) (i : Fin m) (T : Finset (Fin m))
    (hTcard : T.card ≤ q) :
    l1On T (thresholdOffdiagRow A B i) ≤ 2 := by
  classical
  let T' : Finset (Fin m) := T.erase i
  let P : Finset (Fin m) := T'.filter fun j => 0 ≤ inner (B i) (A j)
  let N : Finset (Fin m) := T'.filter fun j => inner (B i) (A j) < 0
  have hiT' : i ∉ T' := by simp [T']
  have hT'card : T'.card ≤ q := by
    have herase : T'.card ≤ T.card := by
      simpa [T'] using
        (Finset.card_erase_le : (T.erase i).card ≤ T.card)
    exact herase.trans hTcard
  have hPsub : P ⊆ T' := Finset.filter_subset _ _
  have hNsub : N ⊆ T' := Finset.filter_subset _ _
  have hiP : i ∉ P := fun hi => hiT' (hPsub hi)
  have hiN : i ∉ N := fun hi => hiT' (hNsub hi)
  have hPcard : P.card ≤ k :=
    (Finset.card_le_card hPsub).trans
      (hT'card.trans (Nat.le_trans (Nat.le_succ q) hqk))
  have hNcard : N.card + 1 ≤ k := by
    have : N.card ≤ q := (Finset.card_le_card hNsub).trans hT'card
    omega
  have hPsum_le : (∑ j ∈ P, inner (B i) (A j)) ≤ threshold i :=
    row_sum_le_threshold_of_thresholdSeparationCondition hsep i hiP hPcard
  have ht_lt_one : threshold i < 1 := by
    have hk_one : 1 ≤ k := Nat.le_trans (by omega : 1 ≤ q + 1) hqk
    simpa [hdiag i] using
      threshold_lt_diagonal_of_thresholdSeparationCondition hk_one hsep i
  have hPsum_lt_one : (∑ j ∈ P, inner (B i) (A j)) < 1 :=
    lt_of_le_of_lt hPsum_le ht_lt_one
  have hNlower :
      threshold i < 1 + ∑ j ∈ N, inner (B i) (A j) := by
    simpa [hdiag i] using
      threshold_lt_diag_add_row_sum_of_thresholdSeparationCondition
        hsep i hiN hNcard
  have ht_nonneg : 0 ≤ threshold i :=
    threshold_nonneg_of_thresholdSeparationCondition hsep i
  have hNabs_lt_one :
      -(∑ j ∈ N, inner (B i) (A j)) < 1 := by
    linarith
  have hcover : P ∪ N = T' := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact hPsub hj
      · exact hNsub hj
    · intro hj
      by_cases hnonneg : 0 ≤ inner (B i) (A j)
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr ⟨hj, hnonneg⟩))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨hj, lt_of_not_ge hnonneg⟩))
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro j hjP hjN
    have hp := (Finset.mem_filter.mp hjP).2
    have hn := (Finset.mem_filter.mp hjN).2
    linarith
  have hsum_abs_T' :
      (∑ j ∈ T', |inner (B i) (A j)|) =
        (∑ j ∈ P, inner (B i) (A j)) -
          (∑ j ∈ N, inner (B i) (A j)) := by
    rw [← hcover, Finset.sum_union hdisj]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      rw [abs_of_nonneg (Finset.mem_filter.mp hj).2]
    · calc
        (∑ j ∈ N, |inner (B i) (A j)|) =
            ∑ j ∈ N, -inner (B i) (A j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [abs_of_neg (Finset.mem_filter.mp hj).2]
        _ = -(∑ j ∈ N, inner (B i) (A j)) :=
          Finset.sum_neg_distrib _
  have hsum_lt_two :
      (∑ j ∈ T', |inner (B i) (A j)|) < 2 := by
    rw [hsum_abs_T']
    linarith
  have hl1_eq :
      l1On T (thresholdOffdiagRow A B i) =
        ∑ j ∈ T', |inner (B i) (A j)| := by
    rw [l1On]
    calc
      (∑ j ∈ T, |thresholdOffdiagRow A B i j|) =
          ∑ j ∈ T.erase i, |thresholdOffdiagRow A B i j| := by
        symm
        apply Finset.sum_erase
        simp [thresholdOffdiagRow]
      _ = ∑ j ∈ T', |inner (B i) (A j)| := by
        apply Finset.sum_congr (by rfl)
        intro j hj
        have hji : j ≠ i := by
          simpa [T'] using (Finset.ne_of_mem_erase hj)
        simp [thresholdOffdiagRow, hji]
  rw [hl1_eq]
  exact le_of_lt hsum_lt_two

theorem l2Sq_thresholdOffdiagRow_le
    {m d k q : ℕ} {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hsep : thresholdSeparationCondition A B threshold k)
    (hdiag : ∀ i : Fin m, inner (B i) (A i) = 1)
    (hq : 0 < q) (hqk : q + 1 ≤ k) (i : Fin m) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (thresholdOffdiagRow A B i) ≤
      4 + (m : ℝ) * (2 / (q : ℝ)) ^ 2 := by
  have hbound :=
    l2Sq_le_sq_add_card_mul_sq_div_of_forall_l1On_card_le
      (thresholdOffdiagRow A B i) hq (by norm_num : (0 : ℝ) ≤ 2)
      (fun T hTcard =>
        l1On_thresholdOffdiagRow_le_two hsep hdiag hqk i T hTcard)
  norm_num at hbound ⊢
  simpa [Fintype.card_fin] using hbound

theorem interference_row_sq_sum_le
    {m d k q : ℕ} {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hsep : thresholdSeparationCondition A B threshold k)
    (hdiag : ∀ i : Fin m, inner (B i) (A i) = 1)
    (hq : 0 < q) (hqk : q + 1 ≤ k) (i : Fin m) :
    (∑ j : Fin m, (interferenceMatrix A B i j) ^ 2) ≤
      5 + (m : ℝ) * (2 / (q : ℝ)) ^ 2 := by
  have hoff := l2Sq_thresholdOffdiagRow_le hsep hdiag hq hqk i
  have hsplit :
      (∑ j : Fin m, (interferenceMatrix A B i j) ^ 2) =
        1 + AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (thresholdOffdiagRow A B i) := by
    rw [AppliedModelingLib.FiniteDimensionalNorms.l2Sq]
    calc
      (∑ j : Fin m, (interferenceMatrix A B i j) ^ 2) =
          (interferenceMatrix A B i i) ^ 2 +
            ∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
              (interferenceMatrix A B i j) ^ 2 := by
        have herase :=
          (Finset.sum_erase_add
            (Finset.univ : Finset (Fin m))
            (fun j => (interferenceMatrix A B i j) ^ 2)
            (Finset.mem_univ i)).symm
        simpa [add_comm] using herase
      _ = 1 +
            ∑ j ∈ (Finset.univ : Finset (Fin m)).erase i,
              (thresholdOffdiagRow A B i j) ^ 2 := by
        congr 1
        · simp [interferenceMatrix, hdiag i]
        · apply Finset.sum_congr rfl
          intro j hj
          have hji : j ≠ i := Finset.ne_of_mem_erase hj
          simp [thresholdOffdiagRow, interferenceMatrix, hji]
      _ = 1 + ∑ j : Fin m, (thresholdOffdiagRow A B i j) ^ 2 := by
        congr 1
        have herase :=
          Finset.sum_erase (Finset.univ : Finset (Fin m))
            (f := fun j => (thresholdOffdiagRow A B i j) ^ 2)
            (a := i) (by simp [thresholdOffdiagRow])
        simpa using herase
  rw [hsplit]
  linarith

theorem symmetrizedInterferenceMatrix_frobeniusSq_le_interferenceMatrix
    {m d : ℕ} (A B : FeatureMatrix m d) :
    frobeniusSq (symmetrizedInterferenceMatrix A B) ≤
      frobeniusSq (interferenceMatrix A B) := by
  classical
  unfold frobeniusSq
  have hpoint : ∀ i j : Fin m,
      (symmetrizedInterferenceMatrix A B i j) ^ 2 ≤
        ((interferenceMatrix A B i j) ^ 2 +
          (interferenceMatrix A B j i) ^ 2) / 2 := by
    intro i j
    rw [symmetrizedInterferenceMatrix_apply]
    have hsq := sq_nonneg
      (interferenceMatrix A B i j - interferenceMatrix A B j i)
    simp only [interferenceMatrix_apply] at hsq ⊢
    nlinarith
  calc
    (∑ i : Fin m, ∑ j : Fin m,
        symmetrizedInterferenceMatrix A B i j ^ 2) ≤
      ∑ i : Fin m, ∑ j : Fin m,
        ((interferenceMatrix A B i j) ^ 2 +
          (interferenceMatrix A B j i) ^ 2) / 2 := by
      exact Finset.sum_le_sum fun i _ =>
        Finset.sum_le_sum fun j _ => hpoint i j
    _ = ∑ i : Fin m, ∑ j : Fin m,
          (interferenceMatrix A B i j) ^ 2 := by
      have hswap :
          (∑ i : Fin m, ∑ j : Fin m,
            (interferenceMatrix A B j i) ^ 2) =
          ∑ i : Fin m, ∑ j : Fin m,
            (interferenceMatrix A B i j) ^ 2 := by
        rw [Finset.sum_comm]
      rw [show
        (∑ i : Fin m, ∑ j : Fin m,
          ((interferenceMatrix A B i j) ^ 2 +
            (interferenceMatrix A B j i) ^ 2) / 2) =
          ((∑ i : Fin m, ∑ j : Fin m,
              (interferenceMatrix A B i j) ^ 2) +
            (∑ i : Fin m, ∑ j : Fin m,
              (interferenceMatrix A B j i) ^ 2)) / 2 by
        simp only [div_eq_mul_inv, add_mul,
          Finset.sum_add_distrib, Finset.sum_mul]]
      rw [hswap]
      ring

theorem thresholdSeparationCondition_trace_frobenius_rank_bound
    {m d k q : ℕ} {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hsep : thresholdSeparationCondition A B threshold k)
    (hdiag : ∀ i : Fin m, inner (B i) (A i) = 1)
    (hq : 0 < q) (hqk : q + 1 ≤ k) :
    (m : ℝ) ^ 2 ≤
      (2 * (d : ℝ)) * ((m : ℝ) * (5 + (m : ℝ) * (2 / (q : ℝ)) ^ 2)) := by
  classical
  let H := symmetrizedInterferenceMatrix A B
  let C := interferenceMatrix A B
  have hHherm : H.IsHermitian := by
    refine Matrix.IsHermitian.ext ?_
    intro i j
    simp only [H, star_id_of_comm]
    exact symmetrizedInterferenceMatrix_symmetric A B j i
  have htrace : H.trace = (m : ℝ) := by
    simp [H, Matrix.trace, Matrix.diag,
      symmetrizedInterferenceMatrix, hdiag]
  have hrank_nat : H.rank ≤ 2 * d := by
    have hfactor : ∀ i j : Fin m,
        H i j =
          ∑ r : Sum (Fin d) (Fin d),
            (match r with
              | Sum.inl a => B i a / 2
              | Sum.inr a => A i a / 2) *
            (match r with
              | Sum.inl a => A j a
              | Sum.inr a => B j a) := by
      intro i j
      simp [H, symmetrizedInterferenceMatrix,
        AppliedModelingLib.Math.LinearCompressedSensing.inner,
        Fintype.sum_sum_type, mul_comm]
      rw [div_eq_mul_inv, add_mul, Finset.sum_mul, Finset.sum_mul]
      simp [div_eq_mul_inv, mul_assoc]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    have hrank :=
      rank_le_middle_card_of_dot_factorization
        (M := H)
        (X := fun i r =>
          match r with
          | Sum.inl a => B i a / 2
          | Sum.inr a => A i a / 2)
        (Y := fun j r =>
          match r with
          | Sum.inl a => A j a
          | Sum.inr a => B j a)
        hfactor
    simpa [Fintype.card_sum, Fintype.card_fin, two_mul] using hrank
  have hrank_real : (H.rank : ℝ) ≤ 2 * (d : ℝ) := by
    exact_mod_cast hrank_nat
  have hC_frob :
      frobeniusSq C ≤
        (m : ℝ) * (5 + (m : ℝ) * (2 / (q : ℝ)) ^ 2) := by
    unfold frobeniusSq
    calc
      (∑ i : Fin m, ∑ j : Fin m, C i j ^ 2) ≤
          ∑ _i : Fin m, (5 + (m : ℝ) * (2 / (q : ℝ)) ^ 2) := by
        exact Finset.sum_le_sum fun i _ => by
          simpa [C] using
            interference_row_sq_sum_le hsep hdiag hq hqk i
      _ = (m : ℝ) * (5 + (m : ℝ) * (2 / (q : ℝ)) ^ 2) := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hH_frob :
      Matrix.trace (Matrix.transpose H * H) ≤
        (m : ℝ) * (5 + (m : ℝ) * (2 / (q : ℝ)) ^ 2) := by
    rw [trace_transpose_mul_self_eq_frobeniusSq]
    exact
      (symmetrizedInterferenceMatrix_frobeniusSq_le_interferenceMatrix A B).trans
        (by simpa [H, C] using hC_frob)
  have htrace_rank :=
    trace_sq_le_rank_mul_trace_transpose_mul_self_of_isHermitian hHherm
  have hfrob_nonneg : 0 ≤ Matrix.trace (Matrix.transpose H * H) :=
    trace_transpose_mul_self_nonneg H
  calc
    (m : ℝ) ^ 2 = H.trace ^ 2 := by rw [htrace]
    _ ≤ (H.rank : ℝ) * Matrix.trace (Matrix.transpose H * H) := htrace_rank
    _ ≤ (2 * (d : ℝ)) *
        ((m : ℝ) * (5 + (m : ℝ) * (2 / (q : ℝ)) ^ 2)) :=
      mul_le_mul hrank_real hH_frob hfrob_nonneg (by positivity)

theorem thresholdSeparationCondition_k_sq_le_42_mul_dimension
    {m d k : ℕ} {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_three : 3 ≤ k)
    (hmsq : (k : ℝ) ^ 2 < (m : ℝ))
    (hsep : thresholdSeparationCondition A B threshold k) :
    (k : ℝ) ^ 2 ≤ 42 * (d : ℝ) := by
  let q : ℕ := k - 1
  let B' : FeatureMatrix m d := diagonalNormalizedProbeMatrix A B
  let threshold' : Fin m → ℝ :=
    diagonalNormalizedThresholds A B threshold
  have hsep' : thresholdSeparationCondition A B' threshold' k := by
    simpa [B', threshold'] using
      thresholdSeparationCondition_diagonalNormalized
        (A := A) (B := B) (threshold := threshold)
        (by omega : 1 ≤ k) hsep
  have hdiag' : ∀ i : Fin m, inner (B' i) (A i) = 1 := by
    intro i
    simpa [B'] using
      diagonalNormalizedProbeMatrix_diag_eq_one_of_thresholdSeparationCondition
        (A := A) (B := B) (threshold := threshold)
        (by omega : 1 ≤ k) hsep i
  have hq_pos : 0 < q := by omega
  have hqk : q + 1 ≤ k := by
    dsimp [q]
    omega
  have hmain :=
    thresholdSeparationCondition_trace_frobenius_rank_bound
      hsep' hdiag' hq_pos hqk
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk_sq_pos : 0 < (k : ℝ) ^ 2 := sq_pos_of_pos hk_pos
  have hm_pos : 0 < (m : ℝ) := lt_trans hk_sq_pos hmsq
  have hq_real_pos : 0 < (q : ℝ) := by exact_mod_cast hq_pos
  have hq_sq_pos : 0 < (q : ℝ) ^ 2 := sq_pos_of_pos hq_real_pos
  have hq_half : (k : ℝ) / 2 ≤ (q : ℝ) := by
    have hq_eq : (q : ℝ) = (k : ℝ) - 1 := by
      dsimp [q]
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    have hk_three_real : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_three
    rw [hq_eq]
    linarith
  have hk_sq_le_four_q_sq : (k : ℝ) ^ 2 ≤ 4 * (q : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((q : ℝ) - (k : ℝ) / 2)]
  have hdiv :
      (m : ℝ) / (q : ℝ) ^ 2 ≤
        4 * (m : ℝ) / (k : ℝ) ^ 2 := by
    rw [div_le_iff₀ hq_sq_pos, div_mul_eq_mul_div,
      le_div_iff₀ hk_sq_pos]
    nlinarith
  have hfive :
      (5 : ℝ) ≤ 5 * (m : ℝ) / (k : ℝ) ^ 2 := by
    rw [le_div_iff₀ hk_sq_pos]
    nlinarith
  have hterm :
      (m : ℝ) * (2 / (q : ℝ)) ^ 2 ≤
        16 * (m : ℝ) / (k : ℝ) ^ 2 := by
    have hrewrite :
        (m : ℝ) * (2 / (q : ℝ)) ^ 2 =
          4 * ((m : ℝ) / (q : ℝ) ^ 2) := by
      field_simp [hq_real_pos.ne']
      ring
    calc
      (m : ℝ) * (2 / (q : ℝ)) ^ 2 =
          4 * ((m : ℝ) / (q : ℝ) ^ 2) := hrewrite
      _ ≤ 4 * (4 * (m : ℝ) / (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ = 16 * (m : ℝ) / (k : ℝ) ^ 2 := by ring
  have hbracket :
      5 + (m : ℝ) * (2 / (q : ℝ)) ^ 2 ≤
        21 * (m : ℝ) / (k : ℝ) ^ 2 := by
    calc
      5 + (m : ℝ) * (2 / (q : ℝ)) ^ 2 ≤
          5 * (m : ℝ) / (k : ℝ) ^ 2 +
            16 * (m : ℝ) / (k : ℝ) ^ 2 := add_le_add hfive hterm
      _ = 21 * (m : ℝ) / (k : ℝ) ^ 2 := by ring
  have hm_nonneg : 0 ≤ (m : ℝ) := hm_pos.le
  have hscaled :
      (2 * (d : ℝ)) *
          ((m : ℝ) * (5 + (m : ℝ) * (2 / (q : ℝ)) ^ 2)) ≤
        42 * (d : ℝ) * (m : ℝ) ^ 2 / (k : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hbracket hm_nonneg
    have hmul' := mul_le_mul_of_nonneg_left hmul
      (by positivity : 0 ≤ 2 * (d : ℝ))
    calc
      (2 * (d : ℝ)) *
          ((m : ℝ) * (5 + (m : ℝ) * (2 / (q : ℝ)) ^ 2)) ≤
        (2 * (d : ℝ)) *
          ((m : ℝ) * (21 * (m : ℝ) / (k : ℝ) ^ 2)) := hmul'
      _ = 42 * (d : ℝ) * (m : ℝ) ^ 2 / (k : ℝ) ^ 2 := by ring
  have hfinal_div :
      (m : ℝ) ^ 2 ≤
        42 * (d : ℝ) * (m : ℝ) ^ 2 / (k : ℝ) ^ 2 :=
    hmain.trans hscaled
  have hmul_final := (le_div_iff₀ hk_sq_pos).mp hfinal_div
  have hm_sq_pos : 0 < (m : ℝ) ^ 2 := sq_pos_of_pos hm_pos
  nlinarith

theorem thresholdSeparationDimensionValue_k_sq_le_42_mul
    {m k dmin : ℕ} (hk_three : 3 ≤ k)
    (hmsq : (k : ℝ) ^ 2 < (m : ℝ))
    (hvalue : thresholdSeparationDimensionValue m k dmin) :
    (k : ℝ) ^ 2 ≤ 42 * (dmin : ℝ) := by
  rcases hvalue.1 with ⟨A, B, threshold, hsep⟩
  exact thresholdSeparationCondition_k_sq_le_42_mul_dimension
    hk_three hmsq hsep

theorem activationSeparationDimensionValue_k_sq_le_42_mul
    {m k dmin : ℕ} (hk_three : 3 ≤ k)
    (hmsq : (k : ℝ) ^ 2 < (m : ℝ))
    (hvalue : activationSeparationDimensionValue m k dmin) :
    (k : ℝ) ^ 2 ≤ 42 * (dmin : ℝ) := by
  rcases hvalue.1 with ⟨A, W, bias, sigma, hmono, hact⟩
  have hsep :
      thresholdSeparationCondition A W
        (activationDerivedThresholds A W bias k) k :=
    thresholdSeparationCondition_of_monotone_activationSeparationCondition
      hmono hact
  exact thresholdSeparationCondition_k_sq_le_42_mul_dimension
    hk_three hmsq hsep

/--
Corrected paper-facing threshold contradiction: after normalizing the diagonal
to `1`, the Turán/rank seam contradicts threshold separation when it supplies a
row with enough large off-diagonal entries.  The parameter `q` is the aligned
set size; for the source theorem use `q = k - 1`.
-/
theorem false_of_thresholdSeparationCondition_and_turan_principalSubmatrix_largeOffdiag
    {m d s k q : ℕ} {eta : ℝ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hsep : thresholdSeparationCondition A B threshold k)
    (hdiag : ∀ i : Fin m, inner (B i) (A i) = 1)
    (heta : 0 ≤ eta) (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (hoffdiag : ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y|)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  classical
  have havg' :
      Fintype.card (Fin m) * (2 * q) <
        (let n := Fintype.card (Fin m)
         let r := s - 1
         n.choose 2 -
          ((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2)) := by
    simpa using havg
  have hoffdiag' : ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((crossInnerMatrix A B).submatrix Subtype.val Subtype.val) x y| := by
    simpa [interferenceMatrix] using hoffdiag
  exact
    false_of_thresholdSeparates_and_card_mul_two_mul_lt_turanBound_of_forall_principalSubmatrix_exists_largeOffdiag
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (threshold := threshold) (η := eta) (s := s) (k := k) (q := q)
      hsep hdiag heta hq hqk hunit hs hoffdiag' havg'

/--
Corrected paper-facing threshold contradiction using the source's coarse
Turán estimate `m^2/(2r)-m/2`.
-/
theorem false_of_thresholdSeparationCondition_and_coarse_turan_principalSubmatrix_largeOffdiag
    {m d s k q : ℕ} {eta : ℝ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hsep : thresholdSeparationCondition A B threshold k)
    (hdiag : ∀ i : Fin m, inner (B i) (A i) = 1)
    (heta : 0 ≤ eta) (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 1 < s)
    (hoffdiag : ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y|)
    (havg :
      (m : ℝ) * ((2 * q : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False := by
  classical
  have hoffdiag' : ∀ t : Finset (Fin m), t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧ eta < |((crossInnerMatrix A B).submatrix Subtype.val Subtype.val) x y| := by
    simpa [interferenceMatrix] using hoffdiag
  have havg' :
      let n := Fintype.card (Fin m)
      let r := s - 1
      (n : ℝ) * ((2 * q : ℕ) : ℝ) <
        (n : ℝ) ^ 2 / (2 * (r : ℝ)) - (n : ℝ) / 2 := by
    simpa using havg
  exact
    false_of_thresholdSeparates_and_real_card_mul_two_mul_lt_coarse_turan_of_forall_principalSubmatrix_exists_largeOffdiag
      (Feature := Fin m) (Coord := Fin d) (A := A) (B := B)
      (threshold := threshold) (η := eta) (s := s) (k := k) (q := q)
      hsep hdiag heta hq hqk hunit hs hoffdiag' havg'

/--
Finite threshold closeout bridge: after diagonal normalization, normalized
Alon plus the rank/Turán counting step contradicts the Boolean threshold
separator under the displayed finite inequalities.
-/
theorem false_of_thresholdSeparationCondition_and_alonNormalizedRankBound_dimension_turan
    {m d s k q : ℕ} {eta c : ℝ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hsep : thresholdSeparationCondition A B threshold k)
    (hdiag : ∀ i : Fin m, inner (B i) (A i) = 1)
    (hAlon : ∀ t : Finset (Fin m), t.card = s →
      ∀ (D : Matrix {j // j ∈ t} {j // j ∈ t} ℝ) {epsilon : ℝ},
        1 / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < epsilon →
        epsilon < 1 / 2 →
        (∀ i, D i i = 1) →
        (∀ ⦃i j⦄, i ≠ j → |D i j| ≤ epsilon) →
        alonNormalizedRankBound (Fintype.card {j // j ∈ t}) epsilon c ≤ (D.rank : ℝ))
    (heta_low : ∀ t : Finset (Fin m), t.card = s →
      1 / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < eta)
    (heta_high : eta < 1 / 2)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (d : ℝ) < alonScaledRankBound (Fintype.card {j // j ∈ t}) 1 eta c)
    (heta : 0 ≤ eta) (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  classical
  have hdiag_lower : ∀ i : Fin m, (1 : ℝ) ≤ inner (B i) (A i) := by
    intro i
    rw [hdiag i]
  have hprincipal :
      ∀ t : Finset (Fin m), t.card = s →
        ∃ x y : {j // j ∈ t},
          x ≠ y ∧
            eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y| :=
    every_principalSubmatrix_has_largeOffdiag_of_alonNormalizedRankBound
      (A := A) (B := B) (c := c) hAlon zero_lt_one
      (by
        intro t ht
        simpa [one_div] using heta_low t ht)
      (by simpa [one_div] using heta_high)
      hdiag_lower
      (hrank := by
        intro t ht
        have hle_nat :
            (((interferenceMatrix A B).submatrix Subtype.val Subtype.val :
                Matrix {j // j ∈ t} {j // j ∈ t} ℝ).rank) ≤ d :=
          interferenceMatrix_principalSubmatrix_rank_le_d
            (A := A) (B := B)
            (select := (Subtype.val : {j // j ∈ t} → Fin m))
        have hle_real :
            (((interferenceMatrix A B).submatrix Subtype.val Subtype.val :
                Matrix {j // j ∈ t} {j // j ∈ t} ℝ).rank : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast hle_nat
        exact lt_of_le_of_lt hle_real (hdim t ht))
  exact
    false_of_thresholdSeparationCondition_and_turan_principalSubmatrix_largeOffdiag
      (A := A) (B := B) (threshold := threshold) (eta := eta)
      (s := s) (k := k) (q := q)
      hsep hdiag heta hq hqk hunit hs hprincipal havg

/--
Finite threshold closeout using the explicit symmetric-power polynomial
obstruction instead of an external Alon theorem.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan
    {m d s k q power : ℕ} {eta : ℝ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hsep : thresholdSeparationCondition A B threshold k)
    (hdiag : ∀ i : Fin m, inner (B i) (A i) = 1)
    (heta : 0 ≤ eta)
    (hsmall : ∀ t : Finset (Fin m), t.card = s →
      (Fintype.card {j // j ∈ t} : ℝ) * eta ^ (2 * power) ≤ 1)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      2 * (Fintype.card (Sym (Sum (Fin d) (Fin d)) power) : ℝ) <
        (Fintype.card {j // j ∈ t} : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  classical
  have hprincipal :
      ∀ t : Finset (Fin m), t.card = s →
        ∃ x y : {j // j ∈ t},
          x ≠ y ∧
            eta < |((interferenceMatrix A B).submatrix Subtype.val Subtype.val) x y| :=
    every_principalSubmatrix_has_largeOffdiag_of_symmetricPower_obstruction
      (A := A) (B := B) hdiag heta hsmall hdim
  exact
    false_of_thresholdSeparationCondition_and_turan_principalSubmatrix_largeOffdiag
      (A := A) (B := B) (threshold := threshold) (eta := eta)
      (s := s) (k := k) (q := q)
      hsep hdiag heta hq hqk hunit hs hprincipal havg

/--
Finite threshold closeout from the source hypotheses before diagonal
normalization.  This applies the paper's positive row-scaling step and then
uses the normalized finite rank/Turán contradiction.
-/
theorem false_of_thresholdSeparationCondition_and_alonNormalizedRankBound_dimension_turan_normalized
    {m d s k q : ℕ} {eta c : ℝ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hAlon : ∀ t : Finset (Fin m), t.card = s →
      ∀ (D : Matrix {j // j ∈ t} {j // j ∈ t} ℝ) {epsilon : ℝ},
        1 / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < epsilon →
        epsilon < 1 / 2 →
        (∀ i, D i i = 1) →
        (∀ ⦃i j⦄, i ≠ j → |D i j| ≤ epsilon) →
        alonNormalizedRankBound (Fintype.card {j // j ∈ t}) epsilon c ≤ (D.rank : ℝ))
    (heta_low : ∀ t : Finset (Fin m), t.card = s →
      1 / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < eta)
    (heta_high : eta < 1 / 2)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (d : ℝ) < alonScaledRankBound (Fintype.card {j // j ∈ t}) 1 eta c)
    (heta : 0 ≤ eta) (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  let B' : FeatureMatrix m d := diagonalNormalizedProbeMatrix A B
  let threshold' : Fin m → ℝ := diagonalNormalizedThresholds A B threshold
  have hsep' : thresholdSeparationCondition A B' threshold' k := by
    simpa [B', threshold'] using
      thresholdSeparationCondition_diagonalNormalized
        (A := A) (B := B) (threshold := threshold) hk_one hsep
  have hdiag' : ∀ i : Fin m, inner (B' i) (A i) = 1 := by
    intro i
    simpa [B'] using
      diagonalNormalizedProbeMatrix_diag_eq_one_of_thresholdSeparationCondition
        (A := A) (B := B) (threshold := threshold) hk_one hsep i
  exact
    false_of_thresholdSeparationCondition_and_alonNormalizedRankBound_dimension_turan
      (A := A) (B := B') (threshold := threshold') (eta := eta)
      (c := c) (s := s) (k := k) (q := q)
      hsep' hdiag' hAlon heta_low heta_high hdim heta hq hqk hunit hs havg

/--
Finite threshold closeout from the source hypotheses using the explicit
symmetric-power obstruction after the source diagonal normalization step.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan_normalized
    {m d s k q power : ℕ} {eta : ℝ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (heta : 0 ≤ eta)
    (hsmall : ∀ t : Finset (Fin m), t.card = s →
      (Fintype.card {j // j ∈ t} : ℝ) * eta ^ (2 * power) ≤ 1)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      2 * (Fintype.card (Sym (Sum (Fin d) (Fin d)) power) : ℝ) <
        (Fintype.card {j // j ∈ t} : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  let B' : FeatureMatrix m d := diagonalNormalizedProbeMatrix A B
  let threshold' : Fin m → ℝ := diagonalNormalizedThresholds A B threshold
  have hsep' : thresholdSeparationCondition A B' threshold' k := by
    simpa [B', threshold'] using
      thresholdSeparationCondition_diagonalNormalized
        (A := A) (B := B) (threshold := threshold) hk_one hsep
  have hdiag' : ∀ i : Fin m, inner (B' i) (A i) = 1 := by
    intro i
    simpa [B'] using
      diagonalNormalizedProbeMatrix_diag_eq_one_of_thresholdSeparationCondition
        (A := A) (B := B) (threshold := threshold) hk_one hsep i
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan
      (A := A) (B := B') (threshold := threshold') (eta := eta)
      (s := s) (k := k) (q := q) (power := power)
      hsep' hdiag' heta hsmall hdim hq hqk hunit hs havg

/--
Finite threshold closeout with stars-and-bars coordinates and source subset
cardinality written directly as `s`.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan_normalized_choose_card
    {m d s k q power : ℕ} {eta : ℝ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (heta : 0 ≤ eta)
    (hsmall : (s : ℝ) * eta ^ (2 * power) ≤ 1)
    (hdim : 2 * ((2 * d + power - 1).choose power : ℝ) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan_normalized
    (A := A) (B := B) (threshold := threshold) (eta := eta)
    (s := s) (k := k) (q := q) (power := power)
    hk_one hsep heta
    (by
      intro t ht
      simpa [Fintype.card_coe, ht] using hsmall)
    (by
      intro t ht
      simpa [card_sym_sum_fin_eq_choose, Fintype.card_coe, ht] using hdim)
    hq hqk hunit hs havg

/--
Finite threshold closeout with the binomial coordinate count replaced by the
simpler sufficient power envelope `(2d + power)^power`.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan_normalized_pow_card
    {m d s k q power : ℕ} {eta : ℝ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (heta : 0 ≤ eta)
    (hsmall : (s : ℝ) * eta ^ (2 * power) ≤ 1)
    (hdim : 2 * ((((2 * d + power) ^ power : ℕ) : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan_normalized_choose_card
    (A := A) (B := B) (threshold := threshold) (eta := eta)
    (s := s) (k := k) (q := q) (power := power)
    hk_one hsep heta hsmall
    (two_mul_choose_sum_fin_lt_of_two_mul_pow_lt (d := d) (t := power) hdim)
    hq hqk hunit hs havg

/--
Finite threshold closeout with the binomial coordinate count replaced by the
factorial-normalized power envelope.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan_normalized_factorial_card
    {m d s k q power : ℕ} {eta : ℝ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (heta : 0 ≤ eta)
    (hsmall : (s : ℝ) * eta ^ (2 * power) ≤ 1)
    (hdim :
      2 * ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
        (power.factorial : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan_normalized_choose_card
    (A := A) (B := B) (threshold := threshold) (eta := eta)
    (s := s) (k := k) (q := q) (power := power)
    hk_one hsep heta hsmall
    (two_mul_choose_sum_fin_lt_of_two_mul_pow_div_factorial_lt
      (d := d) (t := power) hdim)
    hq hqk hunit hs havg

/--
Finite threshold closeout with the source threshold substitution `eta = 1/q`.
The scalar condition `1 <= q * eta` is then automatic.
-/
theorem false_of_thresholdSeparationCondition_and_alonNormalizedRankBound_source_eta
    {m d s k q : ℕ} {c : ℝ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hAlon : ∀ t : Finset (Fin m), t.card = s →
      ∀ (D : Matrix {j // j ∈ t} {j // j ∈ t} ℝ) {epsilon : ℝ},
        1 / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < epsilon →
        epsilon < 1 / 2 →
        (∀ i, D i i = 1) →
        (∀ ⦃i j⦄, i ≠ j → |D i j| ≤ epsilon) →
        alonNormalizedRankBound (Fintype.card {j // j ∈ t}) epsilon c ≤ (D.rank : ℝ))
    (heta_low : ∀ t : Finset (Fin m), t.card = s →
      1 / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < 1 / (q : ℝ))
    (heta_high : 1 / (q : ℝ) < 1 / 2)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (d : ℝ) < alonScaledRankBound (Fintype.card {j // j ∈ t}) 1 (1 / (q : ℝ)) c)
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hq_real_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have heta_nonneg : 0 ≤ 1 / (q : ℝ) := by positivity
  have hunit : 1 ≤ (q : ℝ) * (1 / (q : ℝ)) := by
    field_simp [ne_of_gt hq_real_pos]
    exact le_rfl
  exact
    false_of_thresholdSeparationCondition_and_alonNormalizedRankBound_dimension_turan_normalized
      (A := A) (B := B) (threshold := threshold) (eta := 1 / (q : ℝ))
      (c := c) (s := s) (k := k) (q := q)
      hk_one hsep hAlon heta_low heta_high hdim
      heta_nonneg hq hqk hunit hs havg

/--
Finite threshold closeout with `eta = 1/q`, using the explicit symmetric-power
rank obstruction.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta
    {m d s k q power : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hsmall : ∀ t : Finset (Fin m), t.card = s →
      (Fintype.card {j // j ∈ t} : ℝ) * (1 / (q : ℝ)) ^ (2 * power) ≤ 1)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      2 * (Fintype.card (Sym (Sum (Fin d) (Fin d)) power) : ℝ) <
        (Fintype.card {j // j ∈ t} : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hq_real_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have heta_nonneg : 0 ≤ 1 / (q : ℝ) := by positivity
  have hunit : 1 ≤ (q : ℝ) * (1 / (q : ℝ)) := by
    field_simp [ne_of_gt hq_real_pos]
    exact le_rfl
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan_normalized
      (A := A) (B := B) (threshold := threshold) (eta := 1 / (q : ℝ))
      (s := s) (k := k) (q := q) (power := power)
      hk_one hsep heta_nonneg hsmall hdim hq hqk hunit hs havg

/--
Finite threshold closeout with `eta = 1/q`, stars-and-bars coordinates, and
the source subset cardinality written directly as `s`.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_choose_card
    {m d s k q power : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hsmall : (s : ℝ) * (1 / (q : ℝ)) ^ (2 * power) ≤ 1)
    (hdim : 2 * ((2 * d + power - 1).choose power : ℝ) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta
    (A := A) (B := B) (threshold := threshold)
    (s := s) (k := k) (q := q) (power := power)
    hk_one hsep
    (by
      intro t ht
      simpa [Fintype.card_coe, ht] using hsmall)
    (by
      intro t ht
      simpa [card_sym_sum_fin_eq_choose, Fintype.card_coe, ht] using hdim)
    hq hqk hs havg

/--
Finite threshold closeout with `eta = 1/q` and the binomial coordinate count
replaced by the simpler sufficient power envelope `(2d + power)^power`.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_pow_card
    {m d s k q power : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hsmall : (s : ℝ) * (1 / (q : ℝ)) ^ (2 * power) ≤ 1)
    (hdim : 2 * ((((2 * d + power) ^ power : ℕ) : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_choose_card
    (A := A) (B := B) (threshold := threshold)
    (s := s) (k := k) (q := q) (power := power)
    hk_one hsep hsmall
    (two_mul_choose_sum_fin_lt_of_two_mul_pow_lt (d := d) (t := power) hdim)
    hq hqk hs havg

/--
Finite threshold closeout with `eta = 1/q` and the factorial-normalized
coordinate envelope.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_factorial_card
    {m d s k q power : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hsmall : (s : ℝ) * (1 / (q : ℝ)) ^ (2 * power) ≤ 1)
    (hdim :
      2 * ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
        (power.factorial : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_choose_card
    (A := A) (B := B) (threshold := threshold)
    (s := s) (k := k) (q := q) (power := power)
    hk_one hsep hsmall
    (two_mul_choose_sum_fin_lt_of_two_mul_pow_div_factorial_lt
      (d := d) (t := power) hdim)
    hq hqk hs havg

/--
Source-readable smallness condition for the threshold/activation lower-bound
proofs.  If the source subset size is at most `q^(2*power)`, then the
normalization choice `eta = 1/q` satisfies the analytic smallness premise.
-/
theorem source_eta_small_of_s_le_q_pow
    {s q power : ℕ} (hq : 0 < q)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power)) :
    (s : ℝ) * (1 / (q : ℝ)) ^ (2 * power) ≤ 1 := by
  have hq_real_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hpow_pos : 0 < (q : ℝ) ^ (2 * power) := pow_pos hq_real_pos _
  have hinv_nonneg : 0 ≤ (1 / (q : ℝ)) ^ (2 * power) := by positivity
  calc
    (s : ℝ) * (1 / (q : ℝ)) ^ (2 * power)
        ≤ (q : ℝ) ^ (2 * power) * (1 / (q : ℝ)) ^ (2 * power) :=
          mul_le_mul_of_nonneg_right hs_le hinv_nonneg
    _ = 1 := by
          rw [one_div, inv_pow]
          exact mul_inv_cancel₀ hpow_pos.ne'

/--
Algebraic form of the source Turán parameter choice: if
`(4q+1) * r < m`, then the coarse Turán average
`m^2/(2r) - m/2` beats `m * 2q`.
-/
theorem coarse_turan_average_of_four_mul_add_one_mul_lt
    {m q r : ℕ} (hm : 0 < m) (hr : 0 < r)
    (h : (((4 * q + 1 : ℕ) : ℝ) * (r : ℝ)) < (m : ℝ)) :
    (m : ℝ) * ((2 * q : ℕ) : ℝ) <
      (m : ℝ) ^ 2 / (2 * (r : ℝ)) - (m : ℝ) / 2 := by
  have hm_real_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hr_real_pos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hnorm : (4 * (q : ℝ) + 1) * (r : ℝ) < (m : ℝ) := by
    norm_num at h ⊢
    simpa [mul_assoc, mul_comm, mul_left_comm, add_comm] using h
  have hmul := mul_lt_mul_of_pos_right hnorm hm_real_pos
  rw [show ((2 * q : ℕ) : ℝ) = 2 * (q : ℝ) by norm_num]
  field_simp [hr_real_pos.ne']
  ring_nf
  nlinarith [hmul]

/--
Source floor choice for the Turán parameter: with
`s = floor(m / (4q+1))`, the strict source Turán inequality holds after
using `s - 1` as the graph-clique parameter.
-/
theorem source_turan_floor_selector_mul_sub_one_lt
    {m q : ℕ} (hm : 0 < m) :
    (((4 * q + 1 : ℕ) : ℝ) *
        (((Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ)) - 1 : ℕ) : ℝ))) <
      (m : ℝ) := by
  exact
    AppliedModelingLib.Math.nat_mul_floor_div_sub_one_lt
      (m := m) (a := 4 * q + 1) hm (by omega)

/--
Split sufficient conditions for the lower-bound symmetric-power dimension
inequality.  This isolates the additive arithmetic from the later logarithmic
parameter choice.
-/
theorem lower_symmetricPower_hdim_of_split_bounds
    {D s k power : ℕ} {epsilon : ℝ}
    (hs : 0 < s) (hepsilon_lt_one : epsilon < 1)
    (hmain :
      (Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
          (1 + epsilon) ^ (2 * power) ≤
        (1 / 4) * (s : ℝ) * (1 - epsilon) ^ (2 * power))
    (hnoise :
      (Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
          (epsilon / (k : ℝ)) ^ (2 * power) ≤
        (1 / 4) * (1 - epsilon) ^ (2 * power)) :
    (Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
        ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
          (s : ℝ) * (s : ℝ) *
              (epsilon / (k : ℝ)) ^ (2 * power)) <
      (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power) := by
  let L : ℝ :=
    (Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) /
      (power : ℝ)) ^ power
  have hs_real_pos : 0 < (s : ℝ) := by exact_mod_cast hs
  have htail_pos : 0 < (1 - epsilon) ^ (2 * power) := by
    exact pow_pos (by linarith) _
  have hmain_mul :
      (s : ℝ) * (L * (1 + epsilon) ^ (2 * power)) ≤
        (s : ℝ) * ((1 / 4) * (s : ℝ) *
          (1 - epsilon) ^ (2 * power)) :=
    mul_le_mul_of_nonneg_left (by simpa [L] using hmain) hs_real_pos.le
  have hnoise_mul :
      (s : ℝ) * (s : ℝ) *
          (L * (epsilon / (k : ℝ)) ^ (2 * power)) ≤
        (s : ℝ) * (s : ℝ) *
          ((1 / 4) * (1 - epsilon) ^ (2 * power)) :=
    mul_le_mul_of_nonneg_left (by simpa [L] using hnoise)
      (mul_nonneg hs_real_pos.le hs_real_pos.le)
  have hsum :
      (s : ℝ) * (L * (1 + epsilon) ^ (2 * power)) +
          (s : ℝ) * (s : ℝ) *
            (L * (epsilon / (k : ℝ)) ^ (2 * power)) ≤
        (s : ℝ) * ((1 / 4) * (s : ℝ) *
          (1 - epsilon) ^ (2 * power)) +
          (s : ℝ) * (s : ℝ) *
            ((1 / 4) * (1 - epsilon) ^ (2 * power)) :=
    add_le_add hmain_mul hnoise_mul
  have hhalf_lt :
      (s : ℝ) * ((1 / 4) * (s : ℝ) *
          (1 - epsilon) ^ (2 * power)) +
          (s : ℝ) * (s : ℝ) *
            ((1 / 4) * (1 - epsilon) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power) := by
    have hrewrite :
        (s : ℝ) * ((1 / 4) * (s : ℝ) *
            (1 - epsilon) ^ (2 * power)) +
            (s : ℝ) * (s : ℝ) *
              ((1 / 4) * (1 - epsilon) ^ (2 * power)) =
          (1 / 2) * ((s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power)) := by
      ring
    rw [hrewrite]
    have htarget_pos : 0 < (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power) := by
      positivity
    nlinarith
  calc
    L *
        ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
          (s : ℝ) * (s : ℝ) *
              (epsilon / (k : ℝ)) ^ (2 * power))
        =
        (s : ℝ) * (L * (1 + epsilon) ^ (2 * power)) +
          (s : ℝ) * (s : ℝ) *
            (L * (epsilon / (k : ℝ)) ^ (2 * power)) := by ring
    _ ≤
        (s : ℝ) * ((1 / 4) * (s : ℝ) *
          (1 - epsilon) ^ (2 * power)) +
          (s : ℝ) * (s : ℝ) *
            ((1 / 4) * (1 - epsilon) ^ (2 * power)) := hsum
    _ < (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power) := hhalf_lt

theorem one_div_four_pow_le_one_div_four {power : ℕ} (hpower : 0 < power) :
    (1 / 4 : ℝ) ^ power ≤ 1 / 4 := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpower) with ⟨n, rfl⟩
  have hpow_nonneg : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
  have hpow_le_one : (1 / 4 : ℝ) ^ n ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  rw [pow_succ]
  nlinarith

/--
Conservative source-scale bound implying the two split bounds used by
`lower_symmetricPower_hdim_of_split_bounds`.
-/
theorem lower_symmetricPower_split_bounds_of_base_le
    {D s k power : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hpower : 0 < power)
    (hepsilon_nonneg : 0 ≤ epsilon) (hepsilon_lt_one : epsilon < 1)
    (hkpow_le_s : (k : ℝ) ^ (2 * power) ≤ (s : ℝ))
    (hbase :
      Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) / (power : ℝ) ≤
        (1 / 4) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (k : ℝ) ^ 2) :
    ((Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
          (1 + epsilon) ^ (2 * power) ≤
        (1 / 4) * (s : ℝ) * (1 - epsilon) ^ (2 * power)) ∧
      ((Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
          (epsilon / (k : ℝ)) ^ (2 * power) ≤
        (1 / 4) * (1 - epsilon) ^ (2 * power)) := by
  let L : ℝ :=
    Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) / (power : ℝ)
  let rho : ℝ := (1 - epsilon) / (1 + epsilon)
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hpower_real_pos : 0 < (power : ℝ) := by exact_mod_cast hpower
  have heps_den_pos : 0 < 1 + epsilon := by linarith
  have hone_sub_pos : 0 < 1 - epsilon := by linarith
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    positivity
  have hrho_nonneg : 0 ≤ rho := by
    dsimp [rho]
    exact div_nonneg hone_sub_pos.le heps_den_pos.le
  have hC_nonneg :
      0 ≤ (1 / 4 : ℝ) * rho ^ 2 * (k : ℝ) ^ 2 := by positivity
  have hLpow_le :
      L ^ power ≤
        ((1 / 4 : ℝ) * rho ^ 2 * (k : ℝ) ^ 2) ^ power :=
    pow_le_pow_left₀ hL_nonneg (by simpa [L, rho] using hbase) power
  have hquarter : (1 / 4 : ℝ) ^ power ≤ 1 / 4 :=
    one_div_four_pow_le_one_div_four hpower
  have hrho_mul : rho * (1 + epsilon) = 1 - epsilon := by
    dsimp [rho]
    field_simp [heps_den_pos.ne']
  have hmain_pow :
      ((1 / 4 : ℝ) * rho ^ 2 * (k : ℝ) ^ 2) ^ power *
          (1 + epsilon) ^ (2 * power) =
        (1 / 4 : ℝ) ^ power * (k : ℝ) ^ (2 * power) *
          (1 - epsilon) ^ (2 * power) := by
    calc
      ((1 / 4 : ℝ) * rho ^ 2 * (k : ℝ) ^ 2) ^ power *
          (1 + epsilon) ^ (2 * power)
          =
          (1 / 4 : ℝ) ^ power * (rho ^ 2) ^ power *
              ((k : ℝ) ^ 2) ^ power *
            (1 + epsilon) ^ (2 * power) := by
            rw [mul_pow, mul_pow]
      _ =
          (1 / 4 : ℝ) ^ power * rho ^ (2 * power) *
              (k : ℝ) ^ (2 * power) *
            (1 + epsilon) ^ (2 * power) := by
            rw [← pow_mul, ← pow_mul]
      _ =
          (1 / 4 : ℝ) ^ power * (k : ℝ) ^ (2 * power) *
            (rho ^ (2 * power) * (1 + epsilon) ^ (2 * power)) := by
            ring
      _ =
          (1 / 4 : ℝ) ^ power * (k : ℝ) ^ (2 * power) *
            (1 - epsilon) ^ (2 * power) := by
            rw [← mul_pow, hrho_mul]
      _ =
          (1 / 4 : ℝ) ^ power * (k : ℝ) ^ (2 * power) *
            (1 - epsilon) ^ (2 * power) := rfl
  have hmain_bound :
      L ^ power * (1 + epsilon) ^ (2 * power) ≤
        (1 / 4) * (s : ℝ) * (1 - epsilon) ^ (2 * power) := by
    have hstep :
        L ^ power * (1 + epsilon) ^ (2 * power) ≤
          ((1 / 4 : ℝ) * rho ^ 2 * (k : ℝ) ^ 2) ^ power *
            (1 + epsilon) ^ (2 * power) :=
      mul_le_mul_of_nonneg_right hLpow_le (by positivity)
    have htarget_nonneg : 0 ≤ (1 - epsilon) ^ (2 * power) := by positivity
    calc
      L ^ power * (1 + epsilon) ^ (2 * power)
          ≤ ((1 / 4 : ℝ) * rho ^ 2 * (k : ℝ) ^ 2) ^ power *
            (1 + epsilon) ^ (2 * power) := hstep
      _ = (1 / 4 : ℝ) ^ power * (k : ℝ) ^ (2 * power) *
            (1 - epsilon) ^ (2 * power) := hmain_pow
      _ ≤ (1 / 4 : ℝ) * (s : ℝ) *
            (1 - epsilon) ^ (2 * power) := by
            have hcoeff :
                (1 / 4 : ℝ) ^ power * (k : ℝ) ^ (2 * power) ≤
                  (1 / 4 : ℝ) * (s : ℝ) :=
              mul_le_mul hquarter hkpow_le_s
                (pow_nonneg hk_real_pos.le (2 * power)) (by norm_num)
            exact mul_le_mul_of_nonneg_right hcoeff htarget_nonneg
  have hrho_eps_nonneg : 0 ≤ rho * epsilon := mul_nonneg hrho_nonneg hepsilon_nonneg
  have hrho_eps_le : rho * epsilon ≤ 1 - epsilon := by
    have heps_div_le_one : epsilon / (1 + epsilon) ≤ 1 := by
      rw [div_le_iff₀ heps_den_pos]
      linarith
    have hrho_eps_eq :
        rho * epsilon = (1 - epsilon) * (epsilon / (1 + epsilon)) := by
      dsimp [rho]
      field_simp [heps_den_pos.ne']
    rw [hrho_eps_eq]
    simpa using mul_le_mul_of_nonneg_left heps_div_le_one hone_sub_pos.le
  have hnoise_pow :
      ((1 / 4 : ℝ) * rho ^ 2 * (k : ℝ) ^ 2) ^ power *
          (epsilon / (k : ℝ)) ^ (2 * power) ≤
        (1 / 4) * (1 - epsilon) ^ (2 * power) := by
    have hprod_eq :
        ((1 / 4 : ℝ) * rho ^ 2 * (k : ℝ) ^ 2) ^ power *
            (epsilon / (k : ℝ)) ^ (2 * power) =
          (1 / 4 : ℝ) ^ power *
            (rho * epsilon) ^ (2 * power) := by
      calc
        ((1 / 4 : ℝ) * rho ^ 2 * (k : ℝ) ^ 2) ^ power *
            (epsilon / (k : ℝ)) ^ (2 * power)
            =
            (1 / 4 : ℝ) ^ power * (rho ^ 2) ^ power *
                ((k : ℝ) ^ 2) ^ power *
              (epsilon / (k : ℝ)) ^ (2 * power) := by
              rw [mul_pow, mul_pow]
        _ =
            (1 / 4 : ℝ) ^ power * rho ^ (2 * power) *
                (k : ℝ) ^ (2 * power) *
              (epsilon / (k : ℝ)) ^ (2 * power) := by
              rw [← pow_mul, ← pow_mul]
        _ =
            (1 / 4 : ℝ) ^ power *
              ((rho * (k : ℝ)) ^ (2 * power) *
                (epsilon / (k : ℝ)) ^ (2 * power)) := by
              rw [← mul_pow]
              ring_nf
        _ =
            (1 / 4 : ℝ) ^ power *
              ((rho * (k : ℝ)) * (epsilon / (k : ℝ))) ^ (2 * power) := by
              rw [← mul_pow]
        _ =
            (1 / 4 : ℝ) ^ power * (rho * epsilon) ^ (2 * power) := by
              have hk_cancel :
                  (rho * (k : ℝ)) * (epsilon / (k : ℝ)) = rho * epsilon := by
                field_simp [hk_real_pos.ne']
              rw [hk_cancel]
    rw [hprod_eq]
    have hpow_eps :
        (rho * epsilon) ^ (2 * power) ≤
          (1 - epsilon) ^ (2 * power) :=
      pow_le_pow_left₀ hrho_eps_nonneg hrho_eps_le (2 * power)
    exact
      mul_le_mul hquarter hpow_eps
        (pow_nonneg hrho_eps_nonneg (2 * power)) (by norm_num)
  constructor
  · exact hmain_bound
  · calc
      L ^ power * (epsilon / (k : ℝ)) ^ (2 * power)
          ≤ ((1 / 4 : ℝ) * rho ^ 2 * (k : ℝ) ^ 2) ^ power *
            (epsilon / (k : ℝ)) ^ (2 * power) :=
            mul_le_mul_of_nonneg_right hLpow_le (by positivity)
      _ ≤ (1 / 4) * (1 - epsilon) ^ (2 * power) := hnoise_pow

/--
Candidate-dimension arithmetic for the lower bound.  The extra large-`k`
premise absorbs the additive `+ power - 1` slack in the symmetric-power
coordinate count.
-/
theorem lower_symmetricPower_base_le_of_candidate_dimension_le
    {D k power : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hpower : 0 < power)
    (hepsilon_lt_one : epsilon < 1)
    (hD :
      (D : ℝ) ≤
        (((1 - epsilon) / (1 + epsilon)) ^ 2 /
          (16 * Real.exp 1)) * (power : ℝ) * (k : ℝ) ^ 2)
    (hk_large :
      Real.exp 1 ≤
        (1 / 8) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (k : ℝ) ^ 2) :
    Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) / (power : ℝ) ≤
      (1 / 4) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
        (k : ℝ) ^ 2 := by
  let rho : ℝ := (1 - epsilon) / (1 + epsilon)
  have hpower_real_pos : 0 < (power : ℝ) := by exact_mod_cast hpower
  have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hN_le :
      ((2 * D + power - 1 : ℕ) : ℝ) ≤
        2 * (D : ℝ) + (power : ℝ) := by
    have hnat : 2 * D + power - 1 ≤ 2 * D + power := Nat.sub_le _ _
    exact_mod_cast hnat
  have hbase_le :
      Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) / (power : ℝ) ≤
        Real.exp 1 * (2 * (D : ℝ) + (power : ℝ)) / (power : ℝ) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hN_le hexp_pos.le) hpower_real_pos.le
  have hDterm :
      2 * Real.exp 1 * (D : ℝ) / (power : ℝ) ≤
        (1 / 8) * rho ^ 2 * (k : ℝ) ^ 2 := by
    have hmul :
        2 * Real.exp 1 * (D : ℝ) ≤
          2 * Real.exp 1 *
            ((((1 - epsilon) / (1 + epsilon)) ^ 2 /
              (16 * Real.exp 1)) * (power : ℝ) * (k : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    have hdiv := div_le_div_of_nonneg_right hmul hpower_real_pos.le
    have hsimp :
        2 * Real.exp 1 *
            ((((1 - epsilon) / (1 + epsilon)) ^ 2 /
              (16 * Real.exp 1)) * (power : ℝ) * (k : ℝ) ^ 2) /
            (power : ℝ) =
          (1 / 8) * rho ^ 2 * (k : ℝ) ^ 2 := by
      dsimp [rho]
      field_simp [hexp_pos.ne', hpower_real_pos.ne']
      ring
    calc
      2 * Real.exp 1 * (D : ℝ) / (power : ℝ)
          ≤
            2 * Real.exp 1 *
              ((((1 - epsilon) / (1 + epsilon)) ^ 2 /
                (16 * Real.exp 1)) * (power : ℝ) * (k : ℝ) ^ 2) /
              (power : ℝ) := hdiv
      _ = (1 / 8) * rho ^ 2 * (k : ℝ) ^ 2 := hsimp
  have hslack :
      Real.exp 1 ≤ (1 / 8) * rho ^ 2 * (k : ℝ) ^ 2 := by
    simpa [rho] using hk_large
  have hexpanded :
      Real.exp 1 * (2 * (D : ℝ) + (power : ℝ)) / (power : ℝ) =
        2 * Real.exp 1 * (D : ℝ) / (power : ℝ) + Real.exp 1 := by
    field_simp [hpower_real_pos.ne']
  calc
    Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) / (power : ℝ)
        ≤ Real.exp 1 * (2 * (D : ℝ) + (power : ℝ)) / (power : ℝ) := hbase_le
    _ = 2 * Real.exp 1 * (D : ℝ) / (power : ℝ) + Real.exp 1 := hexpanded
    _ ≤ (1 / 8) * rho ^ 2 * (k : ℝ) ^ 2 +
        (1 / 8) * rho ^ 2 * (k : ℝ) ^ 2 := add_le_add hDterm hslack
    _ = (1 / 4) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
        (k : ℝ) ^ 2 := by
          dsimp [rho]
          ring

/--
Finite linear-recovery lower-bound closeout where the Turán average is
supplied by the source parameter inequality `(4k+1)(s-1) < m`.
-/
theorem false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_exp_card_source_turan
    {m d s k power : ℕ} {epsilon : ℝ} {A B : FeatureMatrix m d}
    (hrec : linearRecoveryCondition A B k epsilon)
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hpower : 0 < power)
    (hdim :
      (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 1 < s)
    (hm : 0 < m)
    (hturan : (((4 * k + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ)) < (m : ℝ)) :
    False :=
  false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_exp_card_coarse_turan
    (A := A) (B := B) (s := s) (k := k) (power := power)
    hrec hk hepsilon_nonneg hepsilon_lt_one hpower hdim hs
    (coarse_turan_average_of_four_mul_add_one_mul_lt
      (m := m) (q := k) (r := s - 1) hm (Nat.sub_pos_of_lt hs) hturan)

/--
Minimum-dimension lower-bound form using source-scale symmetric-power and
source Turán parameter inequalities.
-/
theorem linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_exp_card_source_turan
    {m D s k power : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hpower : 0 < power)
    (hdim :
      (Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs : 1 < s)
    (hm : 0 < m)
    (hturan : (((4 * k + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ)) < (m : ℝ))
    {dmin : ℕ}
    (hvalue : linearCompressedSensingDimensionValue m k epsilon dmin) :
    D < dmin := by
  refine linearCompressedSensingDimensionValue_gt_of_not_feasible_dimension hvalue ?_
  intro hfeas
  rcases hfeas with ⟨A, B, hrec⟩
  exact
    false_of_linearRecoveryCondition_and_symmetricPower_source_parameters_exp_card_source_turan
      (A := A) (B := B) (s := s) (k := k) (power := power)
      hrec hk hepsilon_nonneg hepsilon_lt_one hpower hdim hs hm hturan

/--
Minimum-dimension lower-bound form with the source Turán parameter selected as
`s = floor(m/(4k+1))`.
-/
theorem linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_exp_card_floor_turan
    {m D k power : ℕ} {epsilon : ℝ}
    (hk : 0 < k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hpower : 0 < power)
    (hdim :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      (Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power))
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)))
    (hm : 0 < m)
    {dmin : ℕ}
    (hvalue : linearCompressedSensingDimensionValue m k epsilon dmin) :
    D < dmin := by
  let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
  exact
    linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_exp_card_source_turan
      (m := m) (D := D) (s := s) (k := k) (power := power)
      hk hepsilon_nonneg hepsilon_lt_one hpower (by simpa [s] using hdim)
      (by simpa [s] using hs) hm
      (by
        simpa [s] using
          source_turan_floor_selector_mul_sub_one_lt (m := m) (q := k) hm)
      hvalue

/--
Minimum-dimension lower-bound form with the source Turán selector and the
logarithmic floor-power selector internalized.  The remaining arithmetic
premise is the source-scale base bound on the candidate dimension `D`.
-/
theorem linearCompressedSensingDimensionValue_gt_of_floor_log_power_base_floor_turan
    {m D k : ℕ} {epsilon : ℝ}
    (hk_two : 2 ≤ k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hpower :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      0 < Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ))))
    (hbase :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      let power :=
        Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ)))
      Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) / (power : ℝ) ≤
        (1 / 4) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (k : ℝ) ^ 2)
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)))
    (hm : 0 < m)
    {dmin : ℕ}
    (hvalue : linearCompressedSensingDimensionValue m k epsilon dmin) :
    D < dmin := by
  let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
  let power : ℕ := Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ)))
  have hk_pos : 0 < k := by omega
  have hk_one : 1 < k := by omega
  have hpower_pos : 0 < power := by simpa [s, power] using hpower
  have hs_pos : 0 < s := by omega
  have hs_one : 1 ≤ s := by omega
  have hkpow_le_s : (k : ℝ) ^ (2 * power) ≤ (s : ℝ) := by
    simpa [power] using
      AppliedModelingLib.Math.pow_two_mul_nat_floor_log_div_le
        (k := k) (s := s) hk_one hs_one
  have hsplit :=
    lower_symmetricPower_split_bounds_of_base_le
      (D := D) (s := s) (k := k) (power := power)
      (epsilon := epsilon) hk_pos hpower_pos hepsilon_nonneg hepsilon_lt_one
      hkpow_le_s (by simpa [s, power] using hbase)
  have hdim :
      (Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power *
          ((s : ℝ) * (1 + epsilon) ^ (2 * power) +
            (s : ℝ) * (s : ℝ) *
                (epsilon / (k : ℝ)) ^ (2 * power)) <
        (s : ℝ) ^ 2 * (1 - epsilon) ^ (2 * power) :=
    lower_symmetricPower_hdim_of_split_bounds
      (D := D) (s := s) (k := k) (power := power)
      (epsilon := epsilon) hs_pos hepsilon_lt_one hsplit.1 hsplit.2
  exact
    linearCompressedSensingDimensionValue_gt_of_symmetricPower_source_parameters_exp_card_floor_turan
      (m := m) (D := D) (k := k) (power := power)
      hk_pos hepsilon_nonneg hepsilon_lt_one hpower_pos
      (by simpa [s, power] using hdim) (by simpa [s] using hs) hm hvalue

/--
Minimum-dimension lower-bound form with the source finite selectors and a
clean candidate-dimension upper bound.
-/
theorem linearCompressedSensingDimensionValue_gt_of_floor_log_power_candidate_floor_turan
    {m D k : ℕ} {epsilon : ℝ}
    (hk_two : 2 ≤ k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hpower :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      0 < Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ))))
    (hD :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      let power :=
        Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ)))
      (D : ℝ) ≤
        (((1 - epsilon) / (1 + epsilon)) ^ 2 /
          (16 * Real.exp 1)) * (power : ℝ) * (k : ℝ) ^ 2)
    (hk_large :
      Real.exp 1 ≤
        (1 / 8) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (k : ℝ) ^ 2)
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)))
    (hm : 0 < m)
    {dmin : ℕ}
    (hvalue : linearCompressedSensingDimensionValue m k epsilon dmin) :
    D < dmin := by
  let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
  let power : ℕ := Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ)))
  have hk_pos : 0 < k := by omega
  have hpower_pos : 0 < power := by simpa [s, power] using hpower
  have hbase :
      Real.exp 1 * ((2 * D + power - 1 : ℕ) : ℝ) / (power : ℝ) ≤
        (1 / 4) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (k : ℝ) ^ 2 :=
    lower_symmetricPower_base_le_of_candidate_dimension_le
      (D := D) (k := k) (power := power) (epsilon := epsilon)
      hk_pos hpower_pos hepsilon_lt_one (by simpa [s, power] using hD) hk_large
  exact
    linearCompressedSensingDimensionValue_gt_of_floor_log_power_base_floor_turan
      (m := m) (D := D) (k := k) (epsilon := epsilon)
      hk_two hepsilon_nonneg hepsilon_lt_one hpower
      (by simpa [s, power] using hbase) hs hm hvalue

/--
Source-regime arithmetic for Theorem `thm:lower`: the paper's
`epsilon > k^(3/2) sqrt(5) / sqrt(m)` condition, squared and written as
`5 k^3 < epsilon^2 m`, implies the Turán floor selector is at least `k^2`
when `0 <= epsilon < 1`.
-/
theorem source_lower_floor_selector_sq_le
    {m k : ℕ} {epsilon : ℝ}
    (hk : 1 ≤ k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hregime : 5 * (k : ℝ) ^ 3 < epsilon ^ 2 * (m : ℝ)) :
    (k : ℝ) ^ 2 ≤
      (Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)) : ℝ) := by
  have hepsilon_sq_lt_one : epsilon ^ 2 < 1 := by
    nlinarith [sq_nonneg epsilon]
  have hfive_lt_m : 5 * (k : ℝ) ^ 3 < (m : ℝ) := by
    have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    have hle : epsilon ^ 2 * (m : ℝ) ≤ 1 * (m : ℝ) :=
      mul_le_mul_of_nonneg_right hepsilon_sq_lt_one.le hm_nonneg
    nlinarith
  have hcoef :
      (((4 * k + 1 : ℕ) : ℝ) * (k : ℝ) ^ 2) ≤
        5 * (k : ℝ) ^ 3 := by
    have hk_real : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    norm_num
    nlinarith
  have hmul_lt :
      (((4 * k + 1 : ℕ) : ℝ) * (k : ℝ) ^ 2) < (m : ℝ) :=
    lt_of_le_of_lt hcoef hfive_lt_m
  have hmul_nat :
      (((4 * k + 1 : ℕ) : ℝ) * ((k ^ 2 : ℕ) : ℝ)) < (m : ℝ) := by
    simpa [pow_two] using hmul_lt
  have hfloor_nat :
      k ^ 2 ≤ Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)) :=
    AppliedModelingLib.Math.nat_le_floor_div_of_mul_lt
      (m := m) (a := 4 * k + 1) (n := k ^ 2) (by omega) hmul_nat
  exact_mod_cast hfloor_nat

/--
The source lower-bound regime makes the Turán floor selector nontrivial.
-/
theorem source_lower_floor_selector_one_lt
    {m k : ℕ} {epsilon : ℝ}
    (hk_two : 2 ≤ k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hregime : 5 * (k : ℝ) ^ 3 < epsilon ^ 2 * (m : ℝ)) :
    1 < Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)) := by
  have hsq :=
    source_lower_floor_selector_sq_le
      (m := m) (k := k) (epsilon := epsilon)
      (by omega) hepsilon_nonneg hepsilon_lt_one hregime
  have hksq_gt_one : 1 < k ^ 2 := by
    have hk_real : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
    have hreal : (1 : ℝ) < ((k ^ 2 : ℕ) : ℝ) := by
      have hcast : ((k ^ 2 : ℕ) : ℝ) = (k : ℝ) ^ 2 := by
        norm_num [pow_two]
      nlinarith
    exact_mod_cast hreal
  have hsq_nat :
      k ^ 2 ≤ Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hsq
  exact lt_of_lt_of_le hksq_gt_one hsq_nat

/--
The source lower-bound regime makes the logarithmic floor-power selector
positive.
-/
theorem source_lower_floor_log_power_pos
    {m k : ℕ} {epsilon : ℝ}
    (hk_two : 2 ≤ k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hregime : 5 * (k : ℝ) ^ 3 < epsilon ^ 2 * (m : ℝ)) :
    0 <
      Nat.floor
        (Real.log
            (Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)) : ℝ) /
          (2 * Real.log (k : ℝ))) := by
  have hsq :=
    source_lower_floor_selector_sq_le
      (m := m) (k := k) (epsilon := epsilon)
      (by omega) hepsilon_nonneg hepsilon_lt_one hregime
  have hone :
      1 ≤
        Nat.floor
          (Real.log
              (Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)) : ℝ) /
            (2 * Real.log (k : ℝ))) :=
    AppliedModelingLib.Math.one_le_nat_floor_log_div_of_sq_le
      (k := k)
      (s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)))
      (by omega) hsq
  exact lt_of_lt_of_le Nat.zero_lt_one hone

/--
Theorem `thm:lower`, finite selected lower-bound witness with the source
regime deriving the floor-selector side conditions.
-/
theorem linearCompressedSensingDimensionValue_gt_of_floor_log_power_candidate_source_regime
    {m D k : ℕ} {epsilon : ℝ}
    (hk_two : 2 ≤ k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hregime : 5 * (k : ℝ) ^ 3 < epsilon ^ 2 * (m : ℝ))
    (hD :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      let power :=
        Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ)))
      (D : ℝ) ≤
        (((1 - epsilon) / (1 + epsilon)) ^ 2 /
          (16 * Real.exp 1)) * (power : ℝ) * (k : ℝ) ^ 2)
    (hk_large :
      Real.exp 1 ≤
        (1 / 8) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (k : ℝ) ^ 2)
    {dmin : ℕ}
    (hvalue : linearCompressedSensingDimensionValue m k epsilon dmin) :
    D < dmin := by
  have hpower :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      0 < Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ))) := by
    simpa using
      source_lower_floor_log_power_pos
        (m := m) (k := k) (epsilon := epsilon)
        hk_two hepsilon_nonneg hepsilon_lt_one hregime
  have hs :
      1 < Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)) :=
    source_lower_floor_selector_one_lt
      (m := m) (k := k) (epsilon := epsilon)
      hk_two hepsilon_nonneg hepsilon_lt_one hregime
  have hm_real : 0 < (m : ℝ) := by
    have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hleft_pos : 0 < 5 * (k : ℝ) ^ 3 := by positivity
    have hprod_pos : 0 < epsilon ^ 2 * (m : ℝ) :=
      lt_trans hleft_pos hregime
    have hepsilon_sq_nonneg : 0 ≤ epsilon ^ 2 := sq_nonneg epsilon
    have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hm : 0 < m := by exact_mod_cast hm_real
  exact
    linearCompressedSensingDimensionValue_gt_of_floor_log_power_candidate_floor_turan
      (m := m) (D := D) (k := k) (epsilon := epsilon)
      hk_two hepsilon_nonneg hepsilon_lt_one hpower hD hk_large hs hm hvalue

/--
Theorem `thm:lower`, real-valued minimum-dimension lower bound for the finite
source-selected Turán and logarithmic power parameters.
-/
theorem linearCompressedSensingDimensionValue_real_gt_floor_log_power_candidate_source_regime
    {m k dmin : ℕ} {epsilon : ℝ}
    (hk_two : 2 ≤ k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hregime : 5 * (k : ℝ) ^ 3 < epsilon ^ 2 * (m : ℝ))
    (hk_large :
      Real.exp 1 ≤
        (1 / 8) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (k : ℝ) ^ 2)
    (hvalue : linearCompressedSensingDimensionValue m k epsilon dmin) :
    ((((1 - epsilon) / (1 + epsilon)) ^ 2 /
        (16 * Real.exp 1)) *
      (Nat.floor
        (Real.log
            (Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)) : ℝ) /
          (2 * Real.log (k : ℝ))) : ℝ) *
      (k : ℝ) ^ 2) < (dmin : ℝ) := by
  by_contra hnot
  have hD :
      let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
      let power :=
        Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ)))
      (dmin : ℝ) ≤
        (((1 - epsilon) / (1 + epsilon)) ^ 2 /
          (16 * Real.exp 1)) * (power : ℝ) * (k : ℝ) ^ 2 := by
    simpa using le_of_not_gt hnot
  have hlt :
      dmin < dmin :=
    linearCompressedSensingDimensionValue_gt_of_floor_log_power_candidate_source_regime
      (m := m) (D := dmin) (k := k) (epsilon := epsilon)
      hk_two hepsilon_nonneg hepsilon_lt_one hregime hD hk_large hvalue
  exact (Nat.lt_irrefl dmin) hlt

/--
Theorem `thm:lower`, logarithmic finite lower-bound envelope.  This packages
the source choice `power = floor(log s / (2 log k))` into an explicit
constant-fraction lower bound in terms of `log s / log k`, where
`s = floor(m/(4k+1))`.
-/
theorem linearCompressedSensingDimensionValue_real_gt_log_floor_selector_source_regime
    {m k dmin : ℕ} {epsilon : ℝ}
    (hk_two : 2 ≤ k) (hepsilon_nonneg : 0 ≤ epsilon)
    (hepsilon_lt_one : epsilon < 1)
    (hregime : 5 * (k : ℝ) ^ 3 < epsilon ^ 2 * (m : ℝ))
    (hk_large :
      Real.exp 1 ≤
        (1 / 8) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (k : ℝ) ^ 2)
    (hvalue : linearCompressedSensingDimensionValue m k epsilon dmin) :
    ((((1 - epsilon) / (1 + epsilon)) ^ 2 /
        (64 * Real.exp 1)) *
      (k : ℝ) ^ 2 *
      (Real.log
          (Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)) : ℝ) /
        Real.log (k : ℝ))) < (dmin : ℝ) := by
  let s := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
  let power : ℕ := Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ)))
  let c : ℝ := ((1 - epsilon) / (1 + epsilon)) ^ 2 / (16 * Real.exp 1)
  have hreal :
      c * (power : ℝ) * (k : ℝ) ^ 2 < (dmin : ℝ) := by
    simpa [s, power, c] using
      linearCompressedSensingDimensionValue_real_gt_floor_log_power_candidate_source_regime
        (m := m) (k := k) (dmin := dmin) (epsilon := epsilon)
        hk_two hepsilon_nonneg hepsilon_lt_one hregime hk_large hvalue
  have hsq :
      (k : ℝ) ^ 2 ≤ (s : ℝ) := by
    simpa [s] using
      source_lower_floor_selector_sq_le
        (m := m) (k := k) (epsilon := epsilon)
        (by omega) hepsilon_nonneg hepsilon_lt_one hregime
  have hpower_lower :
      Real.log (s : ℝ) / (4 * Real.log (k : ℝ)) ≤ (power : ℝ) := by
    simpa [power] using
      AppliedModelingLib.Math.half_log_div_le_nat_floor_log_div_of_sq_le
        (k := k) (s := s) (by omega : 1 < k) hsq
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hk_sq_nonneg : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
  have hscaled :
      c * (Real.log (s : ℝ) / (4 * Real.log (k : ℝ))) *
          (k : ℝ) ^ 2 ≤
        c * (power : ℝ) * (k : ℝ) ^ 2 := by
    have hleft :=
      mul_le_mul_of_nonneg_left hpower_lower hc_nonneg
    have hright :=
      mul_le_mul_of_nonneg_right hleft hk_sq_nonneg
    simpa [mul_assoc, mul_comm, mul_left_comm] using hright
  have htarget_le :
      ((((1 - epsilon) / (1 + epsilon)) ^ 2 /
          (64 * Real.exp 1)) *
        (k : ℝ) ^ 2 *
        (Real.log (s : ℝ) / Real.log (k : ℝ))) ≤
        c * (power : ℝ) * (k : ℝ) ^ 2 := by
    calc
      (((1 - epsilon) / (1 + epsilon)) ^ 2 /
          (64 * Real.exp 1)) *
        (k : ℝ) ^ 2 *
        (Real.log (s : ℝ) / Real.log (k : ℝ)) =
          c * (Real.log (s : ℝ) / (4 * Real.log (k : ℝ))) *
            (k : ℝ) ^ 2 := by
            dsimp [c]
            ring
      _ ≤ c * (power : ℝ) * (k : ℝ) ^ 2 := hscaled
  exact lt_of_le_of_lt (by simpa [s] using htarget_le) hreal

/--
In the source lower-bound regime, the floor-log scale is nonnegative.
-/
theorem linearCompressedSensingLowerFloorLogScale_nonneg_of_source_regime
    {epsilon : ℝ} {p : ℕ × ℕ}
    (hsource : linearCompressedSensingLowerSourceRegime epsilon p) :
    0 ≤ linearCompressedSensingLowerFloorLogScale p := by
  rcases p with ⟨m, k⟩
  rcases hsource with
    ⟨hk_two, hepsilon_nonneg, hepsilon_lt_one, hregime⟩
  let s : ℕ := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
  have hsq : (k : ℝ) ^ 2 ≤ (s : ℝ) := by
    simpa [s] using
      source_lower_floor_selector_sq_le
        (m := m) (k := k) (epsilon := epsilon)
        (by omega : 1 ≤ k) hepsilon_nonneg hepsilon_lt_one hregime
  have hk_real_one : (1 : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ k)
  have hk_sq_one : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
    nlinarith
  have hs_one : (1 : ℝ) ≤ (s : ℝ) :=
    le_trans hk_sq_one hsq
  have hlogs_nonneg : 0 ≤ Real.log (s : ℝ) :=
    Real.log_nonneg hs_one
  have hlogk_pos : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hratio_nonneg :
      0 ≤ Real.log (s : ℝ) / Real.log (k : ℝ) :=
    div_nonneg hlogs_nonneg hlogk_pos.le
  exact
    mul_nonneg (sq_nonneg (k : ℝ)) hratio_nonneg

/--
In the source lower-bound regime and for large enough `k`, the printed
`log(m/k)` scale is controlled by a constant multiple of the floor-log scale
that comes directly out of the rank/Turán proof.
-/
theorem linearCompressedSensingLowerSourceLogScale_le_two_floor_logScale
    {epsilon : ℝ} {m k : ℕ}
    (hk_four : 4 ≤ k)
    (hsource : linearCompressedSensingLowerSourceRegime epsilon (m, k)) :
    linearCompressedSensingLowerSourceLogScale (m, k) ≤
      2 * linearCompressedSensingLowerFloorLogScale (m, k) := by
  rcases hsource with
    ⟨hk_two, hepsilon_nonneg, hepsilon_lt_one, hregime⟩
  let s : ℕ := Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ))
  have hsq : (k : ℝ) ^ 2 ≤ (s : ℝ) := by
    simpa [s] using
      source_lower_floor_selector_sq_le
        (m := m) (k := k) (epsilon := epsilon)
        (by omega : 1 ≤ k) hepsilon_nonneg hepsilon_lt_one hregime
  have hk_real_pos : 0 < (k : ℝ) := by
    exact_mod_cast (by omega : 0 < k)
  have hk_log_pos : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hk_sq_ge_sixteen : (16 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have hk_four_real : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_four
    nlinarith
  have hs_ten : (10 : ℝ) ≤ (s : ℝ) :=
    le_trans (by norm_num : (10 : ℝ) ≤ 16) (le_trans hk_sq_ge_sixteen hsq)
  have hs_one : (1 : ℝ) ≤ (s : ℝ) :=
    le_trans (by norm_num : (1 : ℝ) ≤ 10) hs_ten
  have hs_pos : 0 < (s : ℝ) := lt_of_lt_of_le zero_lt_one hs_one
  have hm_pos : 0 < (m : ℝ) := by
    have hleft_pos : 0 < 5 * (k : ℝ) ^ 3 := by positivity
    have hprod_pos : 0 < epsilon ^ 2 * (m : ℝ) :=
      lt_trans hleft_pos hregime
    have hepsilon_sq_nonneg : 0 ≤ epsilon ^ 2 := sq_nonneg epsilon
    have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hden_pos : 0 < (((4 * k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 0 < 4 * k + 1)
  have hcoef_le :
      (((4 * k + 1 : ℕ) : ℝ) / (k : ℝ)) ≤ 5 := by
    rw [div_le_iff₀ hk_real_pos]
    norm_num
    have hk_one_real : (1 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ k)
    nlinarith
  have hfloor_upper :
      (m : ℝ) / (((4 * k + 1 : ℕ) : ℝ)) ≤ (s : ℝ) + 1 := by
    exact le_of_lt (by
      simpa [s] using
        Nat.lt_floor_add_one
          ((m : ℝ) / (((4 * k + 1 : ℕ) : ℝ))))
  have hfloor_arg_nonneg :
      0 ≤ (m : ℝ) / (((4 * k + 1 : ℕ) : ℝ)) :=
    div_nonneg hm_pos.le hden_pos.le
  have hcoef_nonneg :
      0 ≤ (((4 * k + 1 : ℕ) : ℝ) / (k : ℝ)) :=
    div_nonneg hden_pos.le hk_real_pos.le
  have hmul_bound :
      (((4 * k + 1 : ℕ) : ℝ) / (k : ℝ)) *
          ((m : ℝ) / (((4 * k + 1 : ℕ) : ℝ))) ≤
        5 * ((s : ℝ) + 1) :=
    mul_le_mul hcoef_le hfloor_upper hfloor_arg_nonneg
      (by norm_num : (0 : ℝ) ≤ 5)
  have hm_div_decomp :
      (m : ℝ) / (k : ℝ) =
        (((4 * k + 1 : ℕ) : ℝ) / (k : ℝ)) *
          ((m : ℝ) / (((4 * k + 1 : ℕ) : ℝ))) := by
    field_simp [hk_real_pos.ne', hden_pos.ne']
  have hm_div_le_ten_s :
      (m : ℝ) / (k : ℝ) ≤ 10 * (s : ℝ) := by
    calc
      (m : ℝ) / (k : ℝ) =
          (((4 * k + 1 : ℕ) : ℝ) / (k : ℝ)) *
            ((m : ℝ) / (((4 * k + 1 : ℕ) : ℝ))) := hm_div_decomp
      _ ≤ 5 * ((s : ℝ) + 1) := hmul_bound
      _ ≤ 10 * (s : ℝ) := by nlinarith [hs_one]
  have hten_s_le_sq : 10 * (s : ℝ) ≤ (s : ℝ) ^ 2 := by
    nlinarith [hs_ten]
  have hm_div_le_sq :
      (m : ℝ) / (k : ℝ) ≤ (s : ℝ) ^ 2 :=
    le_trans hm_div_le_ten_s hten_s_le_sq
  have hm_div_pos : 0 < (m : ℝ) / (k : ℝ) :=
    div_pos hm_pos hk_real_pos
  have hlog_le_sq :
      Real.log ((m : ℝ) / (k : ℝ)) ≤ Real.log ((s : ℝ) ^ 2) :=
    Real.log_le_log hm_div_pos hm_div_le_sq
  have hlog_sq :
      Real.log ((s : ℝ) ^ 2) = 2 * Real.log (s : ℝ) := by
    rw [Real.log_pow]
    norm_num
  have hlog_le :
      Real.log ((m : ℝ) / (k : ℝ)) ≤ 2 * Real.log (s : ℝ) := by
    simpa [hlog_sq] using hlog_le_sq
  have hratio_le :
      Real.log ((m : ℝ) / (k : ℝ)) / Real.log (k : ℝ) ≤
        2 * (Real.log (s : ℝ) / Real.log (k : ℝ)) := by
    calc
      Real.log ((m : ℝ) / (k : ℝ)) / Real.log (k : ℝ)
          ≤ (2 * Real.log (s : ℝ)) / Real.log (k : ℝ) :=
            div_le_div_of_nonneg_right hlog_le hk_log_pos.le
      _ = 2 * (Real.log (s : ℝ) / Real.log (k : ℝ)) := by ring
  have hscaled :=
    mul_le_mul_of_nonneg_left hratio_le (sq_nonneg (k : ℝ))
  simpa [linearCompressedSensingLowerSourceLogScale,
    linearCompressedSensingLowerFloorLogScale, s, mul_assoc, mul_comm,
    mul_left_comm] using hscaled

/--
In the source lower-bound regime, the printed lower-bound scale is eventually
nonnegative.
-/
theorem linearCompressedSensingLowerSourceLogScale_eventually_nonneg
    {epsilon : ℝ} :
    ∀ᶠ p in linearCompressedSensingLowerSourceFilter epsilon,
      0 ≤ linearCompressedSensingLowerSourceLogScale p := by
  rw [linearCompressedSensingLowerSourceFilter]
  exact eventually_inf_principal.2 <| by
    refine eventually_atTop.2 ⟨(0, 4), ?_⟩
    intro p hp hsource
    rcases p with ⟨m, k⟩
    rcases hsource with
      ⟨_hk_two, hepsilon_nonneg, hepsilon_lt_one, hregime⟩
    have hk_four : 4 ≤ k := hp.2
    have hk_real_pos : 0 < (k : ℝ) := by
      exact_mod_cast (by omega : 0 < k)
    have hm_pos : 0 < (m : ℝ) := by
      have hleft_pos : 0 < 5 * (k : ℝ) ^ 3 := by positivity
      have hprod_pos : 0 < epsilon ^ 2 * (m : ℝ) :=
        lt_trans hleft_pos hregime
      have hepsilon_sq_nonneg : 0 ≤ epsilon ^ 2 := sq_nonneg epsilon
      have hm_nonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith
    have hsq :
        (k : ℝ) ^ 2 ≤
          (Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)) : ℝ) :=
      source_lower_floor_selector_sq_le
        (m := m) (k := k) (epsilon := epsilon)
        (by omega : 1 ≤ k) hepsilon_nonneg hepsilon_lt_one hregime
    have hm_ge_k : (k : ℝ) ≤ (m : ℝ) := by
      have hk_sq_ge_k : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
        nlinarith [show (1 : ℝ) ≤ (k : ℝ) by exact_mod_cast (by omega : 1 ≤ k)]
      have hfloor_le_arg :
          (Nat.floor ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)) : ℝ) ≤
            (m : ℝ) / ((4 * k + 1 : ℕ) : ℝ) :=
        Nat.floor_le (div_nonneg hm_pos.le
          (by exact_mod_cast (by omega : 0 ≤ 4 * k + 1)))
      have hdiv_ge_k : (k : ℝ) ≤ (m : ℝ) / ((4 * k + 1 : ℕ) : ℝ) :=
        le_trans hk_sq_ge_k (le_trans hsq hfloor_le_arg)
      have hden_pos : 0 < (((4 * k + 1 : ℕ) : ℝ)) := by
        exact_mod_cast (by omega : 0 < 4 * k + 1)
      have hden_ge_one : (1 : ℝ) ≤ (((4 * k + 1 : ℕ) : ℝ)) := by
        exact_mod_cast (by omega : 1 ≤ 4 * k + 1)
      have hmul := (le_div_iff₀ hden_pos).1 hdiv_ge_k
      nlinarith
    have hratio_ge_one : (1 : ℝ) ≤ (m : ℝ) / (k : ℝ) := by
      rw [le_div_iff₀ hk_real_pos]
      simpa using hm_ge_k
    have hlog_nonneg : 0 ≤ Real.log ((m : ℝ) / (k : ℝ)) :=
      Real.log_nonneg hratio_ge_one
    have hlogk_pos : 0 < Real.log (k : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    have hratio_nonneg :
        0 ≤ Real.log ((m : ℝ) / (k : ℝ)) / Real.log (k : ℝ) :=
      div_nonneg hlog_nonneg hlogk_pos.le
    exact mul_nonneg (sq_nonneg (k : ℝ)) hratio_nonneg

/--
The printed lower-bound scale is Big-O of the finite floor-log scale along
the source lower-bound regime.
-/
theorem linearCompressedSensingLowerSourceLogScale_isBigO_floor_log_source_regime
    {epsilon : ℝ} :
    Asymptotics.IsBigO
      (linearCompressedSensingLowerSourceFilter epsilon)
      linearCompressedSensingLowerSourceLogScale
      linearCompressedSensingLowerFloorLogScale := by
  refine AppliedModelingLib.Math.isBigO_of_eventually_nonneg_le_const_mul
    (C := 2) (by norm_num) ?_ ?_ ?_
  · exact linearCompressedSensingLowerSourceLogScale_eventually_nonneg
  · rw [linearCompressedSensingLowerSourceFilter]
    exact eventually_inf_principal.2 <| by
      filter_upwards with p hsource
      exact linearCompressedSensingLowerFloorLogScale_nonneg_of_source_regime hsource
  · rw [linearCompressedSensingLowerSourceFilter]
    exact eventually_inf_principal.2 <| by
      refine eventually_atTop.2 ⟨(0, 4), ?_⟩
      intro p hp hsource
      rcases p with ⟨m, k⟩
      exact
        linearCompressedSensingLowerSourceLogScale_le_two_floor_logScale
          (epsilon := epsilon) (m := m) (k := k) hp.2 hsource

/--
For fixed `0 < epsilon < 1`, the large-`k` side condition used by the finite
lower-bound proof is eventually true.
-/
theorem linearCompressedSensingLowerFiniteLargeK_eventually_atTop
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    ∀ᶠ p : ℕ × ℕ in Filter.atTop,
      Real.exp 1 ≤
        (1 / 8) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (p.2 : ℝ) ^ 2 := by
  let a : ℝ := (1 / 8) * ((1 - epsilon) / (1 + epsilon)) ^ 2
  have ha_pos : 0 < a := by
    have hone_sub_pos : 0 < 1 - epsilon := by linarith
    have hone_add_pos : 0 < 1 + epsilon := by linarith
    dsimp [a]
    positivity
  rcases exists_nat_gt (max (1 : ℝ) (Real.exp 1 / a)) with ⟨N, hN⟩
  refine eventually_atTop.2 ⟨(0, N), ?_⟩
  intro p hp
  have hN_le_k : (N : ℝ) ≤ (p.2 : ℝ) := by
    exact_mod_cast hp.2
  have hdiv_le_max :
      Real.exp 1 / a ≤ max (1 : ℝ) (Real.exp 1 / a) :=
    le_max_right _ _
  have hmax_le_N : max (1 : ℝ) (Real.exp 1 / a) ≤ (N : ℝ) :=
    le_of_lt hN
  have hone_le_k : (1 : ℝ) ≤ (p.2 : ℝ) := by
    have hone_le_max : (1 : ℝ) ≤ max (1 : ℝ) (Real.exp 1 / a) :=
      le_max_left _ _
    linarith
  have hk_le_sq : (p.2 : ℝ) ≤ (p.2 : ℝ) ^ 2 := by
    nlinarith
  have hdiv_le_sq : Real.exp 1 / a ≤ (p.2 : ℝ) ^ 2 := by
    linarith
  have hmul : Real.exp 1 ≤ (p.2 : ℝ) ^ 2 * a := by
    exact (div_le_iff₀ ha_pos).1 hdiv_le_sq
  calc
    Real.exp 1 ≤ (p.2 : ℝ) ^ 2 * a := hmul
    _ = a * (p.2 : ℝ) ^ 2 := by ring
    _ =
        (1 / 8) * ((1 - epsilon) / (1 + epsilon)) ^ 2 *
          (p.2 : ℝ) ^ 2 := by rfl

/--
Theorem `thm:lower`, Landau wrapper for the finite lower-bound envelope proved
above.  Along the source lower-bound regime, the floor-log scale from the
rank/Turán proof is Big-O of the minimum feasible linear compressed-sensing
dimension, which is the formal `Omega_epsilon` direction.
-/
theorem linearCompressedSensingDimension_isBigO_lower_floor_log_source_regime
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    Asymptotics.IsBigO
      (linearCompressedSensingLowerSourceFilter epsilon)
      linearCompressedSensingLowerFloorLogScale
      (fun p : ℕ × ℕ =>
        (linearCompressedSensingDimension p.1 p.2 epsilon : ℝ)) := by
  let c : ℝ :=
    ((1 - epsilon) / (1 + epsilon)) ^ 2 / (64 * Real.exp 1)
  have hc_pos : 0 < c := by
    have hone_sub_pos : 0 < 1 - epsilon := by linarith
    have hone_add_pos : 0 < 1 + epsilon := by linarith
    dsimp [c]
    positivity
  refine AppliedModelingLib.Math.isBigO_of_eventually_pos_mul_le
    (c := c) hc_pos ?_ ?_ ?_
  · rw [linearCompressedSensingLowerSourceFilter]
    exact eventually_inf_principal.2 <| by
      filter_upwards with p hsource
      exact linearCompressedSensingLowerFloorLogScale_nonneg_of_source_regime hsource
  · filter_upwards with p
    exact Nat.cast_nonneg _
  · rw [linearCompressedSensingLowerSourceFilter]
    exact eventually_inf_principal.2 <| by
      filter_upwards
        [linearCompressedSensingLowerFiniteLargeK_eventually_atTop
          hepsilon_pos hepsilon_lt_one] with p hk_large hsource
      rcases p with ⟨m, k⟩
      rcases hsource with
        ⟨hk_two, hepsilon_nonneg, hepsilon_lt_one', hregime⟩
      have hvalue :
          linearCompressedSensingDimensionValue m k epsilon
            (linearCompressedSensingDimension m k epsilon) :=
        linearCompressedSensingDimension_spec m k hepsilon_pos
      have hlt :
          c *
            ((k : ℝ) ^ 2 *
              (Real.log
                  (Nat.floor
                    ((m : ℝ) / ((4 * k + 1 : ℕ) : ℝ)) : ℝ) /
                Real.log (k : ℝ))) <
            (linearCompressedSensingDimension m k epsilon : ℝ) := by
        simpa [c, mul_assoc] using
          linearCompressedSensingDimensionValue_real_gt_log_floor_selector_source_regime
            (m := m) (k := k)
            (dmin := linearCompressedSensingDimension m k epsilon)
            (epsilon := epsilon)
            hk_two hepsilon_nonneg hepsilon_lt_one' hregime hk_large hvalue
      exact le_of_lt (by
        simpa [linearCompressedSensingLowerFloorLogScale, c] using hlt)

/--
Theorem `thm:lower`, source-scale Landau lower-bound wrapper: along the
source lower-bound regime, the printed scale
`(k^2 / log k) * log(m/k)` is Big-O of the minimum feasible linear
compressed-sensing dimension.
-/
theorem linearCompressedSensingDimension_isBigO_lower_source_log_source_regime
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    Asymptotics.IsBigO
      (linearCompressedSensingLowerSourceFilter epsilon)
      linearCompressedSensingLowerSourceLogScale
      (fun p : ℕ × ℕ =>
        (linearCompressedSensingDimension p.1 p.2 epsilon : ℝ)) :=
  (linearCompressedSensingLowerSourceLogScale_isBigO_floor_log_source_regime
    (epsilon := epsilon)).trans
      (linearCompressedSensingDimension_isBigO_lower_floor_log_source_regime
        hepsilon_pos hepsilon_lt_one)

/--
Threshold symmetric-power arithmetic: a base bound at scale `q^2` makes the
Stirling-style coordinate-count envelope smaller than the selected source
subset size `q^(2*power)`.
-/
theorem threshold_symmetricPower_hdim_of_base_le_q_pow
    {d q power : ℕ}
    (hq : 0 < q) (hpower : 0 < power)
    (hbase :
      Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ) ≤
        (1 / 4) * (q : ℝ) ^ 2) :
    2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power <
      (q : ℝ) ^ (2 * power) := by
  let base : ℝ :=
    Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) / (power : ℝ)
  have hbase_nonneg : 0 ≤ base := by
    dsimp [base]
    positivity
  have hpow_le :
      base ^ power ≤ ((1 / 4 : ℝ) * (q : ℝ) ^ 2) ^ power :=
    pow_le_pow_left₀ hbase_nonneg (by simpa [base] using hbase) power
  have htarget :
      ((1 / 4 : ℝ) * (q : ℝ) ^ 2) ^ power =
        (1 / 4 : ℝ) ^ power * (q : ℝ) ^ (2 * power) := by
    rw [mul_pow, pow_mul]
  have hpow_le' :
      base ^ power ≤
        (1 / 4 : ℝ) ^ power * (q : ℝ) ^ (2 * power) := by
    calc
      base ^ power ≤ ((1 / 4 : ℝ) * (q : ℝ) ^ 2) ^ power := hpow_le
      _ = (1 / 4 : ℝ) ^ power * (q : ℝ) ^ (2 * power) := htarget
  have hquarter : (1 / 4 : ℝ) ^ power ≤ 1 / 4 :=
    one_div_four_pow_le_one_div_four hpower
  have hfactor_lt : 2 * ((1 / 4 : ℝ) ^ power) < 1 := by
    nlinarith
  have hq_real_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqpow_pos : 0 < (q : ℝ) ^ (2 * power) := pow_pos hq_real_pos _
  calc
    2 * base ^ power
        ≤ 2 * ((1 / 4 : ℝ) ^ power * (q : ℝ) ^ (2 * power)) := by
          exact mul_le_mul_of_nonneg_left hpow_le' (by norm_num)
    _ = (2 * ((1 / 4 : ℝ) ^ power)) *
          (q : ℝ) ^ (2 * power) := by ring
    _ < 1 * (q : ℝ) ^ (2 * power) :=
          mul_lt_mul_of_pos_right hfactor_lt hqpow_pos
    _ = (q : ℝ) ^ (2 * power) := by ring

/--
Candidate-dimension arithmetic for the threshold and activation/bias lower
bounds.  The extra large-`q` premise absorbs the additive `+ power - 1` slack
in the symmetric-power coordinate count.
-/
theorem threshold_symmetricPower_base_le_of_candidate_dimension_le
    {d q power : ℕ}
    (hq : 0 < q) (hpower : 0 < power)
    (hD :
      (d : ℝ) ≤ (1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2)
    (hq_large :
      Real.exp 1 ≤ (1 / 8) * (q : ℝ) ^ 2) :
    Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) / (power : ℝ) ≤
      (1 / 4) * (q : ℝ) ^ 2 := by
  have hpower_real_pos : 0 < (power : ℝ) := by exact_mod_cast hpower
  have hexp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hN_le :
      ((2 * d + power - 1 : ℕ) : ℝ) ≤
        2 * (d : ℝ) + (power : ℝ) := by
    have hnat : 2 * d + power - 1 ≤ 2 * d + power := Nat.sub_le _ _
    exact_mod_cast hnat
  have hbase_le :
      Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) / (power : ℝ) ≤
        Real.exp 1 * (2 * (d : ℝ) + (power : ℝ)) / (power : ℝ) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hN_le hexp_pos.le) hpower_real_pos.le
  have hDterm :
      2 * Real.exp 1 * (d : ℝ) / (power : ℝ) ≤
        (1 / 8) * (q : ℝ) ^ 2 := by
    have hmul :
        2 * Real.exp 1 * (d : ℝ) ≤
          2 * Real.exp 1 *
            ((1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    have hdiv := div_le_div_of_nonneg_right hmul hpower_real_pos.le
    have hsimp :
        2 * Real.exp 1 *
            ((1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2) /
            (power : ℝ) =
          (1 / 8) * (q : ℝ) ^ 2 := by
      field_simp [hexp_pos.ne', hpower_real_pos.ne']
      ring
    calc
      2 * Real.exp 1 * (d : ℝ) / (power : ℝ)
          ≤
            2 * Real.exp 1 *
              ((1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2) /
              (power : ℝ) := hdiv
      _ = (1 / 8) * (q : ℝ) ^ 2 := hsimp
  have hexpanded :
      Real.exp 1 * (2 * (d : ℝ) + (power : ℝ)) / (power : ℝ) =
        2 * Real.exp 1 * (d : ℝ) / (power : ℝ) + Real.exp 1 := by
    field_simp [hpower_real_pos.ne']
  calc
    Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) / (power : ℝ)
        ≤ Real.exp 1 * (2 * (d : ℝ) + (power : ℝ)) / (power : ℝ) := hbase_le
    _ = 2 * Real.exp 1 * (d : ℝ) / (power : ℝ) + Real.exp 1 := hexpanded
    _ ≤ (1 / 8) * (q : ℝ) ^ 2 + (1 / 8) * (q : ℝ) ^ 2 :=
          add_le_add hDterm hq_large
    _ = (1 / 4) * (q : ℝ) ^ 2 := by ring

/--
Threshold source-size arithmetic: the corrected finite size premise used by
the proof makes the floor selector at least `(k-1)^2`.
-/
theorem source_threshold_floor_selector_sq_le
    {m k : ℕ}
    (hk_three : 3 ≤ k)
    (hsize :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
        (m : ℝ)) :
    ((k - 1 : ℕ) : ℝ) ^ 2 ≤
      (Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ)) : ℝ) := by
  let q : ℕ := k - 1
  have hmul_nat :
      (((4 * q + 1 : ℕ) : ℝ) * ((q ^ 2 : ℕ) : ℝ)) < (m : ℝ) := by
    simpa [q, pow_two] using hsize
  have hfloor_nat :
      q ^ 2 ≤ Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ)) :=
    AppliedModelingLib.Math.nat_le_floor_div_of_mul_lt
      (m := m) (a := 4 * q + 1) (n := q ^ 2) (by omega) hmul_nat
  exact_mod_cast hfloor_nat

/--
Finite threshold closeout with `eta = 1/q` and the paper-readable smallness
premise `s <= q^(2*power)`.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_factorial_card_of_s_le_q_pow
    {m d s k q power : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hdim :
      2 * ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
        (power.factorial : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_factorial_card
    (A := A) (B := B) (threshold := threshold)
    (s := s) (k := k) (q := q) (power := power)
    hk_one hsep (source_eta_small_of_s_le_q_pow hq hs_le) hdim hq hqk hs havg

/--
Finite threshold closeout with the paper-readable smallness premise and a
Stirling-style source-scale envelope for the symmetric-power coordinate count.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow
    {m d s k q power : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_factorial_card_of_s_le_q_pow
    (A := A) (B := B) (threshold := threshold)
    (s := s) (k := k) (q := q) (power := power)
    hk_one hsep hs_le
    (two_mul_pow_div_factorial_lt_of_two_mul_exp_mul_div_pow_lt
      (N := 2 * d + power - 1) hpower hdim)
    hq hqk hs havg

/--
Finite threshold closeout in the strongest source-shaped form currently used
for the paper: `eta = 1/q`, `s <= q^(2*power)`, a Stirling-style
symmetric-power envelope, and the source's coarse Turán average estimate.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_coarse_turan
    {m d s k q power : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 1 < s)
    (havg :
      (m : ℝ) * ((2 * q : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False := by
  let B' : FeatureMatrix m d := diagonalNormalizedProbeMatrix A B
  let threshold' : Fin m → ℝ := diagonalNormalizedThresholds A B threshold
  have hsep' : thresholdSeparationCondition A B' threshold' k := by
    simpa [B', threshold'] using
      thresholdSeparationCondition_diagonalNormalized
        (A := A) (B := B) (threshold := threshold) hk_one hsep
  have hdiag' : ∀ i : Fin m, inner (B' i) (A i) = 1 := by
    intro i
    simpa [B'] using
      diagonalNormalizedProbeMatrix_diag_eq_one_of_thresholdSeparationCondition
        (A := A) (B := B) (threshold := threshold) hk_one hsep i
  have hq_real_pos : 0 < (q : ℝ) := by exact_mod_cast hq
  have heta_nonneg : 0 ≤ 1 / (q : ℝ) := by positivity
  have hunit : 1 ≤ (q : ℝ) * (1 / (q : ℝ)) := by
    field_simp [ne_of_gt hq_real_pos]
    exact le_rfl
  have hsmall :
      ∀ t : Finset (Fin m), t.card = s →
        (Fintype.card {j // j ∈ t} : ℝ) *
          (1 / (q : ℝ)) ^ (2 * power) ≤ 1 := by
    intro t ht
    simpa [Fintype.card_coe, ht] using
      source_eta_small_of_s_le_q_pow (s := s) (q := q) (power := power) hq hs_le
  have hdim' :
      ∀ t : Finset (Fin m), t.card = s →
        2 * (Fintype.card (Sym (Sum (Fin d) (Fin d)) power) : ℝ) <
          (Fintype.card {j // j ∈ t} : ℝ) := by
    intro t ht
    simpa [Fintype.card_coe, ht] using
      two_mul_card_sym_sum_fin_lt_of_two_mul_exp_mul_div_pow_lt
        (d := d) (t := power) hpower hdim
  have hprincipal :
      ∀ t : Finset (Fin m), t.card = s →
        ∃ x y : {j // j ∈ t},
          x ≠ y ∧
            (1 / (q : ℝ)) <
              |((interferenceMatrix A B').submatrix Subtype.val Subtype.val) x y| :=
    every_principalSubmatrix_has_largeOffdiag_of_symmetricPower_obstruction
      (A := A) (B := B') hdiag' heta_nonneg hsmall hdim'
  exact
    false_of_thresholdSeparationCondition_and_coarse_turan_principalSubmatrix_largeOffdiag
      (A := A) (B := B') (threshold := threshold') (eta := 1 / (q : ℝ))
      (s := s) (k := k) (q := q)
      hsep' hdiag' heta_nonneg hq hqk hunit hs hprincipal havg

/--
Finite threshold closeout where the Turán average is supplied by the source
parameter inequality `(4q+1)(s-1) < m`.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_source_turan
    {m d s k q power : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_one : 1 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 1 < s)
    (hm : 0 < m)
    (hturan : (((4 * q + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ)) < (m : ℝ)) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_coarse_turan
    (A := A) (B := B) (threshold := threshold)
    (s := s) (k := k) (q := q) (power := power)
    hk_one hsep hs_le hpower hdim hq hqk hs
    (coarse_turan_average_of_four_mul_add_one_mul_lt
      (m := m) (q := q) (r := s - 1) hm (Nat.sub_pos_of_lt hs) hturan)

/--
Source-shaped threshold closeout with selected finite parameters:
`q = k - 1`, `s = q^(2*power)`, and
`power = floor(log floor(m/(4q+1)) / (2 log q))`.

The selector premise states exactly the finite size fact needed by the
polynomial/rank obstruction; it is derived from the corrected source-size
premise in the next theorem.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_floor_log_power_base
    {m d k : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_three : 3 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hselector :
      ((k - 1 : ℕ) : ℝ) ^ 2 ≤
        (Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ)) : ℝ))
    (hbase :
      let q := k - 1
      let s0 := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
      let power := Nat.floor (Real.log (s0 : ℝ) /
        (2 * Real.log ((q : ℝ))))
      Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ) ≤
        (1 / 4) * (q : ℝ) ^ 2)
    (hm : 0 < m) :
    False := by
  let q : ℕ := k - 1
  let s0 : ℕ := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
  let power : ℕ := Nat.floor (Real.log (s0 : ℝ) /
    (2 * Real.log ((q : ℝ))))
  let s : ℕ := q ^ (2 * power)
  have hq_one : 1 < q := by omega
  have hq_pos : 0 < q := by omega
  have hq_sq_ge_one : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by
    have hq_real : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq_one
    nlinarith
  have hs0_one_real : (1 : ℝ) ≤ (s0 : ℝ) := by
    exact le_trans hq_sq_ge_one (by simpa [q, s0] using hselector)
  have hs0_one : 1 ≤ s0 := by exact_mod_cast hs0_one_real
  have hpower_one : 1 ≤ power := by
    simpa [power] using
      AppliedModelingLib.Math.one_le_nat_floor_log_div_of_sq_le
        (k := q) (s := s0) hq_one (by simpa [q, s0] using hselector)
  have hpower_pos : 0 < power := lt_of_lt_of_le Nat.zero_lt_one hpower_one
  have hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power) := by
    simp [s]
  have hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ) := by
    have hdim_real :=
      threshold_symmetricPower_hdim_of_base_le_q_pow
        (d := d) (q := q) (power := power)
        hq_pos hpower_pos (by simpa [q, s0, power] using hbase)
    simpa [s] using hdim_real
  have hs : 1 < s := by
    have htwo_power_ne : 2 * power ≠ 0 := by omega
    simpa [s] using (one_lt_pow' hq_one htwo_power_ne)
  have hpow_le_s0_real : (q : ℝ) ^ (2 * power) ≤ (s0 : ℝ) := by
    simpa [power] using
      AppliedModelingLib.Math.pow_two_mul_nat_floor_log_div_le
        (k := q) (s := s0) hq_one hs0_one
  have hpow_le_s0_nat : q ^ (2 * power) ≤ s0 := by
    exact_mod_cast hpow_le_s0_real
  have hsub_le :
      (((s - 1 : ℕ) : ℝ)) ≤ (((s0 - 1 : ℕ) : ℝ)) := by
    have hnat : s - 1 ≤ s0 - 1 := Nat.sub_le_sub_right hpow_le_s0_nat 1
    exact_mod_cast hnat
  have hcoef_nonneg : 0 ≤ ((4 * q + 1 : ℕ) : ℝ) := by positivity
  have hturan :
      (((4 * q + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ)) < (m : ℝ) := by
    have hle :
        ((4 * q + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ) ≤
          ((4 * q + 1 : ℕ) : ℝ) * ((s0 - 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hsub_le hcoef_nonneg
    exact lt_of_le_of_lt hle
      (by
        simpa [q, s0] using
          source_turan_floor_selector_mul_sub_one_lt (m := m) (q := q) hm)
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_source_turan
      (A := A) (B := B) (threshold := threshold)
      (s := s) (k := k) (q := q) (power := power)
      (by omega) hsep hs_le hpower_pos hdim hq_pos (by omega) hs hm hturan

/--
Threshold closeout with the corrected source-size premise deriving the finite
selector side condition.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_floor_log_power_base_source_size
    {m d k : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_three : 3 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hsize :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
        (m : ℝ))
    (hbase :
      let q := k - 1
      let s0 := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
      let power := Nat.floor (Real.log (s0 : ℝ) /
        (2 * Real.log ((q : ℝ))))
      Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ) ≤
        (1 / 4) * (q : ℝ) ^ 2) :
    False := by
  have hm_real : 0 < (m : ℝ) := by
    have hcoef_pos :
        0 < ((4 * (k - 1) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < 4 * (k - 1) + 1)
    have hq_pos : 0 < ((k - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < k - 1)
    have hleft_pos :
        0 < (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) :=
      mul_pos hcoef_pos (pow_pos hq_pos _)
    exact lt_trans hleft_pos hsize
  have hm : 0 < m := by exact_mod_cast hm_real
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_floor_log_power_base
      (m := m) (d := d) (k := k) (A := A) (B := B)
      (threshold := threshold) hk_three hsep
      (source_threshold_floor_selector_sq_le
        (m := m) (k := k) hk_three hsize)
      hbase hm

/--
Threshold closeout with the corrected source-size premise and a clean
candidate-dimension bound.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_floor_log_power_candidate_source_size
    {m d k : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_three : 3 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hsize :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
        (m : ℝ))
    (hD :
      let q := k - 1
      let s0 := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
      let power := Nat.floor (Real.log (s0 : ℝ) /
        (2 * Real.log ((q : ℝ))))
      (d : ℝ) ≤ (1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2)
    (hq_large :
      Real.exp 1 ≤ (1 / 8) * ((k - 1 : ℕ) : ℝ) ^ 2) :
    False := by
  let q : ℕ := k - 1
  let s0 : ℕ := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
  let power : ℕ := Nat.floor (Real.log (s0 : ℝ) /
    (2 * Real.log ((q : ℝ))))
  have hselector :
      (q : ℝ) ^ 2 ≤ (s0 : ℝ) := by
    simpa [q, s0] using
      source_threshold_floor_selector_sq_le
        (m := m) (k := k) hk_three hsize
  have hpower_pos : 0 < power := by
    have hone : 1 ≤ power := by
      simpa [power] using
        AppliedModelingLib.Math.one_le_nat_floor_log_div_of_sq_le
          (k := q) (s := s0) (by omega) hselector
    exact lt_of_lt_of_le Nat.zero_lt_one hone
  have hbase :
      Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) / (power : ℝ) ≤
        (1 / 4) * (q : ℝ) ^ 2 :=
    threshold_symmetricPower_base_le_of_candidate_dimension_le
      (d := d) (q := q) (power := power)
      (by omega) hpower_pos (by simpa [q, s0, power] using hD)
      (by simpa [q] using hq_large)
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_floor_log_power_base_source_size
      (m := m) (d := d) (k := k) (A := A) (B := B)
      (threshold := threshold) hk_three hsep hsize
      (by simpa [q, s0, power] using hbase)

/--
Minimum-dimension form of the corrected finite threshold lower bound.  This
turns the contradiction row into a direct lower bound for the smallest
threshold-separating dimension.
-/
theorem thresholdSeparationDimensionValue_real_gt_floor_log_power_candidate_source_size
    {m k dmin : ℕ}
    (hk_three : 3 ≤ k)
    (hsize :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
        (m : ℝ))
    (hq_large :
      Real.exp 1 ≤ (1 / 8) * ((k - 1 : ℕ) : ℝ) ^ 2)
    (hvalue : thresholdSeparationDimensionValue m k dmin) :
    let q := k - 1
    let s0 := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
    let power := Nat.floor (Real.log (s0 : ℝ) /
      (2 * Real.log ((q : ℝ))))
    (1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2 <
      (dmin : ℝ) := by
  let q : ℕ := k - 1
  let s0 : ℕ := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
  let power : ℕ := Nat.floor (Real.log (s0 : ℝ) /
    (2 * Real.log ((q : ℝ))))
  change
    (1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2 <
      (dmin : ℝ)
  by_contra hnot
  have hD :
      (dmin : ℝ) ≤
        (1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2 :=
    le_of_not_gt hnot
  rcases hvalue.1 with ⟨A, B, threshold, hsep⟩
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_floor_log_power_candidate_source_size
      (m := m) (d := dmin) (k := k) (A := A) (B := B)
      (threshold := threshold) hk_three hsep hsize
      (by simpa [q, s0, power] using hD) hq_large

/--
Activation/bias closeout with the corrected source-size premise and a clean
candidate-dimension bound.  Monotonicity reduces the statement to the
threshold closeout.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_floor_log_power_candidate_source_size
    {m d k : ℕ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_three : 3 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hsize :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
        (m : ℝ))
    (hD :
      let q := k - 1
      let s0 := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
      let power := Nat.floor (Real.log (s0 : ℝ) /
        (2 * Real.log ((q : ℝ))))
      (d : ℝ) ≤ (1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2)
    (hq_large :
      Real.exp 1 ≤ (1 / 8) * ((k - 1 : ℕ) : ℝ) ^ 2) :
    False := by
  have hsep :
      thresholdSeparationCondition A W (activationDerivedThresholds A W bias k) k :=
    thresholdSeparationCondition_of_monotone_activationSeparationCondition
      (A := A) (W := W) (bias := bias) (sigma := sigma) hmono hact
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_floor_log_power_candidate_source_size
      (m := m) (d := d) (k := k) (A := A) (B := W)
      (threshold := activationDerivedThresholds A W bias k)
      hk_three hsep hsize hD hq_large

/--
Minimum-dimension form of the corrected finite activation/bias lower bound.
-/
theorem activationSeparationDimensionValue_real_gt_floor_log_power_candidate_source_size
    {m k dmin : ℕ}
    (hk_three : 3 ≤ k)
    (hsize :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
        (m : ℝ))
    (hq_large :
      Real.exp 1 ≤ (1 / 8) * ((k - 1 : ℕ) : ℝ) ^ 2)
    (hvalue : activationSeparationDimensionValue m k dmin) :
    let q := k - 1
    let s0 := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
    let power := Nat.floor (Real.log (s0 : ℝ) /
      (2 * Real.log ((q : ℝ))))
    (1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2 <
      (dmin : ℝ) := by
  let q : ℕ := k - 1
  let s0 : ℕ := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
  let power : ℕ := Nat.floor (Real.log (s0 : ℝ) /
    (2 * Real.log ((q : ℝ))))
  change
    (1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2 <
      (dmin : ℝ)
  by_contra hnot
  have hD :
      (dmin : ℝ) ≤
        (1 / (16 * Real.exp 1)) * (power : ℝ) * (q : ℝ) ^ 2 :=
    le_of_not_gt hnot
  rcases hvalue.1 with ⟨A, W, bias, sigma, hmono, hact⟩
  exact
    false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_floor_log_power_candidate_source_size
      (m := m) (d := dmin) (k := k) (A := A) (W := W)
      (bias := bias) (sigma := sigma) hk_three hmono hact hsize
      (by simpa [q, s0, power] using hD) hq_large

/--
Source-shaped threshold closeout with the auxiliary threshold denominator
specialized to `k - 1`, removing the non-source `q` parameter from the theorem
surface.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_k_pred_pow_source_turan
    {m d s k power : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_two : 2 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hs_le : (s : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hs : 1 < s)
    (hm : 0 < m)
    (hturan :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ)) < (m : ℝ)) :
    False :=
  false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_source_turan
    (A := A) (B := B) (threshold := threshold)
    (s := s) (k := k) (q := k - 1) (power := power)
    (by omega) hsep hs_le hpower hdim (by omega) (by omega) hs hm hturan

/--
Source-shaped threshold closeout with `q = k - 1` and
`s = floor(m/(4(k-1)+1))`.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_k_pred_pow_floor_turan
    {m d k power : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_two : 2 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hs_le :
      let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
      (s : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ)))
    (hm : 0 < m) :
    False := by
  let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_k_pred_pow_source_turan
      (A := A) (B := B) (threshold := threshold)
      (s := s) (k := k) (power := power)
      hk_two hsep (by simpa [s] using hs_le) hpower (by simpa [s] using hdim)
      (by simpa [s] using hs) hm
      (by
        simpa [s] using
          source_turan_floor_selector_mul_sub_one_lt (m := m) (q := k - 1) hm)

/--
Source-shaped threshold closeout with both finite source counting parameters
selected: `s = floor(m/(4(k-1)+1))` and
`power = ceil(log s / (2 log(k-1)))`.  This internalizes the analytic
smallness premise `s <= (k-1)^(2*power)`.
-/
theorem false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_ceil_power_floor_turan
    {m d k : ℕ}
    {A B : FeatureMatrix m d} {threshold : Fin m → ℝ}
    (hk_three : 3 ≤ k)
    (hsep : thresholdSeparationCondition A B threshold k)
    (hdim :
      let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
      let power :=
        Nat.ceil (Real.log (s : ℝ) /
          (2 * Real.log (((k - 1 : ℕ) : ℝ))))
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ)))
    (hm : 0 < m) :
    False := by
  let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
  let power : ℕ :=
    Nat.ceil (Real.log (s : ℝ) /
      (2 * Real.log (((k - 1 : ℕ) : ℝ))))
  have hq_one : 1 < k - 1 := by omega
  have hs_one_le : 1 ≤ s := by omega
  have hs_le :
      (s : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ (2 * power) := by
    simpa [power] using
      AppliedModelingLib.Math.le_pow_two_mul_nat_ceil_log_div
        (k := k - 1) (s := s) hq_one hs_one_le
  have hlogq_pos : 0 < Real.log (((k - 1 : ℕ) : ℝ)) := by
    exact Real.log_pos (by exact_mod_cast hq_one)
  have hlogs_pos : 0 < Real.log (s : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (by simpa [s] using hs))
  have harg_pos :
      0 <
        Real.log (s : ℝ) /
          (2 * Real.log (((k - 1 : ℕ) : ℝ))) := by
    exact div_pos hlogs_pos (by positivity)
  have hpower : 0 < power := by
    simpa [power] using Nat.ceil_pos.mpr harg_pos
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_k_pred_pow_floor_turan
      (A := A) (B := B) (threshold := threshold)
      (m := m) (d := d) (k := k) (power := power)
      (by omega) hsep (by simpa [s, power] using hs_le) hpower
      (by simpa [s, power] using hdim) (by simpa [s] using hs) hm

/--
Finite activation/bias closeout: a monotone activation separator first yields
the linear threshold separator, then the normalized finite rank/Turán
contradiction applies.
-/
theorem false_of_activationSeparationCondition_and_alonNormalizedRankBound_dimension_turan
    {m d s k q : ℕ} {eta c : ℝ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hAlon : ∀ t : Finset (Fin m), t.card = s →
      ∀ (D : Matrix {j // j ∈ t} {j // j ∈ t} ℝ) {epsilon : ℝ},
        1 / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < epsilon →
        epsilon < 1 / 2 →
        (∀ i, D i i = 1) →
        (∀ ⦃i j⦄, i ≠ j → |D i j| ≤ epsilon) →
        alonNormalizedRankBound (Fintype.card {j // j ∈ t}) epsilon c ≤ (D.rank : ℝ))
    (heta_low : ∀ t : Finset (Fin m), t.card = s →
      1 / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < eta)
    (heta_high : eta < 1 / 2)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (d : ℝ) < alonScaledRankBound (Fintype.card {j // j ∈ t}) 1 eta c)
    (heta : 0 ≤ eta) (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hsep :
      thresholdSeparationCondition A W (activationDerivedThresholds A W bias k) k :=
    thresholdSeparationCondition_of_monotone_activationSeparationCondition
      (A := A) (W := W) (bias := bias) (sigma := sigma)
      hmono hact
  exact
    false_of_thresholdSeparationCondition_and_alonNormalizedRankBound_dimension_turan_normalized
      (A := A) (B := W) (threshold := activationDerivedThresholds A W bias k)
      (eta := eta) (c := c) (s := s) (k := k) (q := q)
      hk_one hsep hAlon heta_low heta_high hdim heta hq hqk hunit hs havg

/--
Finite activation/bias closeout using the explicit symmetric-power obstruction.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_dimension_turan
    {m d s k q power : ℕ} {eta : ℝ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (heta : 0 ≤ eta)
    (hsmall : ∀ t : Finset (Fin m), t.card = s →
      (Fintype.card {j // j ∈ t} : ℝ) * eta ^ (2 * power) ≤ 1)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      2 * (Fintype.card (Sym (Sum (Fin d) (Fin d)) power) : ℝ) <
        (Fintype.card {j // j ∈ t} : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hsep :
      thresholdSeparationCondition A W (activationDerivedThresholds A W bias k) k :=
    thresholdSeparationCondition_of_monotone_activationSeparationCondition
      (A := A) (W := W) (bias := bias) (sigma := sigma)
      hmono hact
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan_normalized
      (A := A) (B := W) (threshold := activationDerivedThresholds A W bias k)
      (eta := eta) (s := s) (k := k) (q := q) (power := power)
      hk_one hsep heta hsmall hdim hq hqk hunit hs havg

/--
Finite activation/bias closeout with stars-and-bars coordinates and source
subset cardinality written directly as `s`.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_dimension_turan_choose_card
    {m d s k q power : ℕ} {eta : ℝ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (heta : 0 ≤ eta)
    (hsmall : (s : ℝ) * eta ^ (2 * power) ≤ 1)
    (hdim : 2 * ((2 * d + power - 1).choose power : ℝ) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hsep :
      thresholdSeparationCondition A W (activationDerivedThresholds A W bias k) k :=
    thresholdSeparationCondition_of_monotone_activationSeparationCondition
      (A := A) (W := W) (bias := bias) (sigma := sigma) hmono hact
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan_normalized_choose_card
      (A := A) (B := W) (threshold := activationDerivedThresholds A W bias k)
      (eta := eta) (s := s) (k := k) (q := q) (power := power)
      hk_one hsep heta hsmall hdim hq hqk hunit hs havg

/--
Finite activation/bias closeout with the binomial coordinate count replaced by
the simpler sufficient power envelope `(2d + power)^power`.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_dimension_turan_pow_card
    {m d s k q power : ℕ} {eta : ℝ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (heta : 0 ≤ eta)
    (hsmall : (s : ℝ) * eta ^ (2 * power) ≤ 1)
    (hdim : 2 * ((((2 * d + power) ^ power : ℕ) : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hsep :
      thresholdSeparationCondition A W (activationDerivedThresholds A W bias k) k :=
    thresholdSeparationCondition_of_monotone_activationSeparationCondition
      (A := A) (W := W) (bias := bias) (sigma := sigma) hmono hact
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan_normalized_pow_card
      (A := A) (B := W) (threshold := activationDerivedThresholds A W bias k)
      (eta := eta) (s := s) (k := k) (q := q) (power := power)
      hk_one hsep heta hsmall hdim hq hqk hunit hs havg

/--
Finite activation/bias closeout with the factorial-normalized coordinate
envelope.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_dimension_turan_factorial_card
    {m d s k q power : ℕ} {eta : ℝ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (heta : 0 ≤ eta)
    (hsmall : (s : ℝ) * eta ^ (2 * power) ≤ 1)
    (hdim :
      2 * ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
        (power.factorial : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * eta)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hsep :
      thresholdSeparationCondition A W (activationDerivedThresholds A W bias k) k :=
    thresholdSeparationCondition_of_monotone_activationSeparationCondition
      (A := A) (W := W) (bias := bias) (sigma := sigma) hmono hact
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_dimension_turan_normalized_factorial_card
      (A := A) (B := W) (threshold := activationDerivedThresholds A W bias k)
      (eta := eta) (s := s) (k := k) (q := q) (power := power)
      hk_one hsep heta hsmall hdim hq hqk hunit hs havg

/--
Finite activation/bias closeout with the source threshold substitution
`eta = 1/q`.
-/
theorem false_of_activationSeparationCondition_and_alonNormalizedRankBound_source_eta
    {m d s k q : ℕ} {c : ℝ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hAlon : ∀ t : Finset (Fin m), t.card = s →
      ∀ (D : Matrix {j // j ∈ t} {j // j ∈ t} ℝ) {epsilon : ℝ},
        1 / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < epsilon →
        epsilon < 1 / 2 →
        (∀ i, D i i = 1) →
        (∀ ⦃i j⦄, i ≠ j → |D i j| ≤ epsilon) →
        alonNormalizedRankBound (Fintype.card {j // j ∈ t}) epsilon c ≤ (D.rank : ℝ))
    (heta_low : ∀ t : Finset (Fin m), t.card = s →
      1 / Real.sqrt (Fintype.card {j // j ∈ t} : ℝ) < 1 / (q : ℝ))
    (heta_high : 1 / (q : ℝ) < 1 / 2)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      (d : ℝ) < alonScaledRankBound (Fintype.card {j // j ∈ t}) 1 (1 / (q : ℝ)) c)
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hsep :
      thresholdSeparationCondition A W (activationDerivedThresholds A W bias k) k :=
    thresholdSeparationCondition_of_monotone_activationSeparationCondition
      (A := A) (W := W) (bias := bias) (sigma := sigma) hmono hact
  exact
    false_of_thresholdSeparationCondition_and_alonNormalizedRankBound_source_eta
      (A := A) (B := W) (threshold := activationDerivedThresholds A W bias k)
      (c := c) (s := s) (k := k) (q := q)
      hk_one hsep hAlon heta_low heta_high hdim hq hqk hs havg

/--
Finite activation/bias closeout with `eta = 1/q`, using the explicit
symmetric-power rank obstruction.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_source_eta
    {m d s k q power : ℕ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hsmall : ∀ t : Finset (Fin m), t.card = s →
      (Fintype.card {j // j ∈ t} : ℝ) * (1 / (q : ℝ)) ^ (2 * power) ≤ 1)
    (hdim : ∀ t : Finset (Fin m), t.card = s →
      2 * (Fintype.card (Sym (Sum (Fin d) (Fin d)) power) : ℝ) <
        (Fintype.card {j // j ∈ t} : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hsep :
      thresholdSeparationCondition A W (activationDerivedThresholds A W bias k) k :=
    thresholdSeparationCondition_of_monotone_activationSeparationCondition
      (A := A) (W := W) (bias := bias) (sigma := sigma) hmono hact
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_source_eta
      (A := A) (B := W) (threshold := activationDerivedThresholds A W bias k)
      (s := s) (k := k) (q := q) (power := power)
      hk_one hsep hsmall hdim hq hqk hs havg

/--
Finite activation/bias closeout with `eta = 1/q`, stars-and-bars
coordinates, and source subset cardinality written directly as `s`.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_source_eta_choose_card
    {m d s k q power : ℕ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hsmall : (s : ℝ) * (1 / (q : ℝ)) ^ (2 * power) ≤ 1)
    (hdim : 2 * ((2 * d + power - 1).choose power : ℝ) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hsep :
      thresholdSeparationCondition A W (activationDerivedThresholds A W bias k) k :=
    thresholdSeparationCondition_of_monotone_activationSeparationCondition
      (A := A) (W := W) (bias := bias) (sigma := sigma) hmono hact
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_choose_card
      (A := A) (B := W) (threshold := activationDerivedThresholds A W bias k)
      (s := s) (k := k) (q := q) (power := power)
      hk_one hsep hsmall hdim hq hqk hs havg

/--
Finite activation/bias closeout with `eta = 1/q` and the binomial coordinate
count replaced by the simpler sufficient power envelope `(2d + power)^power`.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_source_eta_pow_card
    {m d s k q power : ℕ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hsmall : (s : ℝ) * (1 / (q : ℝ)) ^ (2 * power) ≤ 1)
    (hdim : 2 * ((((2 * d + power) ^ power : ℕ) : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hsep :
      thresholdSeparationCondition A W (activationDerivedThresholds A W bias k) k :=
    thresholdSeparationCondition_of_monotone_activationSeparationCondition
      (A := A) (W := W) (bias := bias) (sigma := sigma) hmono hact
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_pow_card
      (A := A) (B := W) (threshold := activationDerivedThresholds A W bias k)
      (s := s) (k := k) (q := q) (power := power)
      hk_one hsep hsmall hdim hq hqk hs havg

/--
Finite activation/bias closeout with `eta = 1/q` and the
factorial-normalized coordinate envelope.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_source_eta_factorial_card
    {m d s k q power : ℕ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hsmall : (s : ℝ) * (1 / (q : ℝ)) ^ (2 * power) ≤ 1)
    (hdim :
      2 * ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
        (power.factorial : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False := by
  have hsep :
      thresholdSeparationCondition A W (activationDerivedThresholds A W bias k) k :=
    thresholdSeparationCondition_of_monotone_activationSeparationCondition
      (A := A) (W := W) (bias := bias) (sigma := sigma) hmono hact
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_factorial_card
      (A := A) (B := W) (threshold := activationDerivedThresholds A W bias k)
      (s := s) (k := k) (q := q) (power := power)
      hk_one hsep hsmall hdim hq hqk hs havg

/--
Finite activation/bias closeout with `eta = 1/q` and the paper-readable
smallness premise `s <= q^(2*power)`.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_source_eta_factorial_card_of_s_le_q_pow
    {m d s k q power : ℕ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hdim :
      2 * ((((2 * d + power - 1) ^ power : ℕ) : ℝ) /
        (power.factorial : ℝ)) < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_source_eta_factorial_card
    (A := A) (W := W) (bias := bias) (sigma := sigma)
    (s := s) (k := k) (q := q) (power := power)
    hk_one hmono hact (source_eta_small_of_s_le_q_pow hq hs_le)
    hdim hq hqk hs havg

/--
Finite activation/bias closeout with the paper-readable smallness premise and
a Stirling-style source-scale envelope for the symmetric-power coordinate
count.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow
    {m d s k q power : ℕ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 0 < s)
    (havg :
      m * (2 * q) <
        (let r := s - 1
         m.choose 2 -
          ((m ^ 2 - (m % r) ^ 2) * (r - 1) / (2 * r) + (m % r).choose 2))) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_source_eta_factorial_card_of_s_le_q_pow
    (A := A) (W := W) (bias := bias) (sigma := sigma)
    (s := s) (k := k) (q := q) (power := power)
    hk_one hmono hact hs_le
    (two_mul_pow_div_factorial_lt_of_two_mul_exp_mul_div_pow_lt
      (N := 2 * d + power - 1) hpower hdim)
    hq hqk hs havg

/--
Finite activation/bias closeout in the strongest source-shaped form currently
used for the paper, with the source's coarse Turán average estimate.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_coarse_turan
    {m d s k q power : ℕ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 1 < s)
    (havg :
      (m : ℝ) * ((2 * q : ℕ) : ℝ) <
        (m : ℝ) ^ 2 / (2 * ((s - 1 : ℕ) : ℝ)) - (m : ℝ) / 2) :
    False := by
  have hsep :
      thresholdSeparationCondition A W (activationDerivedThresholds A W bias k) k :=
    thresholdSeparationCondition_of_monotone_activationSeparationCondition
      (A := A) (W := W) (bias := bias) (sigma := sigma)
      hmono hact
  exact
    false_of_thresholdSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_coarse_turan
      (A := A) (B := W) (threshold := activationDerivedThresholds A W bias k)
      (s := s) (k := k) (q := q) (power := power)
      hk_one hsep hs_le hpower hdim hq hqk hs havg

/--
Finite activation/bias closeout where the Turán average is supplied by the
source parameter inequality `(4q+1)(s-1) < m`.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_source_turan
    {m d s k q power : ℕ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_one : 1 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hs_le : (s : ℝ) ≤ (q : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hs : 1 < s)
    (hm : 0 < m)
    (hturan : (((4 * q + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ)) < (m : ℝ)) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_coarse_turan
    (A := A) (W := W) (bias := bias) (sigma := sigma)
    (s := s) (k := k) (q := q) (power := power)
    hk_one hmono hact hs_le hpower hdim hq hqk hs
    (coarse_turan_average_of_four_mul_add_one_mul_lt
      (m := m) (q := q) (r := s - 1) hm (Nat.sub_pos_of_lt hs) hturan)

/--
Source-shaped activation/bias closeout with the auxiliary threshold denominator
specialized to `k - 1`, matching the threshold wrapper.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_k_pred_pow_source_turan
    {m d s k power : ℕ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_two : 2 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hs_le : (s : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hs : 1 < s)
    (hm : 0 < m)
    (hturan :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((s - 1 : ℕ) : ℝ)) < (m : ℝ)) :
    False :=
  false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_q_pow_source_turan
    (A := A) (W := W) (bias := bias) (sigma := sigma)
    (s := s) (k := k) (q := k - 1) (power := power)
    (by omega) hmono hact hs_le hpower hdim (by omega) (by omega) hs hm hturan

/--
Source-shaped activation/bias closeout with `q = k - 1` and
`s = floor(m/(4(k-1)+1))`.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_k_pred_pow_floor_turan
    {m d k power : ℕ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_two : 2 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hs_le :
      let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
      (s : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ (2 * power))
    (hpower : 0 < power)
    (hdim :
      let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ)))
    (hm : 0 < m) :
    False := by
  let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
  exact
    false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_k_pred_pow_source_turan
      (A := A) (W := W) (bias := bias) (sigma := sigma)
      (s := s) (k := k) (power := power)
      hk_two hmono hact (by simpa [s] using hs_le) hpower (by simpa [s] using hdim)
      (by simpa [s] using hs) hm
      (by
        simpa [s] using
          source_turan_floor_selector_mul_sub_one_lt (m := m) (q := k - 1) hm)

/--
Source-shaped activation/bias closeout with both finite source counting
parameters selected.  It shares the same ceiling-power choice as the threshold
closeout after reducing activation separation to threshold separation.
-/
theorem false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_ceil_power_floor_turan
    {m d k : ℕ}
    {A W : FeatureMatrix m d} {bias : Fin m → ℝ} {sigma : ℝ → ℝ}
    (hk_three : 3 ≤ k)
    (hmono : Monotone sigma)
    (hact : activationSeparationCondition A W bias sigma k)
    (hdim :
      let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
      let power :=
        Nat.ceil (Real.log (s : ℝ) /
          (2 * Real.log (((k - 1 : ℕ) : ℝ))))
      2 * (Real.exp 1 * ((2 * d + power - 1 : ℕ) : ℝ) /
          (power : ℝ)) ^ power < (s : ℝ))
    (hs :
      1 < Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ)))
    (hm : 0 < m) :
    False := by
  let s := Nat.floor ((m : ℝ) / ((4 * (k - 1) + 1 : ℕ) : ℝ))
  let power : ℕ :=
    Nat.ceil (Real.log (s : ℝ) /
      (2 * Real.log (((k - 1 : ℕ) : ℝ))))
  have hq_one : 1 < k - 1 := by omega
  have hs_one_le : 1 ≤ s := by omega
  have hs_le :
      (s : ℝ) ≤ ((k - 1 : ℕ) : ℝ) ^ (2 * power) := by
    simpa [power] using
      AppliedModelingLib.Math.le_pow_two_mul_nat_ceil_log_div
        (k := k - 1) (s := s) hq_one hs_one_le
  have hlogq_pos : 0 < Real.log (((k - 1 : ℕ) : ℝ)) := by
    exact Real.log_pos (by exact_mod_cast hq_one)
  have hlogs_pos : 0 < Real.log (s : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (by simpa [s] using hs))
  have harg_pos :
      0 <
        Real.log (s : ℝ) /
          (2 * Real.log (((k - 1 : ℕ) : ℝ))) := by
    exact div_pos hlogs_pos (by positivity)
  have hpower : 0 < power := by
    simpa [power] using Nat.ceil_pos.mpr harg_pos
  exact
    false_of_activationSeparationCondition_and_symmetricPower_source_eta_exp_card_of_s_le_k_pred_pow_floor_turan
      (A := A) (W := W) (bias := bias) (sigma := sigma)
      (m := m) (d := d) (k := k) (power := power)
      (by omega) hmono hact (by simpa [s, power] using hs_le) hpower
      (by simpa [s, power] using hdim) (by simpa [s] using hs) hm

/--
Corrected finite source regime for the threshold and activation/bias
asymptotic wrappers.  This is the explicit condition needed by the source
rank/Turán proof route after specializing the auxiliary threshold denominator
to `q = k - 1`.
-/
def thresholdActivationCorrectedSourceRegime (p : ℕ × ℕ) : Prop :=
  3 ≤ p.2 ∧
    (((4 * (p.2 - 1) + 1 : ℕ) : ℝ) * ((p.2 - 1 : ℕ) : ℝ) ^ 2) <
      (p.1 : ℝ)

/--
Restricted-at-infinity filter for corrected threshold/activation asymptotics.
-/
noncomputable def thresholdActivationCorrectedSourceFilter :
    Filter (ℕ × ℕ) :=
  Filter.atTop ⊓
    Filter.principal
      {p : ℕ × ℕ | thresholdActivationCorrectedSourceRegime p}

/--
Finite floor-log scale delivered directly by the corrected
threshold/activation rank/Turán proof:
`(k-1)^2 log floor(m/(4(k-1)+1)) / log(k-1)`.
-/
noncomputable def thresholdActivationLowerFloorLogScale
    (p : ℕ × ℕ) : ℝ :=
  let q : ℕ := p.2 - 1
  (q : ℝ) ^ 2 *
    (Real.log
        (Nat.floor ((p.1 : ℝ) / ((4 * q + 1 : ℕ) : ℝ)) : ℝ) /
      Real.log (q : ℝ))

/--
The printed threshold/activation source scale:
`k^2 log(m/k) / log k`.
-/
noncomputable def thresholdActivationLowerSourceLogScale
    (p : ℕ × ℕ) : ℝ :=
  (p.2 : ℝ) ^ 2 *
    (Real.log ((p.1 : ℝ) / (p.2 : ℝ)) / Real.log (p.2 : ℝ))

/-- The original source regime `k < sqrt(m)`, written without a square root. -/
def thresholdActivationOriginalSourceRegime (p : ℕ × ℕ) : Prop :=
  3 ≤ p.2 ∧ (p.2 : ℝ) ^ 2 < (p.1 : ℝ)

/-- Restricted-at-infinity filter for the paper's original source regime. -/
noncomputable def thresholdActivationOriginalSourceFilter :
    Filter (ℕ × ℕ) :=
  Filter.atTop ⊓ Filter.principal
    {p : ℕ × ℕ | thresholdActivationOriginalSourceRegime p}

theorem thresholdActivationLowerSourceLogScale_nonneg_of_original_regime
    {m k : ℕ} (hsource : thresholdActivationOriginalSourceRegime (m, k)) :
    0 ≤ thresholdActivationLowerSourceLogScale (m, k) := by
  rcases hsource with ⟨hk_three, hmsq⟩
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk_log_pos : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hk_le_m : (k : ℝ) ≤ (m : ℝ) := by
    have hk_le_sq : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      have hk_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
      nlinarith
    exact hk_le_sq.trans (le_of_lt hmsq)
  have hratio_one : (1 : ℝ) ≤ (m : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hk_pos]
    simpa using hk_le_m
  exact mul_nonneg (sq_nonneg _) <|
    div_nonneg (Real.log_nonneg hratio_one) hk_log_pos.le

/--
When the original source regime holds but the stronger finite condition used
by the Alon--Turan branch does not, the printed logarithmic scale is at most a
constant multiple of `k^2`.
-/
theorem thresholdActivationLowerSourceLogScale_le_four_k_sq_of_not_corrected
    {m k : ℕ} (hk_five : 5 ≤ k)
    (hsource : thresholdActivationOriginalSourceRegime (m, k))
    (hnot_corrected :
      ¬ (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
          (m : ℝ)) :
    thresholdActivationLowerSourceLogScale (m, k) ≤ 4 * (k : ℝ) ^ 2 := by
  rcases hsource with ⟨_hk_three, hmsq⟩
  let q : ℕ := k - 1
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk_log_pos : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hm_pos : 0 < (m : ℝ) :=
    lt_trans (sq_pos_of_pos hk_pos) hmsq
  have hq_le_k : q ≤ k := by dsimp [q]; omega
  have hcoef_le : (4 * q + 1 : ℕ) ≤ 5 * k := by
    dsimp [q]
    omega
  have hq_sq_le : (q : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 := by
    have hcast : (q : ℝ) ≤ (k : ℝ) := by exact_mod_cast hq_le_k
    exact pow_le_pow_left₀ (Nat.cast_nonneg q) hcast 2
  have hsize_le :
      (m : ℝ) ≤ ((4 * q + 1 : ℕ) : ℝ) * (q : ℝ) ^ 2 := by
    simpa [q] using le_of_not_gt hnot_corrected
  have hcoef_real_le :
      (((4 * q + 1 : ℕ) : ℝ)) ≤ 5 * (k : ℝ) := by
    exact_mod_cast hcoef_le
  have hupper : (m : ℝ) ≤ 5 * (k : ℝ) ^ 3 := by
    calc
      (m : ℝ) ≤ ((4 * q + 1 : ℕ) : ℝ) * (q : ℝ) ^ 2 := hsize_le
      _ ≤ (5 * (k : ℝ)) * (k : ℝ) ^ 2 :=
        mul_le_mul hcoef_real_le hq_sq_le (sq_nonneg _) (by positivity)
      _ = 5 * (k : ℝ) ^ 3 := by ring
  have hmk_pos : 0 < (m : ℝ) / (k : ℝ) := div_pos hm_pos hk_pos
  have hmk_le : (m : ℝ) / (k : ℝ) ≤ 5 * (k : ℝ) ^ 2 := by
    rw [div_le_iff₀ hk_pos]
    nlinarith
  have hk_sq_ge_five : (5 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have hk_five_real : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_five
    nlinarith
  have hfive_ksq_le_kfour :
      5 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by
    nlinarith [sq_nonneg ((k : ℝ) ^ 2 - 5)]
  have hmk_le_kfour : (m : ℝ) / (k : ℝ) ≤ (k : ℝ) ^ 4 :=
    hmk_le.trans hfive_ksq_le_kfour
  have hlog_le :
      Real.log ((m : ℝ) / (k : ℝ)) ≤ 4 * Real.log (k : ℝ) := by
    have := Real.log_le_log hmk_pos hmk_le_kfour
    simpa [Real.log_pow] using this
  have hratio_le :
      Real.log ((m : ℝ) / (k : ℝ)) / Real.log (k : ℝ) ≤ 4 := by
    rw [div_le_iff₀ hk_log_pos]
    simpa [mul_comm] using hlog_le
  simpa [thresholdActivationLowerSourceLogScale, mul_comm] using
    (mul_le_mul_of_nonneg_left hratio_le (sq_nonneg (k : ℝ)))

/--
The corrected threshold/activation regime makes the floor-log scale
nonnegative.
-/
theorem thresholdActivationLowerFloorLogScale_nonneg_of_corrected_regime
    {p : ℕ × ℕ}
    (hsource : thresholdActivationCorrectedSourceRegime p) :
    0 ≤ thresholdActivationLowerFloorLogScale p := by
  rcases p with ⟨m, k⟩
  rcases hsource with ⟨hk_three, hsize⟩
  let q : ℕ := k - 1
  let s0 : ℕ := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
  have hselector : (q : ℝ) ^ 2 ≤ (s0 : ℝ) := by
    simpa [q, s0] using
      source_threshold_floor_selector_sq_le
        (m := m) (k := k) hk_three hsize
  have hq_one : 1 < q := by omega
  have hq_real_one : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ q)
  have hq_sq_one : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by
    nlinarith
  have hs_one : (1 : ℝ) ≤ (s0 : ℝ) :=
    le_trans hq_sq_one hselector
  have hlogs_nonneg : 0 ≤ Real.log (s0 : ℝ) :=
    Real.log_nonneg hs_one
  have hlogq_pos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hq_one)
  have hratio_nonneg :
      0 ≤ Real.log (s0 : ℝ) / Real.log (q : ℝ) :=
    div_nonneg hlogs_nonneg hlogq_pos.le
  exact
    mul_nonneg (sq_nonneg (q : ℝ)) hratio_nonneg

/--
The printed threshold/activation source scale is eventually nonnegative along
the corrected source regime.
-/
theorem thresholdActivationLowerSourceLogScale_eventually_nonneg :
    ∀ᶠ p in thresholdActivationCorrectedSourceFilter,
      0 ≤ thresholdActivationLowerSourceLogScale p := by
  rw [thresholdActivationCorrectedSourceFilter]
  exact eventually_inf_principal.2 <| by
    refine eventually_atTop.2 ⟨(0, 4), ?_⟩
    intro p hp hsource
    rcases p with ⟨m, k⟩
    rcases hsource with ⟨hk_three, hsize⟩
    let q : ℕ := k - 1
    let s0 : ℕ := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
    have hk_four : 4 ≤ k := hp.2
    have hselector : (q : ℝ) ^ 2 ≤ (s0 : ℝ) := by
      simpa [q, s0] using
        source_threshold_floor_selector_sq_le
          (m := m) (k := k) hk_three hsize
    have hq_one : 1 < q := by omega
    have hq_sq_ge_q : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
      have hq_one_real : (1 : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ q)
      nlinarith
    have hfloor_le_arg :
        (s0 : ℝ) ≤ (m : ℝ) / ((4 * q + 1 : ℕ) : ℝ) :=
      Nat.floor_le (div_nonneg (Nat.cast_nonneg m)
        (by exact_mod_cast (by omega : 0 ≤ 4 * q + 1)))
    have hq_le_div : (q : ℝ) ≤ (m : ℝ) / ((4 * q + 1 : ℕ) : ℝ) :=
      le_trans hq_sq_ge_q (le_trans hselector hfloor_le_arg)
    have hden_pos : 0 < (((4 * q + 1 : ℕ) : ℝ)) := by
      exact_mod_cast (by omega : 0 < 4 * q + 1)
    have hmul := (le_div_iff₀ hden_pos).1 hq_le_div
    have hk_real_pos : 0 < (k : ℝ) := by
      exact_mod_cast (by omega : 0 < k)
    have hq_pos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hm_ge_k : (k : ℝ) ≤ (m : ℝ) := by
      have hk_le_q_mul :
          (k : ℝ) ≤ (q : ℝ) * ((4 * q + 1 : ℕ) : ℝ) := by
        have hk_eq : (k : ℝ) = (q : ℝ) + 1 := by
          simp [q]
          exact_mod_cast (by omega : k = k - 1 + 1)
        have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
        have hfactor_ge_two : (2 : ℝ) ≤ ((4 * q + 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : 2 ≤ 4 * q + 1)
        nlinarith
      linarith
    have hratio_ge_one : (1 : ℝ) ≤ (m : ℝ) / (k : ℝ) := by
      rw [le_div_iff₀ hk_real_pos]
      simpa using hm_ge_k
    have hlog_nonneg : 0 ≤ Real.log ((m : ℝ) / (k : ℝ)) :=
      Real.log_nonneg hratio_ge_one
    have hlogk_pos : 0 < Real.log (k : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    have hratio_nonneg :
        0 ≤ Real.log ((m : ℝ) / (k : ℝ)) / Real.log (k : ℝ) :=
      div_nonneg hlog_nonneg hlogk_pos.le
    exact
      mul_nonneg (sq_nonneg (k : ℝ)) hratio_nonneg

/--
Auxiliary comparison: with `q = k - 1`, the `q`-source log scale is controlled
by the finite floor-log scale produced by the rank/Turan proof.
-/
theorem thresholdActivationLowerQSourceLogScale_le_two_floor_logScale
    {m k : ℕ}
    (hk_five : 5 ≤ k)
    (hsource : thresholdActivationCorrectedSourceRegime (m, k)) :
    let q : ℕ := k - 1
    (q : ℝ) ^ 2 *
      (Real.log ((m : ℝ) / (q : ℝ)) / Real.log (q : ℝ)) ≤
        2 * thresholdActivationLowerFloorLogScale (m, k) := by
  rcases hsource with ⟨hk_three, hsize⟩
  let q : ℕ := k - 1
  let s : ℕ := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
  have hk_four_q : 4 ≤ q := by omega
  have hsq : (q : ℝ) ^ 2 ≤ (s : ℝ) := by
    simpa [q, s] using
      source_threshold_floor_selector_sq_le
        (m := m) (k := k) hk_three hsize
  have hq_real_pos : 0 < (q : ℝ) := by
    exact_mod_cast (by omega : 0 < q)
  have hq_log_pos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hq_sq_ge_sixteen : (16 : ℝ) ≤ (q : ℝ) ^ 2 := by
    have hq_four_real : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hk_four_q
    nlinarith
  have hs_ten : (10 : ℝ) ≤ (s : ℝ) :=
    le_trans (by norm_num : (10 : ℝ) ≤ 16) (le_trans hq_sq_ge_sixteen hsq)
  have hs_one : (1 : ℝ) ≤ (s : ℝ) :=
    le_trans (by norm_num : (1 : ℝ) ≤ 10) hs_ten
  have hs_pos : 0 < (s : ℝ) := lt_of_lt_of_le zero_lt_one hs_one
  have hm_pos : 0 < (m : ℝ) := by
    have hcoef_pos :
        0 < ((4 * q + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < 4 * q + 1)
    have hq_pos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hleft_pos :
        0 < (((4 * q + 1 : ℕ) : ℝ) * (q : ℝ) ^ 2) :=
      mul_pos hcoef_pos (pow_pos hq_pos _)
    have hsize' :
        (((4 * q + 1 : ℕ) : ℝ) * (q : ℝ) ^ 2) < (m : ℝ) := by
      simpa [q] using hsize
    exact lt_trans hleft_pos hsize'
  have hden_pos : 0 < (((4 * q + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 0 < 4 * q + 1)
  have hcoef_le :
      (((4 * q + 1 : ℕ) : ℝ) / (q : ℝ)) ≤ 5 := by
    rw [div_le_iff₀ hq_real_pos]
    norm_num
    have hq_one_real : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ q)
    nlinarith
  have hfloor_upper :
      (m : ℝ) / (((4 * q + 1 : ℕ) : ℝ)) ≤ (s : ℝ) + 1 := by
    exact le_of_lt (by
      simpa [s] using
        Nat.lt_floor_add_one
          ((m : ℝ) / (((4 * q + 1 : ℕ) : ℝ))))
  have hfloor_arg_nonneg :
      0 ≤ (m : ℝ) / (((4 * q + 1 : ℕ) : ℝ)) :=
    div_nonneg hm_pos.le hden_pos.le
  have hmul_bound :
      (((4 * q + 1 : ℕ) : ℝ) / (q : ℝ)) *
          ((m : ℝ) / (((4 * q + 1 : ℕ) : ℝ))) ≤
        5 * ((s : ℝ) + 1) :=
    mul_le_mul hcoef_le hfloor_upper hfloor_arg_nonneg
      (by norm_num : (0 : ℝ) ≤ 5)
  have hm_div_decomp :
      (m : ℝ) / (q : ℝ) =
        (((4 * q + 1 : ℕ) : ℝ) / (q : ℝ)) *
          ((m : ℝ) / (((4 * q + 1 : ℕ) : ℝ))) := by
    field_simp [hq_real_pos.ne', hden_pos.ne']
  have hm_div_le_ten_s :
      (m : ℝ) / (q : ℝ) ≤ 10 * (s : ℝ) := by
    calc
      (m : ℝ) / (q : ℝ) =
          (((4 * q + 1 : ℕ) : ℝ) / (q : ℝ)) *
            ((m : ℝ) / (((4 * q + 1 : ℕ) : ℝ))) := hm_div_decomp
      _ ≤ 5 * ((s : ℝ) + 1) := hmul_bound
      _ ≤ 10 * (s : ℝ) := by nlinarith [hs_one]
  have hten_s_le_sq : 10 * (s : ℝ) ≤ (s : ℝ) ^ 2 := by
    nlinarith [hs_ten]
  have hm_div_le_sq :
      (m : ℝ) / (q : ℝ) ≤ (s : ℝ) ^ 2 :=
    le_trans hm_div_le_ten_s hten_s_le_sq
  have hm_div_pos : 0 < (m : ℝ) / (q : ℝ) :=
    div_pos hm_pos hq_real_pos
  have hlog_le_sq :
      Real.log ((m : ℝ) / (q : ℝ)) ≤ Real.log ((s : ℝ) ^ 2) :=
    Real.log_le_log hm_div_pos hm_div_le_sq
  have hlog_sq :
      Real.log ((s : ℝ) ^ 2) = 2 * Real.log (s : ℝ) := by
    rw [Real.log_pow]
    norm_num
  have hlog_le :
      Real.log ((m : ℝ) / (q : ℝ)) ≤ 2 * Real.log (s : ℝ) := by
    simpa [hlog_sq] using hlog_le_sq
  have hratio_le :
      Real.log ((m : ℝ) / (q : ℝ)) / Real.log (q : ℝ) ≤
        2 * (Real.log (s : ℝ) / Real.log (q : ℝ)) := by
    calc
      Real.log ((m : ℝ) / (q : ℝ)) / Real.log (q : ℝ)
          ≤ (2 * Real.log (s : ℝ)) / Real.log (q : ℝ) :=
            div_le_div_of_nonneg_right hlog_le hq_log_pos.le
      _ = 2 * (Real.log (s : ℝ) / Real.log (q : ℝ)) := by ring
  have hscaled :=
    mul_le_mul_of_nonneg_left hratio_le (sq_nonneg (q : ℝ))
  simpa [thresholdActivationLowerFloorLogScale, s, q, mul_assoc, mul_comm,
    mul_left_comm] using hscaled

/--
The printed `k`-scale is controlled by the `q = k - 1` scale used in the
finite proof.
-/
theorem thresholdActivationLowerSourceLogScale_le_four_q_source_log_scale
    {m k : ℕ}
    (hk_five : 5 ≤ k)
    (hsource : thresholdActivationCorrectedSourceRegime (m, k)) :
    let q : ℕ := k - 1
    thresholdActivationLowerSourceLogScale (m, k) ≤
      4 * ((q : ℝ) ^ 2 *
        (Real.log ((m : ℝ) / (q : ℝ)) / Real.log (q : ℝ))) := by
  rcases hsource with ⟨hk_three, hsize⟩
  let q : ℕ := k - 1
  let s0 : ℕ := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
  have hselector : (q : ℝ) ^ 2 ≤ (s0 : ℝ) := by
    simpa [q, s0] using
      source_threshold_floor_selector_sq_le
        (m := m) (k := k) hk_three hsize
  have hq_one : 1 < q := by omega
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hq_sq_ge_q : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
    have hq_one_real : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ q)
    nlinarith
  have hfloor_le_arg :
      (s0 : ℝ) ≤ (m : ℝ) / ((4 * q + 1 : ℕ) : ℝ) :=
    Nat.floor_le (div_nonneg (Nat.cast_nonneg m)
      (by exact_mod_cast (by omega : 0 ≤ 4 * q + 1)))
  have hq_le_div : (q : ℝ) ≤ (m : ℝ) / ((4 * q + 1 : ℕ) : ℝ) :=
    le_trans hq_sq_ge_q (le_trans hselector hfloor_le_arg)
  have hden_pos : 0 < (((4 * q + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (by omega : 0 < 4 * q + 1)
  have hm_lower :=
    (le_div_iff₀ hden_pos).1 hq_le_div
  have hm_pos : 0 < (m : ℝ) := by
    have hleft_pos : 0 < (q : ℝ) * ((4 * q + 1 : ℕ) : ℝ) :=
      mul_pos hq_pos hden_pos
    exact lt_of_lt_of_le hleft_pos hm_lower
  have hk_le_qfactor :
      (k : ℝ) ≤ (q : ℝ) * ((4 * q + 1 : ℕ) : ℝ) := by
    have hk_eq : (k : ℝ) = (q : ℝ) + 1 := by
      simp [q]
      exact_mod_cast (by omega : k = k - 1 + 1)
    have hfactor_ge_two : (2 : ℝ) ≤ ((4 * q + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 2 ≤ 4 * q + 1)
    nlinarith
  have hk_le_m : (k : ℝ) ≤ (m : ℝ) := le_trans hk_le_qfactor hm_lower
  have hmk_pos : 0 < (m : ℝ) / (k : ℝ) := div_pos hm_pos hk_pos
  have hmq_pos : 0 < (m : ℝ) / (q : ℝ) := div_pos hm_pos hq_pos
  have hmk_le_hmq : (m : ℝ) / (k : ℝ) ≤ (m : ℝ) / (q : ℝ) := by
    exact div_le_div_of_nonneg_left hm_pos.le hq_pos (by exact_mod_cast (by omega : q ≤ k))
  have hlog_mk_le_mq :
      Real.log ((m : ℝ) / (k : ℝ)) ≤ Real.log ((m : ℝ) / (q : ℝ)) :=
    Real.log_le_log hmk_pos hmk_le_hmq
  have hratio_mq_nonneg :
      0 ≤ Real.log ((m : ℝ) / (q : ℝ)) / Real.log (q : ℝ) := by
    have hq_le_m : (q : ℝ) ≤ (m : ℝ) := by
      exact le_trans (by exact_mod_cast (by omega : q ≤ k)) hk_le_m
    have hmq_ge_one : (1 : ℝ) ≤ (m : ℝ) / (q : ℝ) := by
      rw [le_div_iff₀ hq_pos]
      simpa using hq_le_m
    exact div_nonneg (Real.log_nonneg hmq_ge_one)
      (Real.log_pos (by exact_mod_cast hq_one)).le
  have hlogq_pos : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast hq_one)
  have hlogk_pos : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hlogq_le_logk : Real.log (q : ℝ) ≤ Real.log (k : ℝ) := by
    exact Real.log_le_log hq_pos (by exact_mod_cast (by omega : q ≤ k))
  have hratio_le :
      Real.log ((m : ℝ) / (k : ℝ)) / Real.log (k : ℝ) ≤
        Real.log ((m : ℝ) / (q : ℝ)) / Real.log (q : ℝ) := by
    calc
      Real.log ((m : ℝ) / (k : ℝ)) / Real.log (k : ℝ)
          ≤ Real.log ((m : ℝ) / (q : ℝ)) / Real.log (k : ℝ) :=
            div_le_div_of_nonneg_right hlog_mk_le_mq hlogk_pos.le
      _ ≤ Real.log ((m : ℝ) / (q : ℝ)) / Real.log (q : ℝ) :=
            div_le_div_of_nonneg_left
              (by
                have hq_le_m : (q : ℝ) ≤ (m : ℝ) := by
                  exact le_trans (by exact_mod_cast (by omega : q ≤ k)) hk_le_m
                have hmq_ge_one : (1 : ℝ) ≤ (m : ℝ) / (q : ℝ) := by
                  rw [le_div_iff₀ hq_pos]
                  simpa using hq_le_m
                exact Real.log_nonneg hmq_ge_one)
              hlogq_pos hlogq_le_logk
  have hk_sq_le : (k : ℝ) ^ 2 ≤ 4 * (q : ℝ) ^ 2 := by
    have hk_eq : (k : ℝ) = (q : ℝ) + 1 := by
      simp [q]
      exact_mod_cast (by omega : k = k - 1 + 1)
    have hq_one_real : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ q)
    nlinarith
  calc
    thresholdActivationLowerSourceLogScale (m, k)
        ≤ (k : ℝ) ^ 2 *
            (Real.log ((m : ℝ) / (q : ℝ)) / Real.log (q : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hratio_le (sq_nonneg (k : ℝ))
    _ ≤ (4 * (q : ℝ) ^ 2) *
            (Real.log ((m : ℝ) / (q : ℝ)) / Real.log (q : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hk_sq_le hratio_mq_nonneg
    _ = 4 * ((q : ℝ) ^ 2 *
            (Real.log ((m : ℝ) / (q : ℝ)) / Real.log (q : ℝ))) := by ring

/--
The printed threshold/activation source scale is Big-O of the finite
floor-log scale in the corrected source regime.
-/
theorem thresholdActivationLowerSourceLogScale_isBigO_floor_log_corrected_regime :
    Asymptotics.IsBigO
      thresholdActivationCorrectedSourceFilter
      thresholdActivationLowerSourceLogScale
      thresholdActivationLowerFloorLogScale := by
  refine AppliedModelingLib.Math.isBigO_of_eventually_nonneg_le_const_mul
    (C := 8) (by norm_num) ?_ ?_ ?_
  · exact thresholdActivationLowerSourceLogScale_eventually_nonneg
  · rw [thresholdActivationCorrectedSourceFilter]
    exact eventually_inf_principal.2 <| by
      filter_upwards with p hsource
      exact thresholdActivationLowerFloorLogScale_nonneg_of_corrected_regime hsource
  · rw [thresholdActivationCorrectedSourceFilter]
    exact eventually_inf_principal.2 <| by
      refine eventually_atTop.2 ⟨(0, 5), ?_⟩
      intro p hp hsource
      rcases p with ⟨m, k⟩
      have hk_five : 5 ≤ k := hp.2
      have hfour :
          thresholdActivationLowerSourceLogScale (m, k) ≤
            4 * (((k - 1 : ℕ) : ℝ) ^ 2 *
              (Real.log ((m : ℝ) / ((k - 1 : ℕ) : ℝ)) /
                Real.log (((k - 1 : ℕ) : ℝ)))) :=
        thresholdActivationLowerSourceLogScale_le_four_q_source_log_scale
          (m := m) (k := k) hk_five hsource
      have htwo :
          (((k - 1 : ℕ) : ℝ) ^ 2 *
              (Real.log ((m : ℝ) / ((k - 1 : ℕ) : ℝ)) /
                Real.log (((k - 1 : ℕ) : ℝ)))) ≤
            2 * thresholdActivationLowerFloorLogScale (m, k) :=
        thresholdActivationLowerQSourceLogScale_le_two_floor_logScale
          (m := m) (k := k) hk_five hsource
      calc
        thresholdActivationLowerSourceLogScale (m, k)
            ≤ 4 * (((k - 1 : ℕ) : ℝ) ^ 2 *
              (Real.log ((m : ℝ) / ((k - 1 : ℕ) : ℝ)) /
                Real.log (((k - 1 : ℕ) : ℝ)))) := hfour
        _ ≤ 4 * (2 * thresholdActivationLowerFloorLogScale (m, k)) :=
              mul_le_mul_of_nonneg_left htwo (by norm_num)
        _ = 8 * thresholdActivationLowerFloorLogScale (m, k) := by ring

/--
The large-`k` side condition used by the corrected finite threshold and
activation/bias lower bounds is eventually true.
-/
theorem thresholdActivationFiniteLargeK_eventually_atTop :
    ∀ᶠ p : ℕ × ℕ in Filter.atTop,
      Real.exp 1 ≤ (1 / 8) * ((p.2 - 1 : ℕ) : ℝ) ^ 2 := by
  let a : ℝ := (1 / 8)
  have ha_pos : 0 < a := by norm_num [a]
  rcases exists_nat_gt (max (1 : ℝ) (Real.exp 1 / a)) with ⟨N, hN⟩
  refine eventually_atTop.2 ⟨(0, N + 1), ?_⟩
  intro p hp
  let q : ℕ := p.2 - 1
  have hN_le_q : N ≤ q := by
    have hp2 : N + 1 ≤ p.2 := hp.2
    dsimp [q]
    omega
  have hN_le_q_real : (N : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hN_le_q
  have hdiv_le_max :
      Real.exp 1 / a ≤ max (1 : ℝ) (Real.exp 1 / a) :=
    le_max_right _ _
  have hmax_le_N : max (1 : ℝ) (Real.exp 1 / a) ≤ (N : ℝ) :=
    le_of_lt hN
  have hdiv_le_q : Real.exp 1 / a ≤ (q : ℝ) := by
    linarith
  have hone_le_q : (1 : ℝ) ≤ (q : ℝ) := by
    have hone_le_max : (1 : ℝ) ≤ max (1 : ℝ) (Real.exp 1 / a) :=
      le_max_left _ _
    linarith
  have hq_le_sq : (q : ℝ) ≤ (q : ℝ) ^ 2 := by
    nlinarith
  have hdiv_le_sq : Real.exp 1 / a ≤ (q : ℝ) ^ 2 := by
    linarith
  have hmul : Real.exp 1 ≤ (q : ℝ) ^ 2 * a :=
    (div_le_iff₀ ha_pos).1 hdiv_le_sq
  calc
    Real.exp 1 ≤ (q : ℝ) ^ 2 * a := hmul
    _ = (1 / 8) * ((p.2 - 1 : ℕ) : ℝ) ^ 2 := by
          simp [a, q, mul_comm]

/--
Corrected finite threshold lower bound in logarithmic scale.  This turns the
floor choice of the symmetric-power exponent into a constant fraction of
`log floor(m/(4(k-1)+1)) / log(k-1)`.
-/
theorem thresholdSeparationDimensionValue_real_gt_log_floor_selector_source_size
    {m k dmin : ℕ}
    (hk_three : 3 ≤ k)
    (hsize :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
        (m : ℝ))
    (hq_large :
      Real.exp 1 ≤ (1 / 8) * ((k - 1 : ℕ) : ℝ) ^ 2)
    (hvalue : thresholdSeparationDimensionValue m k dmin) :
    let q := k - 1
    let s0 := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
    (1 / (64 * Real.exp 1)) * (q : ℝ) ^ 2 *
        (Real.log (s0 : ℝ) / Real.log (q : ℝ)) <
      (dmin : ℝ) := by
  let q : ℕ := k - 1
  let s0 : ℕ := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
  let power : ℕ := Nat.floor (Real.log (s0 : ℝ) /
    (2 * Real.log ((q : ℝ))))
  let c : ℝ := 1 / (16 * Real.exp 1)
  have hreal :
      c * (power : ℝ) * (q : ℝ) ^ 2 < (dmin : ℝ) := by
    simpa [q, s0, power, c, mul_assoc, mul_comm, mul_left_comm] using
      thresholdSeparationDimensionValue_real_gt_floor_log_power_candidate_source_size
        (m := m) (k := k) (dmin := dmin)
        hk_three hsize hq_large hvalue
  have hselector :
      (q : ℝ) ^ 2 ≤ (s0 : ℝ) := by
    simpa [q, s0] using
      source_threshold_floor_selector_sq_le
        (m := m) (k := k) hk_three hsize
  have hpower_lower :
      Real.log (s0 : ℝ) / (4 * Real.log (q : ℝ)) ≤ (power : ℝ) := by
    simpa [power] using
      AppliedModelingLib.Math.half_log_div_le_nat_floor_log_div_of_sq_le
        (k := q) (s := s0) (by omega : 1 < q) hselector
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hq_sq_nonneg : 0 ≤ (q : ℝ) ^ 2 := sq_nonneg _
  have hscaled :
      c * (Real.log (s0 : ℝ) / (4 * Real.log (q : ℝ))) *
          (q : ℝ) ^ 2 ≤
        c * (power : ℝ) * (q : ℝ) ^ 2 := by
    have hleft := mul_le_mul_of_nonneg_left hpower_lower hc_nonneg
    have hright := mul_le_mul_of_nonneg_right hleft hq_sq_nonneg
    simpa [mul_assoc, mul_comm, mul_left_comm] using hright
  have htarget_le :
      (1 / (64 * Real.exp 1)) * (q : ℝ) ^ 2 *
          (Real.log (s0 : ℝ) / Real.log (q : ℝ)) ≤
        c * (power : ℝ) * (q : ℝ) ^ 2 := by
    calc
      (1 / (64 * Real.exp 1)) * (q : ℝ) ^ 2 *
          (Real.log (s0 : ℝ) / Real.log (q : ℝ)) =
          c * (Real.log (s0 : ℝ) / (4 * Real.log (q : ℝ))) *
            (q : ℝ) ^ 2 := by
            dsimp [c]
            ring
      _ ≤ c * (power : ℝ) * (q : ℝ) ^ 2 := hscaled
  exact lt_of_le_of_lt (by simpa [q, s0] using htarget_le) hreal

/--
Corrected finite activation/bias lower bound in logarithmic scale.
-/
theorem activationSeparationDimensionValue_real_gt_log_floor_selector_source_size
    {m k dmin : ℕ}
    (hk_three : 3 ≤ k)
    (hsize :
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
        (m : ℝ))
    (hq_large :
      Real.exp 1 ≤ (1 / 8) * ((k - 1 : ℕ) : ℝ) ^ 2)
    (hvalue : activationSeparationDimensionValue m k dmin) :
    let q := k - 1
    let s0 := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
    (1 / (64 * Real.exp 1)) * (q : ℝ) ^ 2 *
        (Real.log (s0 : ℝ) / Real.log (q : ℝ)) <
      (dmin : ℝ) := by
  let q : ℕ := k - 1
  let s0 : ℕ := Nat.floor ((m : ℝ) / ((4 * q + 1 : ℕ) : ℝ))
  let power : ℕ := Nat.floor (Real.log (s0 : ℝ) /
    (2 * Real.log ((q : ℝ))))
  let c : ℝ := 1 / (16 * Real.exp 1)
  have hreal :
      c * (power : ℝ) * (q : ℝ) ^ 2 < (dmin : ℝ) := by
    simpa [q, s0, power, c, mul_assoc, mul_comm, mul_left_comm] using
      activationSeparationDimensionValue_real_gt_floor_log_power_candidate_source_size
        (m := m) (k := k) (dmin := dmin)
        hk_three hsize hq_large hvalue
  have hselector :
      (q : ℝ) ^ 2 ≤ (s0 : ℝ) := by
    simpa [q, s0] using
      source_threshold_floor_selector_sq_le
        (m := m) (k := k) hk_three hsize
  have hpower_lower :
      Real.log (s0 : ℝ) / (4 * Real.log (q : ℝ)) ≤ (power : ℝ) := by
    simpa [power] using
      AppliedModelingLib.Math.half_log_div_le_nat_floor_log_div_of_sq_le
        (k := q) (s := s0) (by omega : 1 < q) hselector
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hq_sq_nonneg : 0 ≤ (q : ℝ) ^ 2 := sq_nonneg _
  have hscaled :
      c * (Real.log (s0 : ℝ) / (4 * Real.log (q : ℝ))) *
          (q : ℝ) ^ 2 ≤
        c * (power : ℝ) * (q : ℝ) ^ 2 := by
    have hleft := mul_le_mul_of_nonneg_left hpower_lower hc_nonneg
    have hright := mul_le_mul_of_nonneg_right hleft hq_sq_nonneg
    simpa [mul_assoc, mul_comm, mul_left_comm] using hright
  have htarget_le :
      (1 / (64 * Real.exp 1)) * (q : ℝ) ^ 2 *
          (Real.log (s0 : ℝ) / Real.log (q : ℝ)) ≤
        c * (power : ℝ) * (q : ℝ) ^ 2 := by
    calc
      (1 / (64 * Real.exp 1)) * (q : ℝ) ^ 2 *
          (Real.log (s0 : ℝ) / Real.log (q : ℝ)) =
          c * (Real.log (s0 : ℝ) / (4 * Real.log (q : ℝ))) *
            (q : ℝ) ^ 2 := by
            dsimp [c]
            ring
      _ ≤ c * (power : ℝ) * (q : ℝ) ^ 2 := hscaled
  exact lt_of_le_of_lt (by simpa [q, s0] using htarget_le) hreal

/--
Corrected-regime Landau lower-bound wrapper for the binary threshold theorem:
the floor-log scale from the rank/Turán proof is Big-O of the minimum
threshold-separating dimension.
-/
theorem thresholdSeparationDimension_isBigO_lower_floor_log_corrected_regime :
    Asymptotics.IsBigO
      thresholdActivationCorrectedSourceFilter
      thresholdActivationLowerFloorLogScale
      (fun p : ℕ × ℕ =>
        (thresholdSeparationDimension p.1 p.2 : ℝ)) := by
  let c : ℝ := 1 / (64 * Real.exp 1)
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  refine AppliedModelingLib.Math.isBigO_of_eventually_pos_mul_le
    (c := c) hc_pos ?_ ?_ ?_
  · rw [thresholdActivationCorrectedSourceFilter]
    exact eventually_inf_principal.2 <| by
      filter_upwards with p hsource
      exact thresholdActivationLowerFloorLogScale_nonneg_of_corrected_regime hsource
  · filter_upwards with p
    exact Nat.cast_nonneg _
  · rw [thresholdActivationCorrectedSourceFilter]
    exact eventually_inf_principal.2 <| by
      filter_upwards [thresholdActivationFiniteLargeK_eventually_atTop]
        with p hk_large hsource
      rcases p with ⟨m, k⟩
      rcases hsource with ⟨hk_three, hsize⟩
      have hvalue :
          thresholdSeparationDimensionValue m k
            (thresholdSeparationDimension m k) :=
        thresholdSeparationDimension_spec m k
      have hlt :
          c * thresholdActivationLowerFloorLogScale (m, k) <
            (thresholdSeparationDimension m k : ℝ) := by
        simpa [thresholdActivationLowerFloorLogScale, c, mul_assoc, mul_comm,
          mul_left_comm] using
          thresholdSeparationDimensionValue_real_gt_log_floor_selector_source_size
            (m := m) (k := k)
            (dmin := thresholdSeparationDimension m k)
            hk_three hsize hk_large hvalue
      exact le_of_lt hlt

/--
Corrected-regime Landau lower-bound wrapper for the binary threshold theorem
in the printed source scale `(k^2 / log k) * log(m/k)`.
-/
theorem thresholdSeparationDimension_isBigO_lower_source_log_corrected_regime :
    Asymptotics.IsBigO
      thresholdActivationCorrectedSourceFilter
      thresholdActivationLowerSourceLogScale
      (fun p : ℕ × ℕ =>
        (thresholdSeparationDimension p.1 p.2 : ℝ)) :=
  thresholdActivationLowerSourceLogScale_isBigO_floor_log_corrected_regime.trans
    thresholdSeparationDimension_isBigO_lower_floor_log_corrected_regime

/--
Corrected-regime Landau lower-bound wrapper for the activation/bias corollary:
the same floor-log scale is Big-O of the minimum activation/bias-separating
dimension.
-/
theorem activationSeparationDimension_isBigO_lower_floor_log_corrected_regime :
    Asymptotics.IsBigO
      thresholdActivationCorrectedSourceFilter
      thresholdActivationLowerFloorLogScale
      (fun p : ℕ × ℕ =>
        (activationSeparationDimension p.1 p.2 : ℝ)) := by
  let c : ℝ := 1 / (64 * Real.exp 1)
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  refine AppliedModelingLib.Math.isBigO_of_eventually_pos_mul_le
    (c := c) hc_pos ?_ ?_ ?_
  · rw [thresholdActivationCorrectedSourceFilter]
    exact eventually_inf_principal.2 <| by
      filter_upwards with p hsource
      exact thresholdActivationLowerFloorLogScale_nonneg_of_corrected_regime hsource
  · filter_upwards with p
    exact Nat.cast_nonneg _
  · rw [thresholdActivationCorrectedSourceFilter]
    exact eventually_inf_principal.2 <| by
      filter_upwards [thresholdActivationFiniteLargeK_eventually_atTop]
        with p hk_large hsource
      rcases p with ⟨m, k⟩
      rcases hsource with ⟨hk_three, hsize⟩
      have hvalue :
          activationSeparationDimensionValue m k
            (activationSeparationDimension m k) :=
        activationSeparationDimension_spec m k
      have hlt :
          c * thresholdActivationLowerFloorLogScale (m, k) <
            (activationSeparationDimension m k : ℝ) := by
        simpa [thresholdActivationLowerFloorLogScale, c, mul_assoc, mul_comm,
          mul_left_comm] using
          activationSeparationDimensionValue_real_gt_log_floor_selector_source_size
            (m := m) (k := k)
            (dmin := activationSeparationDimension m k)
            hk_three hsize hk_large hvalue
      exact le_of_lt hlt

/--
Corrected-regime Landau lower-bound wrapper for the activation/bias corollary
in the printed source scale `(k^2 / log k) * log(m/k)`.
-/
theorem activationSeparationDimension_isBigO_lower_source_log_corrected_regime :
    Asymptotics.IsBigO
      thresholdActivationCorrectedSourceFilter
      thresholdActivationLowerSourceLogScale
      (fun p : ℕ × ℕ =>
        (activationSeparationDimension p.1 p.2 : ℝ)) :=
  thresholdActivationLowerSourceLogScale_isBigO_floor_log_corrected_regime.trans
    activationSeparationDimension_isBigO_lower_floor_log_corrected_regime

/--
Shared two-regime closeout for the paper's original `k < sqrt(m)` threshold
and activation/bias claims.  The large-`m` branch uses the existing
Alon--Turan proof; the complementary branch uses the trace/Frobenius
`k^2 ≤ 42d` bound.
-/
theorem thresholdActivationLowerSourceLogScale_isBigO_original_regime_of_bounds
    (dimension : ℕ × ℕ → ℝ)
    (hdim_nonneg : ∀ p, 0 ≤ dimension p)
    (hlarge : ∀ {m k : ℕ},
      3 ≤ k →
      (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) < (m : ℝ) →
      Real.exp 1 ≤ (1 / 8) * ((k - 1 : ℕ) : ℝ) ^ 2 →
      (1 / (64 * Real.exp 1)) *
          thresholdActivationLowerFloorLogScale (m, k) < dimension (m, k))
    (hsmall : ∀ {m k : ℕ},
      3 ≤ k → (k : ℝ) ^ 2 < (m : ℝ) →
      (k : ℝ) ^ 2 ≤ 42 * dimension (m, k)) :
    Asymptotics.IsBigO
      thresholdActivationOriginalSourceFilter
      thresholdActivationLowerSourceLogScale
      dimension := by
  let C : ℝ := 512 * Real.exp 1
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  refine AppliedModelingLib.Math.isBigO_of_eventually_nonneg_le_const_mul
    (C := C) hC_nonneg ?_ ?_ ?_
  · rw [thresholdActivationOriginalSourceFilter]
    exact eventually_inf_principal.2 <| by
      filter_upwards with p hsource
      rcases p with ⟨m, k⟩
      exact thresholdActivationLowerSourceLogScale_nonneg_of_original_regime
        hsource
  · filter_upwards with p
    exact hdim_nonneg p
  · rw [thresholdActivationOriginalSourceFilter]
    exact eventually_inf_principal.2 <| by
      have hk_event : ∀ᶠ p : ℕ × ℕ in Filter.atTop, 5 ≤ p.2 :=
        eventually_atTop.2 ⟨(0, 5), fun p hp => hp.2⟩
      filter_upwards [thresholdActivationFiniteLargeK_eventually_atTop, hk_event]
        with p hq_large hp_five hsource
      rcases p with ⟨m, k⟩
      rcases hsource with ⟨hk_three, hmsq⟩
      have hk_five : 5 ≤ k := hp_five
      by_cases hsize :
          (((4 * (k - 1) + 1 : ℕ) : ℝ) * ((k - 1 : ℕ) : ℝ) ^ 2) <
            (m : ℝ)
      · have hcorrected : thresholdActivationCorrectedSourceRegime (m, k) :=
          ⟨hk_three, hsize⟩
        have hfour :
            thresholdActivationLowerSourceLogScale (m, k) ≤
              4 * (((k - 1 : ℕ) : ℝ) ^ 2 *
                (Real.log ((m : ℝ) / ((k - 1 : ℕ) : ℝ)) /
                  Real.log (((k - 1 : ℕ) : ℝ)))) :=
          thresholdActivationLowerSourceLogScale_le_four_q_source_log_scale
            hk_five hcorrected
        have htwo :
            (((k - 1 : ℕ) : ℝ) ^ 2 *
                (Real.log ((m : ℝ) / ((k - 1 : ℕ) : ℝ)) /
                  Real.log (((k - 1 : ℕ) : ℝ)))) ≤
              2 * thresholdActivationLowerFloorLogScale (m, k) :=
          thresholdActivationLowerQSourceLogScale_le_two_floor_logScale
            hk_five hcorrected
        have hsource_floor :
            thresholdActivationLowerSourceLogScale (m, k) ≤
              8 * thresholdActivationLowerFloorLogScale (m, k) := by
          calc
            thresholdActivationLowerSourceLogScale (m, k) ≤
                4 * (((k - 1 : ℕ) : ℝ) ^ 2 *
                  (Real.log ((m : ℝ) / ((k - 1 : ℕ) : ℝ)) /
                    Real.log (((k - 1 : ℕ) : ℝ)))) := hfour
            _ ≤ 4 * (2 * thresholdActivationLowerFloorLogScale (m, k)) :=
              mul_le_mul_of_nonneg_left htwo (by norm_num)
            _ = 8 * thresholdActivationLowerFloorLogScale (m, k) := by ring
        have hfinite :
            (1 / (64 * Real.exp 1)) *
                thresholdActivationLowerFloorLogScale (m, k) <
              dimension (m, k) :=
          hlarge hk_three hsize hq_large
        have hscale_pos : 0 < 64 * Real.exp 1 := by positivity
        have hfloor_lt :
            thresholdActivationLowerFloorLogScale (m, k) <
              (64 * Real.exp 1) * dimension (m, k) := by
          calc
            thresholdActivationLowerFloorLogScale (m, k) =
                (64 * Real.exp 1) *
                  ((1 / (64 * Real.exp 1)) *
                    thresholdActivationLowerFloorLogScale (m, k)) := by
                      field_simp [(Real.exp_pos 1).ne']
            _ < (64 * Real.exp 1) * dimension (m, k) :=
              mul_lt_mul_of_pos_left hfinite hscale_pos
        have hsource_lt :
            thresholdActivationLowerSourceLogScale (m, k) <
              C * dimension (m, k) := by
          calc
            thresholdActivationLowerSourceLogScale (m, k) ≤
                8 * thresholdActivationLowerFloorLogScale (m, k) :=
              hsource_floor
            _ < 8 * ((64 * Real.exp 1) * dimension (m, k)) :=
              mul_lt_mul_of_pos_left hfloor_lt (by norm_num)
            _ = C * dimension (m, k) := by
              dsimp [C]
              ring
        exact le_of_lt hsource_lt
      · have hsource_four :
            thresholdActivationLowerSourceLogScale (m, k) ≤
              4 * (k : ℝ) ^ 2 :=
          thresholdActivationLowerSourceLogScale_le_four_k_sq_of_not_corrected
            hk_five ⟨hk_three, hmsq⟩ hsize
        have hk_sq :
            (k : ℝ) ^ 2 ≤ 42 * dimension (m, k) :=
          hsmall hk_three hmsq
        have h168 :
            thresholdActivationLowerSourceLogScale (m, k) ≤
              168 * dimension (m, k) := by
          calc
            thresholdActivationLowerSourceLogScale (m, k) ≤
                4 * (k : ℝ) ^ 2 := hsource_four
            _ ≤ 4 * (42 * dimension (m, k)) :=
              mul_le_mul_of_nonneg_left hk_sq (by norm_num)
            _ = 168 * dimension (m, k) := by ring
        have hexp_one : (1 : ℝ) ≤ Real.exp 1 :=
          Real.one_le_exp (by norm_num)
        have hconst : (168 : ℝ) ≤ C := by
          dsimp [C]
          nlinarith
        exact h168.trans <|
          mul_le_mul_of_nonneg_right hconst (hdim_nonneg (m, k))

/--
Theorem `thm:threshold` in its original printed regime `k < sqrt(m)` and
source scale `(k^2 / log k) log(m/k)`.
-/
theorem thresholdSeparationDimension_isBigO_lower_source_log_original_regime :
    Asymptotics.IsBigO
      thresholdActivationOriginalSourceFilter
      thresholdActivationLowerSourceLogScale
      (fun p : ℕ × ℕ => (thresholdSeparationDimension p.1 p.2 : ℝ)) := by
  apply thresholdActivationLowerSourceLogScale_isBigO_original_regime_of_bounds
  · intro p
    exact Nat.cast_nonneg _
  · intro m k hk_three hsize hq_large
    have hvalue :
        thresholdSeparationDimensionValue m k
          (thresholdSeparationDimension m k) :=
      thresholdSeparationDimension_spec m k
    simpa [thresholdActivationLowerFloorLogScale,
      mul_assoc, mul_comm, mul_left_comm] using
      thresholdSeparationDimensionValue_real_gt_log_floor_selector_source_size
        hk_three hsize hq_large hvalue
  · intro m k hk_three hmsq
    exact thresholdSeparationDimensionValue_k_sq_le_42_mul
      hk_three hmsq (thresholdSeparationDimension_spec m k)

/--
Corollary `cor:activation-bias` in its original printed regime and source
scale.  The monotone activation result uses the same two-regime closeout after
the existing activation-to-threshold reduction.
-/
theorem activationSeparationDimension_isBigO_lower_source_log_original_regime :
    Asymptotics.IsBigO
      thresholdActivationOriginalSourceFilter
      thresholdActivationLowerSourceLogScale
      (fun p : ℕ × ℕ => (activationSeparationDimension p.1 p.2 : ℝ)) := by
  apply thresholdActivationLowerSourceLogScale_isBigO_original_regime_of_bounds
  · intro p
    exact Nat.cast_nonneg _
  · intro m k hk_three hsize hq_large
    have hvalue :
        activationSeparationDimensionValue m k
          (activationSeparationDimension m k) :=
      activationSeparationDimension_spec m k
    simpa [thresholdActivationLowerFloorLogScale,
      mul_assoc, mul_comm, mul_left_comm] using
      activationSeparationDimensionValue_real_gt_log_floor_selector_source_size
        hk_three hsize hq_large hvalue
  · intro m k hk_three hmsq
    exact activationSeparationDimensionValue_k_sq_le_42_mul
      hk_three hmsq (activationSeparationDimension_spec m k)

end GKP26LinearRepresentationHypothesis
