import GCG24UserItemFairness.Optimization
import AppliedModelingLib.Applications.RecommenderSystems.Classwise
import Mathlib.Data.Finset.Sum

open AppliedModelingLib

namespace GCG24UserItemFairness

abbrev UserType (K : ℕ) := Fin K
abbrev TypePolicy (K n : ℕ) := AppliedModelingLib.Policy (UserType K) (Item n)

namespace RecommendationModel

/--
A recommendation model together with a user-type map for which equal types have
identical utility rows. This is the data needed to formalize the paper's `S_symm`.
-/
structure SymmetricData (m n K : ℕ) where
  model : RecommendationModel m n
  types : UserTypeAssignment m K
  agreeWithinTypes : UtilitiesAgreeWithinTypes model types

end RecommendationModel

namespace UserTypeAssignment

/-- Lift a type-level policy to a user-level policy by composition with the type map. -/
def liftTypePolicy {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : TypePolicy K n) : Policy m n :=
  AppliedModelingLib.Policy.liftAlong τ.toType ρ

/-- A user-level policy is type-symmetric if equal types receive equal PMFs. -/
def IsTypeSymmetric {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : Policy m n) : Prop :=
  AppliedModelingLib.Policy.IsClasswise τ.toType ρ

/--
When declared types are exactly utility-row classes, the source definition of
`S_symm` agrees with the label-based representation used by the reduction.
-/
theorem utilityRowSymmetric_iff_isTypeSymmetric {m n K : ℕ}
    (S : RecommendationModel.SymmetricData m n K)
    (hRowsDetermineTypes :
      RecommendationModel.UserTypeAssignment.UtilityRowsDetermineTypes
        S.model S.types)
    (ρ : Policy m n) :
    RecommendationModel.UtilityRowSymmetric S.model ρ ↔
      IsTypeSymmetric S.types ρ := by
  constructor
  · intro hRows u u' hType
    exact hRows u u' (S.agreeWithinTypes u u' hType)
  · intro hTypes u u' hRows
    exact hTypes u u' (hRowsDetermineTypes u u' hRows)

/-- The finite index type for the coordinate equalities defining `S_symm`. -/
abbrev TypeSymmetryLinearConstraintIndex (m n : ℕ) :=
  User m × User m × Item n

/-- The linear coordinate expression `ρᵢⱼ - ρᵢ'ⱼ` when `i` and `i'` have
the same type.  For different types the corresponding constraint is `0 = 0`.
-/
noncomputable def typeSymmetryLinearExpression {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (c : TypeSymmetryLinearConstraintIndex m n)
    (ρ : Policy m n) : ℝ :=
  if τ.toType c.1 = τ.toType c.2.1 then
    (ρ c.1 c.2.2).toReal - (ρ c.2.1 c.2.2).toReal
  else 0

/-- Satisfaction of the finite coordinate-linear description of `S_symm`. -/
def SatisfiesTypeSymmetryLinearConstraints {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (ρ : Policy m n) : Prop :=
  ∀ c : TypeSymmetryLinearConstraintIndex m n,
    typeSymmetryLinearExpression τ c ρ = 0

/-- `S_symm` is exactly the solution set of the finite linear equalities
`ρᵢⱼ - ρᵢ'ⱼ = 0` for equal-type user pairs. -/
theorem satisfiesTypeSymmetryLinearConstraints_iff_isTypeSymmetric
    {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : Policy m n) :
    SatisfiesTypeSymmetryLinearConstraints τ ρ ↔ IsTypeSymmetric τ ρ := by
  constructor
  · intro hlin u u' htype
    apply PMF.ext
    intro j
    have hcoord := hlin (u, u', j)
    simp [typeSymmetryLinearExpression, htype] at hcoord
    have hreal : (ρ u j).toReal = (ρ u' j).toReal := sub_eq_zero.mp hcoord
    exact (ENNReal.toReal_eq_toReal_iff'
      ((ρ u).apply_ne_top j) ((ρ u').apply_ne_top j)).mp hreal
  · intro hsym c
    rcases c with ⟨u, u', j⟩
    by_cases htype : τ.toType u = τ.toType u'
    · have hrow : ρ u = ρ u' := hsym u u' htype
      simp [typeSymmetryLinearExpression, htype, hrow]
    · simp [typeSymmetryLinearExpression, htype]

/-- The set `S_symm` of type-symmetric user-level policies. -/
def SymmetricPolicies {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) : Set (Policy m n) :=
  AppliedModelingLib.Policy.ClasswisePolicies τ.toType

/-- Coefficients realizing a type-symmetry coordinate equality as a linear
expression over all policy coordinates. -/
noncomputable def typeSymmetryLinearCoefficient {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (c : TypeSymmetryLinearConstraintIndex m n)
    (u : User m) (j : Item n) : ℝ :=
  if τ.toType c.1 = τ.toType c.2.1 then
    (if u = c.1 then if j = c.2.2 then 1 else 0 else 0) -
      (if u = c.2.1 then if j = c.2.2 then 1 else 0 else 0)
  else 0

theorem policyLinearExpression_typeSymmetryLinearCoefficient {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (c : TypeSymmetryLinearConstraintIndex m n) (ρ : Policy m n) :
    RecommendationModel.policyLinearExpression
        (typeSymmetryLinearCoefficient τ c) ρ =
      typeSymmetryLinearExpression τ c ρ := by
  classical
  rcases c with ⟨u, u', j⟩
  by_cases htype : τ.toType u = τ.toType u'
  · simp only [RecommendationModel.policyLinearExpression,
      typeSymmetryLinearCoefficient, typeSymmetryLinearExpression, htype,
      if_pos]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    simp
  · simp [RecommendationModel.policyLinearExpression,
      typeSymmetryLinearCoefficient, typeSymmetryLinearExpression, htype]

/-- A finite coefficient-level linear description witnessing condition (i) of
Proposition 2 for `S_symm`. -/
noncomputable def symmetricPoliciesFiniteLinearDescription {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) :
    RecommendationModel.FiniteLinearPolicySetDescription
      (SymmetricPolicies (n := n) τ) where
  ConstraintIndex := TypeSymmetryLinearConstraintIndex m n
  constraintFintype := inferInstance
  coefficient := typeSymmetryLinearCoefficient τ
  rhs := fun _ => 0
  comparison := fun _ => .eq
  mem_iff := by
    intro ρ
    change IsTypeSymmetric τ ρ ↔
      ∀ c : TypeSymmetryLinearConstraintIndex m n,
        RecommendationModel.policyLinearExpression
          (typeSymmetryLinearCoefficient τ c) ρ = 0
    rw [← satisfiesTypeSymmetryLinearConstraints_iff_isTypeSymmetric τ ρ]
    apply iff_of_eq
    apply propext
    apply forall_congr'
    intro c
    rw [policyLinearExpression_typeSymmetryLinearCoefficient]

@[simp] theorem liftTypePolicy_apply {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : TypePolicy K n) (u : User m) :
    liftTypePolicy τ ρ u = ρ (τ.toType u) := rfl

@[simp] theorem liftTypePolicy_sameType {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : TypePolicy K n)
    {u u' : User m} (h : τ.toType u = τ.toType u') :
    liftTypePolicy τ ρ u = liftTypePolicy τ ρ u' := by
  simp [liftTypePolicy, h]

/-- Every lifted type-level policy is type-symmetric. -/
theorem liftTypePolicy_isTypeSymmetric {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (ρ : TypePolicy K n) :
    IsTypeSymmetric τ (liftTypePolicy τ ρ) := by
  simpa [IsTypeSymmetric, liftTypePolicy] using
    (AppliedModelingLib.Policy.liftAlong_isClasswise (τ := τ.toType) (ρ := ρ))

/-- Chosen representative user for each declared user type. -/
abbrev TypeRepresentatives {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) :=
  AppliedModelingLib.Policy.FiberRepresentatives τ.toType

/--
Descend a user-level policy to the type level by evaluating it on one chosen
representative user from each type.
-/
def descendTypePolicy {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n) : TypePolicy K n :=
  AppliedModelingLib.Policy.descendAlong reps ρ

@[simp] theorem descendTypePolicy_apply {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n) (k : UserType K) :
    descendTypePolicy τ reps ρ k = ρ (reps.repr k) := rfl

@[simp] theorem descendTypePolicy_liftTypePolicy {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : TypePolicy K n) :
    descendTypePolicy τ reps (liftTypePolicy τ ρ) = ρ := by
  simpa [descendTypePolicy, liftTypePolicy] using
    (AppliedModelingLib.Policy.descendAlong_liftAlong (τ := τ.toType) reps ρ)

/-- Descending a type-symmetric user-level policy does not depend on the
chosen representative users. -/
theorem descendTypePolicy_eq_of_isTypeSymmetric {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps reps' : TypeRepresentatives τ) (ρ : Policy m n)
    (hρ : IsTypeSymmetric τ ρ) :
    descendTypePolicy τ reps ρ = descendTypePolicy τ reps' ρ := by
  funext k
  exact hρ (reps.repr k) (reps'.repr k) (by
    rw [reps.repr_spec k, reps'.repr_spec k])

/--
If a user-level policy is type-symmetric, then after choosing one representative
per type it is exactly the lift of a type-level policy.
-/
theorem liftTypePolicy_descendTypePolicy_eq_of_isTypeSymmetric {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n)
    (hρ : IsTypeSymmetric τ ρ) :
    liftTypePolicy τ (descendTypePolicy τ reps ρ) = ρ := by
  simpa [IsTypeSymmetric, descendTypePolicy, liftTypePolicy] using
    (AppliedModelingLib.Policy.liftAlong_descendAlong_eq_of_isClasswise
      (τ := τ.toType) reps ρ hρ)

/--
A user-level policy is type-symmetric exactly when it comes from lifting some
policy on user types. Representatives make the reverse direction explicit.
-/
theorem isTypeSymmetric_iff_exists_liftTypePolicy {m n K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n) :
    IsTypeSymmetric τ ρ ↔ ∃ ρK : TypePolicy K n, liftTypePolicy τ ρK = ρ := by
  simpa [IsTypeSymmetric, liftTypePolicy] using
    (AppliedModelingLib.Policy.isClasswise_iff_exists_liftAlong (τ := τ.toType) reps ρ)

end UserTypeAssignment

namespace TypePolicy

/-- Positive-support type-item pairs `(k, j)`. -/
noncomputable def activeTypeItemPairs {K n : ℕ}
    (ρ : TypePolicy K n) : Finset (UserType K × Item n) :=
  AppliedModelingLib.Policy.activePairs ρ

/-- Number of positive-support type-item pairs. -/
noncomputable def activeTypeItemPairsCard {K n : ℕ} (ρ : TypePolicy K n) : ℕ :=
  AppliedModelingLib.Policy.activePairsCard ρ

/-- Zero-support type-item pairs `(k, j)`. -/
noncomputable def inactiveTypeItemPairs {K n : ℕ}
    (ρ : TypePolicy K n) : Finset (UserType K × Item n) :=
  AppliedModelingLib.Policy.inactivePairs ρ

@[simp] theorem mem_inactiveTypeItemPairs {K n : ℕ}
    (ρ : TypePolicy K n) (p : UserType K × Item n) :
    p ∈ inactiveTypeItemPairs ρ ↔ ρ p.1 p.2 = 0 := by
  simp [inactiveTypeItemPairs]

/-- Number of zero-support type-item pairs. -/
noncomputable def inactiveTypeItemPairsCard {K n : ℕ} (ρ : TypePolicy K n) : ℕ :=
  AppliedModelingLib.Policy.inactivePairsCard ρ

/-- Items recommended to more than one user type. -/
noncomputable def sharedItems {K n : ℕ} (ρ : TypePolicy K n) : Finset (Item n) :=
  AppliedModelingLib.Policy.multiAssignedActions ρ

/-- Target shape of the first sparsity conclusion in Proposition 2. -/
def ActivePairsBound {K n : ℕ} (ρ : TypePolicy K n) : Prop :=
  activeTypeItemPairsCard ρ ≤ n + K - 1

/-- Target shape of the second sparsity conclusion in Proposition 2. -/
def SharedItemsBound {K n : ℕ} (ρ : TypePolicy K n) : Prop :=
  (sharedItems ρ).card ≤ K - 1

/-- The combined sparse-support shape extracted from Proposition 2. -/
def SparseShape {K n : ℕ} (ρ : TypePolicy K n) : Prop :=
  ActivePairsBound ρ ∧ SharedItemsBound ρ

/--
Two-type threshold support shape from Appendix D, Lemma 4: type `0` only uses
items weakly before the pivot and type `1` only uses items weakly after it.
-/
def TwoTypeThresholdSupport {n : ℕ} (ρ : TypePolicy 2 n) : Prop :=
  ∃ t : Item n,
    (∀ {j : Item n}, t.val < j.val → ρ 0 j = 0) ∧
    (∀ {j : Item n}, j.val < t.val → ρ 1 j = 0)

/--
No-gap condition for the first row of Problem 6: once an earlier `x_j` is zero,
all later `x_i` are zero.
-/
def TwoTypeXZeroClosed {n : ℕ} (ρ : TypePolicy 2 n) : Prop :=
  ∀ {j i : Item n}, j.val < i.val → ρ 0 j = 0 → ρ 0 i = 0

/--
No-gap condition for the second row of Problem 6: once a later `y_j` is zero,
all earlier `y_i` are zero.
-/
def TwoTypeYZeroClosed {n : ℕ} (ρ : TypePolicy 2 n) : Prop :=
  ∀ {i j : Item n}, i.val < j.val → ρ 1 j = 0 → ρ 1 i = 0

/-- Every PMF row of a type policy uses at least one item. -/
theorem exists_active_item_for_type {K n : ℕ} [NeZero n]
    (ρ : TypePolicy K n) (k : UserType K) :
    ∃ j : Item n, ρ k j ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hsum := AppliedModelingLib.pmfToRealSum (ρ k)
  have hzero : (∑ j : Item n, (ρ k j).toReal) = 0 := by
    simp [hnone]
  linarith

/-- Items used with positive probability by type `0`. -/
noncomputable def typeZeroActiveItems {n : ℕ}
    (ρ : TypePolicy 2 n) : Finset (Item n) :=
  Finset.univ.filter fun j => ρ 0 j ≠ 0

theorem typeZeroActiveItems_nonempty {n : ℕ} [NeZero n]
    (ρ : TypePolicy 2 n) :
    (typeZeroActiveItems ρ).Nonempty := by
  rcases exists_active_item_for_type ρ 0 with ⟨j, hj⟩
  exact ⟨j, by simp [typeZeroActiveItems, hj]⟩

/-- The last item used by type `0`; this is the pivot candidate in Lemma 4. -/
noncomputable def lastActiveTypeZero {n : ℕ} [NeZero n]
    (ρ : TypePolicy 2 n) : Item n :=
  (typeZeroActiveItems ρ).max' (typeZeroActiveItems_nonempty ρ)

theorem lastActiveTypeZero_active {n : ℕ} [NeZero n]
    (ρ : TypePolicy 2 n) :
    ρ 0 (lastActiveTypeZero ρ) ≠ 0 := by
  have hmem :=
    Finset.max'_mem (typeZeroActiveItems ρ)
      (typeZeroActiveItems_nonempty ρ)
  simpa [lastActiveTypeZero, typeZeroActiveItems] using hmem

theorem typeZero_zero_after_lastActive {n : ℕ} [NeZero n]
    (ρ : TypePolicy 2 n) {j : Item n}
    (hj : (lastActiveTypeZero ρ).val < j.val) :
    ρ 0 j = 0 := by
  by_contra hne
  have hmem : j ∈ typeZeroActiveItems ρ := by
    simp [typeZeroActiveItems, hne]
  have hle :
      j ≤ lastActiveTypeZero ρ := by
    simpa [lastActiveTypeZero] using
      (typeZeroActiveItems ρ).le_max' j hmem
  have hle_val : j.val ≤ (lastActiveTypeZero ρ).val := hle
  omega

theorem typeZero_active_before_lastActive_of_zeroClosed {n : ℕ} [NeZero n]
    (ρ : TypePolicy 2 n)
    (hx : TwoTypeXZeroClosed ρ) {j : Item n}
    (hj : j.val < (lastActiveTypeZero ρ).val) :
    ρ 0 j ≠ 0 := by
  by_contra hz
  exact lastActiveTypeZero_active ρ (hx hj hz)

theorem mem_sharedItems_of_two_type_active {n : ℕ}
    (ρ : TypePolicy 2 n) {j : Item n}
    (hx : ρ 0 j ≠ 0) (hy : ρ 1 j ≠ 0) :
    j ∈ sharedItems ρ := by
  simp [sharedItems]
  exact Or.inl ⟨hx, hy⟩

/--
With the no-gap properties and the shared-item bound, type `1` is zero before
the last item used by type `0`.
-/
theorem typeOne_zero_before_lastActive_of_zeroClosed_of_sharedBound {n : ℕ}
    [NeZero n] (ρ : TypePolicy 2 n)
    (hx : TwoTypeXZeroClosed ρ)
    (hy : TwoTypeYZeroClosed ρ)
    (hshared : SharedItemsBound ρ)
    {j : Item n} (hj : j.val < (lastActiveTypeZero ρ).val) :
    ρ 1 j = 0 := by
  classical
  by_contra hyj_zero
  have hxj : ρ 0 j ≠ 0 :=
    typeZero_active_before_lastActive_of_zeroClosed ρ hx hj
  have hyj : ρ 1 j ≠ 0 := hyj_zero
  have hyt : ρ 1 (lastActiveTypeZero ρ) ≠ 0 := by
    by_contra hyt_zero
    exact hyj (hy hj hyt_zero)
  have hxt : ρ 0 (lastActiveTypeZero ρ) ≠ 0 :=
    lastActiveTypeZero_active ρ
  have hj_shared : j ∈ sharedItems ρ :=
    mem_sharedItems_of_two_type_active ρ hxj hyj
  have ht_shared : lastActiveTypeZero ρ ∈ sharedItems ρ :=
    mem_sharedItems_of_two_type_active ρ hxt hyt
  have hne : j ≠ lastActiveTypeZero ρ := by
    intro h
    subst h
    omega
  have hpair_subset :
      ({j, lastActiveTypeZero ρ} : Finset (Item n)) ⊆ sharedItems ρ := by
    intro a ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj_shared
    · exact ht_shared
  have htwo : 2 ≤ (sharedItems ρ).card := by
    have hcard :
        ({j, lastActiveTypeZero ρ} : Finset (Item n)).card = 2 := by
      simp [hne]
    calc
      2 = ({j, lastActiveTypeZero ρ} : Finset (Item n)).card := hcard.symm
      _ ≤ (sharedItems ρ).card := Finset.card_le_card hpair_subset
  have hone : (sharedItems ρ).card ≤ 1 := by
    simpa [SharedItemsBound] using hshared
  omega

/--
Appendix D, Lemma 4 threshold extraction: the support no-gap properties,
together with the Proposition 2 shared-item bound, force the sparse threshold
shape used in Lemma 5.
-/
theorem twoTypeThresholdSupport_of_zeroClosed_of_sharedBound {n : ℕ}
    [NeZero n] (ρ : TypePolicy 2 n)
    (hx : TwoTypeXZeroClosed ρ)
    (hy : TwoTypeYZeroClosed ρ)
    (hshared : SharedItemsBound ρ) :
    TwoTypeThresholdSupport ρ := by
  classical
  refine ⟨lastActiveTypeZero ρ, ?_, ?_⟩
  · intro j hj
    exact typeZero_zero_after_lastActive ρ hj
  · intro j hj
    exact typeOne_zero_before_lastActive_of_zeroClosed_of_sharedBound
      ρ hx hy hshared hj

/-- Variables of the reduced equality-form LP: one coordinate for every
type-item probability and one coordinate for the objective `ell`. -/
abbrev ReducedEqualityLPVariable (K n : ℕ) :=
  (UserType K × Item n) ⊕ Unit

/-- Constraints of the reduced equality-form LP.  The left summand contains
the `n` item-equalization equations and `K` row-sum equations; the right
summand contains the `nK` nonnegativity constraints. -/
abbrev ReducedEqualityLPConstraint (K n : ℕ) :=
  (Item n ⊕ UserType K) ⊕ (UserType K × Item n)

/-- A reduced LP candidate as a real vector, including the objective
coordinate. -/
noncomputable def reducedEqualityLPCandidate {K n : ℕ}
    (ρ : TypePolicy K n) (ell : ℝ) : ReducedEqualityLPVariable K n → ℝ
  | Sum.inl (k, j) => (ρ k j).toReal
  | Sum.inr _ => ell

/-- Coefficient vector of a constraint in a reduced equality-form LP.  Item
equation normals are supplied by the concrete utility model. -/
noncomputable def reducedEqualityLPConstraintNormal {K n : ℕ}
    (itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ) :
    ReducedEqualityLPConstraint K n →
      ReducedEqualityLPVariable K n → ℝ
  | Sum.inl (Sum.inl j), v => itemNormal j v
  | Sum.inl (Sum.inr k), Sum.inl (k', _j) => if k' = k then 1 else 0
  | Sum.inl (Sum.inr _k), Sum.inr _ => 0
  | Sum.inr (k, j), Sum.inl (k', j') => if k' = k ∧ j' = j then 1 else 0
  | Sum.inr (_k, _j), Sum.inr _ => 0

/-- A constraint is active at `(ρ, ell)` exactly in the source LP sense. -/
def ReducedEqualityLPConstraintActive {K n : ℕ}
    (itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ)
    (ρ : TypePolicy K n) (ell : ℝ) :
    ReducedEqualityLPConstraint K n → Prop
  | Sum.inl (Sum.inl j) =>
      (∑ v : ReducedEqualityLPVariable K n,
        itemNormal j v * reducedEqualityLPCandidate ρ ell v) = 0
  | Sum.inl (Sum.inr k) => (∑ j : Item n, (ρ k j).toReal) = 1
  | Sum.inr (k, j) => ρ k j = 0

/--
The standard active-basis definition of a basic feasible solution for the
paper's reduced equality-form LP.  In particular, the support bound is not a
field: it will be derived from the independent active basis below.
-/
structure ReducedEqualityLPActiveBasis {K n : ℕ}
    (itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ)
    (ρ : TypePolicy K n) (ell : ℝ) where
  equality_feasible :
    ∀ j : Item n,
      (∑ v : ReducedEqualityLPVariable K n,
        itemNormal j v * reducedEqualityLPCandidate ρ ell v) = 0
  basis : Finset (ReducedEqualityLPConstraint K n)
  basis_card : basis.card = n * K + 1
  basis_independent :
    LinearIndependent ℝ
      (fun c : {c // c ∈ basis} =>
        reducedEqualityLPConstraintNormal itemNormal c.1)
  basis_active :
    ∀ c ∈ basis, ReducedEqualityLPConstraintActive itemNormal ρ ell c

/-- A reduced policy is basic feasible when its equality-form LP constraints
contain a full active basis. -/
abbrev ReducedEqualityLPBasicFeasible {K n : ℕ}
    (itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ)
    (ρ : TypePolicy K n) (ell : ℝ) : Prop :=
  Nonempty (ReducedEqualityLPActiveBasis itemNormal ρ ell)

/-- The old support-count proposition, retained as a derived compatibility
interface for the paper's downstream Problem 6 and Problem 11 developments. -/
def BasicFeasibleSupportCertificate {K n : ℕ} (ρ : TypePolicy K n) : Prop :=
  n * K + 1 - (n + K) ≤ inactiveTypeItemPairsCard ρ

namespace ReducedEqualityLPBasicFeasible

/-- Equality constraints selected by an active basis. -/
noncomputable def equalityBasis {K n : ℕ}
    {itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ}
    {ρ : TypePolicy K n} {ell : ℝ}
    (h : ReducedEqualityLPActiveBasis itemNormal ρ ell) :
    Finset (Item n ⊕ UserType K) :=
  h.basis.toLeft

/-- Binding nonnegativity constraints selected by an active basis. -/
noncomputable def nonnegativityBasis {K n : ℕ}
    {itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ}
    {ρ : TypePolicy K n} {ell : ℝ}
    (h : ReducedEqualityLPActiveBasis itemNormal ρ ell) :
    Finset (UserType K × Item n) :=
  h.basis.toRight

theorem basis_card_eq_equality_add_nonnegativity {K n : ℕ}
    {itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ}
    {ρ : TypePolicy K n} {ell : ℝ}
    (h : ReducedEqualityLPActiveBasis itemNormal ρ ell) :
    h.basis.card = (equalityBasis h).card + (nonnegativityBasis h).card := by
  exact Finset.card_toLeft_add_card_toRight.symm

theorem equalityBasis_card_le {K n : ℕ}
    {itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ}
    {ρ : TypePolicy K n} {ell : ℝ}
    (h : ReducedEqualityLPActiveBasis itemNormal ρ ell) :
    (equalityBasis h).card ≤ n + K := by
  classical
  calc
    (equalityBasis h).card ≤ Fintype.card (Item n ⊕ UserType K) :=
      Finset.card_le_univ _
    _ = n + K := by simp [Item, UserType]

theorem nonnegativityBasis_card_le_inactive {K n : ℕ}
    {itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ}
    {ρ : TypePolicy K n} {ell : ℝ}
    (h : ReducedEqualityLPActiveBasis itemNormal ρ ell) :
    (nonnegativityBasis h).card ≤ inactiveTypeItemPairsCard ρ := by
  classical
  unfold inactiveTypeItemPairsCard AppliedModelingLib.Policy.inactivePairsCard
  change (nonnegativityBasis h).card ≤ (inactiveTypeItemPairs ρ).card
  apply Finset.card_le_card
  intro p hp
  have hpbasis :
      (Sum.inr p : ReducedEqualityLPConstraint K n) ∈ h.basis := by
    simpa [nonnegativityBasis] using hp
  have hactive := h.basis_active (Sum.inr p) hpbasis
  simpa [ReducedEqualityLPConstraintActive] using hactive

/-- A genuine LP basic feasible solution supplies the support-count certificate
used by the downstream paper arguments. -/
theorem basicFeasibleSupportCertificate {K n : ℕ}
    {itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ}
    {ρ : TypePolicy K n} {ell : ℝ}
    (h : ReducedEqualityLPBasicFeasible itemNormal ρ ell) :
    BasicFeasibleSupportCertificate ρ := by
  rcases h with ⟨h⟩
  have hsplit := basis_card_eq_equality_add_nonnegativity h
  have heq := equalityBasis_card_le h
  have hnonneg := nonnegativityBasis_card_le_inactive h
  unfold BasicFeasibleSupportCertificate
  have htotal :
      n * K + 1 = (equalityBasis h).card + (nonnegativityBasis h).card := by
    calc
      n * K + 1 = h.basis.card := h.basis_card.symm
      _ = (equalityBasis h).card + (nonnegativityBasis h).card := hsplit
  have htotal_le :
      n * K + 1 ≤ (n + K) + (nonnegativityBasis h).card := by
    omega
  have hzero_count :
      n * K + 1 - (n + K) ≤ (nonnegativityBasis h).card := by
    rw [Nat.sub_le_iff_le_add]
    simpa [Nat.add_comm] using htotal_le
  exact hzero_count.trans hnonneg

end ReducedEqualityLPBasicFeasible

/-- Active and inactive type-item pairs partition all `K * n` type-item pairs. -/
theorem activeTypeItemPairsCard_add_inactiveTypeItemPairsCard_eq {K n : ℕ}
    (ρ : TypePolicy K n) :
    activeTypeItemPairsCard ρ + inactiveTypeItemPairsCard ρ = K * n := by
  simpa [activeTypeItemPairsCard, inactiveTypeItemPairsCard, UserType, Item]
    using (AppliedModelingLib.Policy.activePairsCard_add_inactivePairsCard_eq_card
      (ρ := ρ))

/--
The paper's support-count arithmetic: once the basic-feasible-solution theorem
gives enough binding nonnegativity constraints, at most `n + K - 1` type-item
pairs can have positive support.
-/
theorem activePairsBound_of_basicFeasibleSupportCertificate {K n : ℕ}
    [NeZero K] [NeZero n]
    (ρ : TypePolicy K n) (hcert : BasicFeasibleSupportCertificate ρ) :
    ActivePairsBound ρ := by
  unfold ActivePairsBound activeTypeItemPairsCard
    BasicFeasibleSupportCertificate inactiveTypeItemPairsCard at *
  have hsupport :=
    AppliedModelingLib.Policy.activePairsCard_le_card_sub_of_inactivePairsCard_ge
      (ρ := ρ) hcert
  simp [UserType, Item, Nat.mul_comm] at hsupport
  exact le_trans hsupport (by omega)

/--
Appendix D, Lemma 4, Part 1 for the two-type Problem 6 LP: a basic feasible
solution has at most `n + 1` positive `x_j,y_j` variables.
-/
theorem activePairsCard_le_n_add_one_of_basicFeasibleSupportCertificate_two
    {n : ℕ} [NeZero n]
    (ρ : TypePolicy 2 n) (hcert : BasicFeasibleSupportCertificate ρ) :
    activeTypeItemPairsCard ρ ≤ n + 1 := by
  have hactive :=
    activePairsBound_of_basicFeasibleSupportCertificate ρ hcert
  unfold ActivePairsBound at hactive
  omega

/--
Appendix D, Lemma 4, Part 1 for the two-type Problem 6 LP: at least `n - 1`
of the `x_j,y_j` variables are zero in a basic feasible solution.
-/
theorem inactivePairsCard_ge_n_sub_one_of_basicFeasibleSupportCertificate_two
    {n : ℕ} [NeZero n]
    (ρ : TypePolicy 2 n) (hcert : BasicFeasibleSupportCertificate ρ) :
    n - 1 ≤ inactiveTypeItemPairsCard ρ := by
  unfold BasicFeasibleSupportCertificate at hcert
  omega

/--
Appendix D threshold-support count: a two-type threshold policy has at least
`n - 1` zero type-item coordinates.  Every item except the pivot is zero for
one of the two types.
-/
theorem inactivePairsCard_ge_n_sub_one_of_twoTypeThresholdSupport
    {n : ℕ} (ρ : TypePolicy 2 n) (hthreshold : TwoTypeThresholdSupport ρ) :
    n - 1 ≤ inactiveTypeItemPairsCard ρ := by
  classical
  rcases hthreshold with ⟨t, hx, hy⟩
  let s : Finset (Item n) := Finset.univ.erase t
  let f :
      {j : Item n // j ∈ s} →
        {p : UserType 2 × Item n // p ∈ inactiveTypeItemPairs ρ} :=
    fun j =>
      if hj : j.1.val < t.val then
        ⟨(1, j.1), by
          have hz : ρ 1 j.1 = 0 := hy hj
          simpa [inactiveTypeItemPairs, hz]⟩
      else
        ⟨(0, j.1), by
          have hne : j.1 ≠ t := by
            have hmem : j.1 ∈ (Finset.univ.erase t : Finset (Item n)) := by
              simpa only [s] using j.2
            exact (Finset.mem_erase.mp hmem).1
          have hgt : t.val < j.1.val := by
            have hval_ne : j.1.val ≠ t.val := by
              intro hval
              exact hne (Fin.ext hval)
            omega
          have hz : ρ 0 j.1 = 0 := hx hgt
          simpa [inactiveTypeItemPairs, hz]⟩
  have hf : Function.Injective f := by
    intro a b hab
    have f_snd (x : {j : Item n // j ∈ s}) :
        ((f x).1 : UserType 2 × Item n).2 = x.1 := by
      by_cases hx : x.1.val < t.val
      · have hx' : (x.1 : Item n) < t := hx
        simp [f, hx']
      · have hx' : ¬ (x.1 : Item n) < t := by
          intro h
          exact hx h
        simp [f, hx']
    have hitem : a.1 = b.1 := by
      have hp := congrArg (fun p :
        {p : UserType 2 × Item n // p ∈ inactiveTypeItemPairs ρ} =>
          (p.1 : UserType 2 × Item n).2) hab
      change ((f a).1 : UserType 2 × Item n).2 =
        ((f b).1 : UserType 2 × Item n).2 at hp
      rw [f_snd a, f_snd b] at hp
      exact hp
    exact Subtype.ext hitem
  have hcard :=
    Fintype.card_le_of_injective f hf
  have hs_card : Fintype.card {j : Item n // j ∈ s} = n - 1 := by
    simp [s, Item]
  have hinactive_card :
      Fintype.card {p : UserType 2 × Item n // p ∈ inactiveTypeItemPairs ρ} =
        inactiveTypeItemPairsCard ρ := by
    simpa [inactiveTypeItemPairsCard, inactiveTypeItemPairs] using
      (Fintype.card_coe (inactiveTypeItemPairs ρ))
  calc
    n - 1 = Fintype.card {j : Item n // j ∈ s} := hs_card.symm
    _ ≤ Fintype.card
        {p : UserType 2 × Item n // p ∈ inactiveTypeItemPairs ρ} := hcard
    _ = inactiveTypeItemPairsCard ρ := hinactive_card

/--
Appendix D threshold-support count as the paper's basic-feasible support
certificate in the two-type Problem 6 LP.
-/
theorem basicFeasibleSupportCertificate_of_twoTypeThresholdSupport
    {n : ℕ} (ρ : TypePolicy 2 n) (hthreshold : TwoTypeThresholdSupport ρ) :
    BasicFeasibleSupportCertificate ρ := by
  have hzero :=
    inactivePairsCard_ge_n_sub_one_of_twoTypeThresholdSupport ρ hthreshold
  unfold BasicFeasibleSupportCertificate
  omega

/-- Types that recommend item `j` with positive probability. -/
noncomputable def activeTypesForItem {K n : ℕ}
    (ρ : TypePolicy K n) (j : Item n) : Finset (UserType K) :=
  Finset.univ.filter fun k => ρ k j ≠ 0

@[simp] theorem mem_activeTypesForItem {K n : ℕ}
    (ρ : TypePolicy K n) (j : Item n) (k : UserType K) :
    k ∈ activeTypesForItem ρ j ↔ ρ k j ≠ 0 := by
  simp [activeTypesForItem]

noncomputable def primaryActiveType {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0)
    (j : Item n) : UserType K :=
  Classical.choose (hcover j)

theorem primaryActiveType_spec {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0)
    (j : Item n) :
    ρ (primaryActiveType ρ hcover j) j ≠ 0 :=
  Classical.choose_spec (hcover j)

theorem exists_activeType_ne_primary_of_shared {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0)
    {j : Item n} (hj : j ∈ sharedItems ρ) :
    ∃ k, k ≠ primaryActiveType ρ hcover j ∧ ρ k j ≠ 0 := by
  rcases (AppliedModelingLib.Policy.mem_multiAssignedActions ρ j).mp hj with
    ⟨k, k', hne, hk, hk'⟩
  by_cases hp : primaryActiveType ρ hcover j = k
  · refine ⟨k', ?_, hk'⟩
    intro hkp
    exact hne (hp.symm.trans hkp.symm)
  · exact ⟨k, (by intro h; exact hp h.symm), hk⟩

noncomputable def secondaryActiveType {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0)
    (j : {j : Item n // j ∈ sharedItems ρ}) : UserType K :=
  Classical.choose (exists_activeType_ne_primary_of_shared ρ hcover j.property)

theorem secondaryActiveType_ne_primary {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0)
    (j : {j : Item n // j ∈ sharedItems ρ}) :
    secondaryActiveType ρ hcover j ≠ primaryActiveType ρ hcover j :=
  (Classical.choose_spec
    (exists_activeType_ne_primary_of_shared ρ hcover j.property)).1

theorem secondaryActiveType_spec {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0)
    (j : {j : Item n // j ∈ sharedItems ρ}) :
    ρ (secondaryActiveType ρ hcover j) j.1 ≠ 0 :=
  (Classical.choose_spec
    (exists_activeType_ne_primary_of_shared ρ hcover j.property)).2

noncomputable def itemSharedInjection {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    (Item n ⊕ {j : Item n // j ∈ sharedItems ρ}) →
      {p : UserType K × Item n // p ∈ activeTypeItemPairs ρ}
  | Sum.inl j =>
      ⟨(primaryActiveType ρ hcover j, j), by
        simpa [activeTypeItemPairs] using primaryActiveType_spec ρ hcover j⟩
  | Sum.inr j =>
      ⟨(secondaryActiveType ρ hcover j, j.1), by
        simpa [activeTypeItemPairs] using secondaryActiveType_spec ρ hcover j⟩

theorem itemSharedInjection_injective {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    Function.Injective (itemSharedInjection ρ hcover) := by
  intro x y hxy
  cases x with
  | inl j =>
      cases y with
      | inl j' =>
          simp [itemSharedInjection] at hxy
          exact congrArg Sum.inl hxy.2
      | inr sj =>
          simp [itemSharedInjection] at hxy
          have hitem : j = sj.1 := hxy.2
          subst hitem
          exact False.elim ((secondaryActiveType_ne_primary ρ hcover sj) hxy.1.symm)
  | inr sj =>
      cases y with
      | inl j =>
          simp [itemSharedInjection] at hxy
          have hitem : sj.1 = j := hxy.2
          subst hitem
          exact False.elim ((secondaryActiveType_ne_primary ρ hcover sj) hxy.1)
      | inr sj' =>
          simp [itemSharedInjection] at hxy
          exact congrArg Sum.inr hxy.2

/--
If every item is recommended by some type, then active type-item pairs contain
one pair for every item plus one additional pair for every shared item.
-/
theorem card_items_add_sharedItems_le_activePairsCard {K n : ℕ}
    (ρ : TypePolicy K n) (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    n + (sharedItems ρ).card ≤ activeTypeItemPairsCard ρ := by
  have hcard :=
    Fintype.card_le_of_injective (itemSharedInjection ρ hcover)
      (itemSharedInjection_injective ρ hcover)
  have hdomain :
      Fintype.card (Item n ⊕ {j : Item n // j ∈ sharedItems ρ}) =
        n + (sharedItems ρ).card := by
    simp [Fintype.card_sum, Fintype.card_coe, Item]
  have hcodomain :
      Fintype.card {p : UserType K × Item n // p ∈ activeTypeItemPairs ρ} =
        (activeTypeItemPairs ρ).card := by
    exact Fintype.card_coe (activeTypeItemPairs ρ)
  rw [hdomain, hcodomain] at hcard
  simpa [activeTypeItemPairsCard] using hcard

theorem sharedItemsBound_of_activePairsBound_of_item_coverage {K n : ℕ}
    [NeZero K]
    (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    SharedItemsBound ρ := by
  have hlower := card_items_add_sharedItems_le_activePairsCard ρ hcover
  unfold ActivePairsBound at hactive
  unfold SharedItemsBound
  have hK : 1 ≤ K := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne K))
  have hle : n + (sharedItems ρ).card ≤ n + (K - 1) := by
    rw [← Nat.add_sub_assoc hK n]
    exact le_trans hlower hactive
  exact Nat.add_le_add_iff_left.mp hle

theorem sparseShape_of_activePairsBound_of_item_coverage {K n : ℕ}
    [NeZero K]
    (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    SparseShape ρ := by
  exact ⟨hactive, sharedItemsBound_of_activePairsBound_of_item_coverage
    ρ hactive hcover⟩

end TypePolicy
end GCG24UserItemFairness
