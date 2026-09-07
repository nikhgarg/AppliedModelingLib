import GCG24UserItemFairness.Symmetry

open scoped BigOperators
open AppliedModelingLib

namespace GCG24UserItemFairness

namespace RecommendationModel

/-- The feasible set for Problem 1 at fairness level `γ`. -/
def feasiblePoliciesAtLevelSet {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : Set (Policy m n) :=
  {ρ | feasibleAtLevel W γ ρ}

/-- The optimal-solution set for Problem 1 at fairness level `γ`. -/
def optimalPoliciesAtLevelSet {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : Set (Policy m n) :=
  {ρ | IsOptimalAtLevel W γ ρ}

/-- The feasible region restricted to type-symmetric policies. -/
def symmetricFeasiblePolicies {m n K : ℕ} [NeZero n]
    (S : SymmetricData m n K) (γ : ℝ) : Set (Policy m n) :=
  {ρ | UserTypeAssignment.IsTypeSymmetric S.types ρ ∧ feasibleAtLevel S.model γ ρ}

/-- The optimal region restricted to type-symmetric policies. -/
def symmetricOptimalPolicies {m n K : ℕ} [NeZero m] [NeZero n]
    (S : SymmetricData m n K) (γ : ℝ) : Set (Policy m n) :=
  {ρ | UserTypeAssignment.IsTypeSymmetric S.types ρ ∧ IsOptimalAtLevel S.model γ ρ}

/-- Item-fairness values attainable by type-symmetric user-level policies. -/
def symmetricAttainableItemFairnessSet {m n K : ℕ} [NeZero n]
    (S : SymmetricData m n K) : Set ℝ :=
  {r | ∃ ρ : Policy m n,
    UserTypeAssignment.IsTypeSymmetric S.types ρ ∧ r = itemFairness S.model ρ}

/-- Supremal item fairness over type-symmetric user-level policies. -/
noncomputable def symmetricOptimalItemFairness {m n K : ℕ} [NeZero n]
    (S : SymmetricData m n K) : ℝ :=
  sSup (symmetricAttainableItemFairnessSet S)

/--
The source-shaped user-coordinate equality LP from Proposition 1, specialized
to the symmetric policy set `S_symm` used in Proposition 2.  The variables are
the original user-item policy coordinates together with the objective coordinate
`ell`; type-level coordinates are not part of this object.
-/
structure UserSymmetricEqualityLP (m n K : ℕ) where
  model : RecommendationModel m n
  types : UserTypeAssignment m K

namespace UserSymmetricEqualityLP

/-- User-coordinate LP variables: every original user-item coordinate plus
the objective variable `ell`. -/
abbrev Variable (m n : ℕ) :=
  (User m × Item n) ⊕ Unit

/--
User-coordinate LP constraints: item equalities, user simplex row sums, the
finite linear equalities defining `S_symm`, and policy-coordinate
nonnegativity constraints.
-/
abbrev Constraint (m n K : ℕ) :=
  ((Item n ⊕ User m) ⊕
      GCG24UserItemFairness.UserTypeAssignment.TypeSymmetryLinearConstraintIndex m n) ⊕
    (User m × Item n)

/-- The real vector associated with a policy and objective candidate. -/
noncomputable def candidate {m n K : ℕ}
    (_L : UserSymmetricEqualityLP m n K) (ρ : Policy m n) (ell : ℝ) :
    Variable m n → ℝ
  | Sum.inl (u, j) => (ρ u j).toReal
  | Sum.inr _ => ell

/-- Descend a feasible user-level LP candidate to type-level coordinates by
reading the policy at representative users and preserving `ell`. -/
noncomputable def reduceUserSymmetricEqualityLP {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K)
    (reps : GCG24UserItemFairness.UserTypeAssignment.TypeRepresentatives L.types)
    (ρ : Policy m n) (ell : ℝ) :
    TypePolicy.ReducedEqualityLPVariable K n → ℝ :=
  TypePolicy.reducedEqualityLPCandidate
    (GCG24UserItemFairness.UserTypeAssignment.descendTypePolicy L.types reps ρ)
    ell

/-- Lift a type-level LP candidate back to the source user-level coordinates by
copying the type row to every user of that type and preserving `ell`. -/
noncomputable def liftReducedEqualityLP {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K)
    (ρ : TypePolicy K n) (ell : ℝ) :
    Variable m n → ℝ :=
  candidate L
    (GCG24UserItemFairness.UserTypeAssignment.liftTypePolicy L.types ρ)
    ell

@[simp] theorem reduceUserSymmetricEqualityLP_type_coordinate {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K)
    (reps : GCG24UserItemFairness.UserTypeAssignment.TypeRepresentatives L.types)
    (ρ : Policy m n) (ell : ℝ) (k : UserType K) (j : Item n) :
    reduceUserSymmetricEqualityLP L reps ρ ell (Sum.inl (k, j)) =
      candidate L ρ ell (Sum.inl (reps.repr k, j)) := rfl

@[simp] theorem reduceUserSymmetricEqualityLP_ell_coordinate {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K)
    (reps : GCG24UserItemFairness.UserTypeAssignment.TypeRepresentatives L.types)
    (ρ : Policy m n) (ell : ℝ) (u : Unit) :
    reduceUserSymmetricEqualityLP L reps ρ ell (Sum.inr u) =
      candidate L ρ ell (Sum.inr u) := rfl

@[simp] theorem liftReducedEqualityLP_user_coordinate {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K)
    (ρ : TypePolicy K n) (ell : ℝ) (u : User m) (j : Item n) :
    liftReducedEqualityLP L ρ ell (Sum.inl (u, j)) =
      TypePolicy.reducedEqualityLPCandidate ρ ell
        (Sum.inl (L.types.toType u, j)) := rfl

@[simp] theorem liftReducedEqualityLP_ell_coordinate {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K)
    (ρ : TypePolicy K n) (ell : ℝ) (u : Unit) :
    liftReducedEqualityLP L ρ ell (Sum.inr u) =
      TypePolicy.reducedEqualityLPCandidate ρ ell (Sum.inr u) := rfl

/-- The forward coordinate map is independent of representatives on the
symmetric subspace `S_symm`. -/
theorem reduceUserSymmetricEqualityLP_eq_of_isTypeSymmetric {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K)
    (reps reps' : GCG24UserItemFairness.UserTypeAssignment.TypeRepresentatives L.types)
    (ρ : Policy m n) (ell : ℝ)
    (hρ : GCG24UserItemFairness.UserTypeAssignment.IsTypeSymmetric L.types ρ) :
    reduceUserSymmetricEqualityLP L reps ρ ell =
      reduceUserSymmetricEqualityLP L reps' ρ ell := by
  simp [reduceUserSymmetricEqualityLP,
    GCG24UserItemFairness.UserTypeAssignment.descendTypePolicy_eq_of_isTypeSymmetric
      L.types reps reps' ρ hρ]

/-- Reducing a lifted type-level candidate recovers the original reduced
candidate. -/
theorem reduceUserSymmetricEqualityLP_liftReducedEqualityLP {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K)
    (reps : GCG24UserItemFairness.UserTypeAssignment.TypeRepresentatives L.types)
    (ρ : TypePolicy K n) (ell : ℝ) :
    reduceUserSymmetricEqualityLP L reps
        (GCG24UserItemFairness.UserTypeAssignment.liftTypePolicy L.types ρ) ell =
      TypePolicy.reducedEqualityLPCandidate ρ ell := by
  simp [reduceUserSymmetricEqualityLP]

/-- Lifting the reduction of a type-symmetric user-level candidate recovers the
original user-level candidate. -/
theorem liftReducedEqualityLP_reduceUserSymmetricEqualityLP
    {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K)
    (reps : GCG24UserItemFairness.UserTypeAssignment.TypeRepresentatives L.types)
    (ρ : Policy m n) (ell : ℝ)
    (hρ : GCG24UserItemFairness.UserTypeAssignment.IsTypeSymmetric L.types ρ) :
    liftReducedEqualityLP L
        (GCG24UserItemFairness.UserTypeAssignment.descendTypePolicy L.types reps ρ)
        ell =
      candidate L ρ ell := by
  have hlift :
      GCG24UserItemFairness.UserTypeAssignment.liftTypePolicy L.types
          (GCG24UserItemFairness.UserTypeAssignment.descendTypePolicy L.types reps ρ) =
        ρ :=
    GCG24UserItemFairness.UserTypeAssignment.liftTypePolicy_descendTypePolicy_eq_of_isTypeSymmetric
      L.types reps ρ hρ
  simp [liftReducedEqualityLP, hlift]

/-- The item-`j` equality normal in the source user-coordinate LP. -/
noncomputable def itemEqualityNormal {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K) (j : Item n) :
    Variable m n → ℝ
  | Sum.inl (u, j') =>
      if j' = j then L.model.utility u j / itemNormalizer L.model j else 0
  | Sum.inr _ => -1

/-- Coefficient vector of a source user-coordinate LP constraint. -/
noncomputable def constraintNormal {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K) :
    Constraint m n K → Variable m n → ℝ
  | Sum.inl (Sum.inl (Sum.inl j)), v => itemEqualityNormal L j v
  | Sum.inl (Sum.inl (Sum.inr u)), Sum.inl (u', _j) => if u' = u then 1 else 0
  | Sum.inl (Sum.inl (Sum.inr _u)), Sum.inr _ => 0
  | Sum.inl (Sum.inr c), Sum.inl (u, j) =>
      GCG24UserItemFairness.UserTypeAssignment.typeSymmetryLinearCoefficient
        L.types c u j
  | Sum.inl (Sum.inr _c), Sum.inr _ => 0
  | Sum.inr (u, j), Sum.inl (u', j') => if u' = u ∧ j' = j then 1 else 0
  | Sum.inr (_u, _j), Sum.inr _ => 0

/-- A source LP constraint is active at `(ρ, ell)` in the usual BFS sense. -/
def ConstraintActive {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K) (ρ : Policy m n) (ell : ℝ) :
    Constraint m n K → Prop
  | Sum.inl (Sum.inl (Sum.inl j)) =>
      propositionOneItemEqualityExpression L.model j ρ ell = 0
  | Sum.inl (Sum.inl (Sum.inr u)) => ∑ j : Item n, (ρ u j).toReal = 1
  | Sum.inl (Sum.inr c) =>
      GCG24UserItemFairness.UserTypeAssignment.typeSymmetryLinearExpression
        L.types c ρ = 0
  | Sum.inr (u, j) => ρ u j = 0

/--
Feasibility for the source user-coordinate LP: user simplex rows,
nonnegativity, membership in `S_symm`, and all item-equalization equations.
The first two clauses are explicit here even though `Policy` already packages
them, because they are rows of the paper-facing LP.
-/
def Feasible {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K) (ρ : Policy m n) (ell : ℝ) : Prop :=
  (∀ u : User m, ∑ j : Item n, (ρ u j).toReal = 1) ∧
    (∀ u : User m, ∀ j : Item n, 0 ≤ (ρ u j).toReal) ∧
      GCG24UserItemFairness.UserTypeAssignment.IsTypeSymmetric L.types ρ ∧
        ∀ j : Item n, propositionOneItemEqualityExpression L.model j ρ ell = 0

/-- Objective optimality in the source user-coordinate equality LP. -/
def Optimal {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K) (ρ : Policy m n) (ell : ℝ) : Prop :=
  L.Feasible ρ ell ∧
    ∀ (ρ' : Policy m n) (ell' : ℝ), L.Feasible ρ' ell' → ell' ≤ ell

/--
A basic feasible solution of the source user-coordinate LP: a feasible point
with a full-cardinality linearly independent active constraint basis over the
original `m * n + 1` variables.
-/
structure ActiveBasis {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K) (ρ : Policy m n) (ell : ℝ) where
  feasible : L.Feasible ρ ell
  basis : Finset (Constraint m n K)
  basis_card : basis.card = m * n + 1
  basis_independent :
    LinearIndependent ℝ
      (fun c : {c // c ∈ basis} => constraintNormal L c.1)
  basis_active :
    ∀ c ∈ basis, ConstraintActive L ρ ell c

/-- Source-side basic feasibility for Proposition 1's LP on `S_symm`. -/
abbrev BasicFeasible {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K) (ρ : Policy m n) (ell : ℝ) : Prop :=
  Nonempty (ActiveBasis L ρ ell)

/-- Construct the source user-coordinate LP attached to symmetric model data. -/
def ofSymmetricData {m n K : ℕ}
    (S : SymmetricData m n K) : UserSymmetricEqualityLP m n K where
  model := S.model
  types := S.types

/--
The source-shaped feasibility predicate is exactly Proposition 1's equality LP
feasibility when condition (i)'s finite linear description is instantiated by
the explicit coordinate description of `S_symm`.
-/
theorem feasible_iff_source_problem5 {m n K : ℕ}
    (L : UserSymmetricEqualityLP m n K) (ρ : Policy m n) (ell : ℝ) :
    L.Feasible ρ ell ↔
      PropositionOneLPFeasible L.model
        (GCG24UserItemFairness.UserTypeAssignment.symmetricPoliciesFiniteLinearDescription
          (n := n) L.types) ρ ell := by
  classical
  let D :=
    GCG24UserItemFairness.UserTypeAssignment.symmetricPoliciesFiniteLinearDescription
      (n := n) L.types
  constructor
  · intro h
    refine ⟨?_, h.2.2.2⟩
    exact (D.satisfies_iff_mem ρ).mpr (by
      simpa [GCG24UserItemFairness.UserTypeAssignment.SymmetricPolicies,
        GCG24UserItemFairness.UserTypeAssignment.IsTypeSymmetric] using h.2.2.1)
  · intro h
    refine ⟨?_, ?_, ?_, h.2⟩
    · intro u
      exact AppliedModelingLib.pmfToRealSum (ρ u)
    · intro u j
      exact ENNReal.toReal_nonneg
    · have hmem := (D.satisfies_iff_mem ρ).mp h.1
      simpa [GCG24UserItemFairness.UserTypeAssignment.SymmetricPolicies,
        GCG24UserItemFairness.UserTypeAssignment.IsTypeSymmetric] using hmem

end UserSymmetricEqualityLP

/--
Source-facing freeze for Proposition 2's LP presentation: the concrete
user-coordinate LP over `S_symm` is the same Problem-(5) equality LP obtained
from Proposition 1 with the explicit finite linear description of `S_symm`.
-/
theorem userSymmetricEqualityLP_eq_source_problem5 {m n K : ℕ}
    (S : SymmetricData m n K) (ρ : Policy m n) (ell : ℝ) :
    (UserSymmetricEqualityLP.ofSymmetricData S).Feasible ρ ell ↔
      PropositionOneLPFeasible S.model
        (GCG24UserItemFairness.UserTypeAssignment.symmetricPoliciesFiniteLinearDescription
          (n := n) S.types) ρ ell := by
  exact UserSymmetricEqualityLP.feasible_iff_source_problem5
    (UserSymmetricEqualityLP.ofSymmetricData S) ρ ell

end RecommendationModel

namespace RecommendationModel.UserTypeAssignment

/-- The cardinality of a user type, viewed as the size of its fiber. -/
def typeCard {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (k : UserType K) : ℕ :=
  (Finset.univ.filter fun u => τ.toType u = k).card

/-- The population share of a type, as a real weight for the reduced LP.

The source model's type masses are population proportions.  The unnormalized
fiber cardinality is retained by `typeCard` for the source-to-reduction sum
identities, while this weight is its normalization by the total population.
-/
noncomputable def typeWeight {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (k : UserType K) : ℝ :=
  (typeCard τ k : ℝ) / (m : ℝ)

@[simp] theorem typeWeight_nonneg {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (k : UserType K) :
    0 ≤ typeWeight τ k := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

end RecommendationModel.UserTypeAssignment

/--
A type-weighted reduction of the recommendation problem. This is the natural LP-side
object once users with identical utility rows have been merged into types.
-/
structure TypeWeightedRecommendationModel (K n : ℕ) where
  utility : UserType K → Item n → ℝ
  weight : UserType K → ℝ

namespace TypeWeightedRecommendationModel

/-- Nonnegativity of the type weights. -/
def NonnegativeWeights {K n : ℕ} (T : TypeWeightedRecommendationModel K n) : Prop :=
  ∀ k, 0 ≤ T.weight k

/-- Entrywise nonnegativity of the reduced utility matrix. -/
def NonnegativeUtilities {K n : ℕ} (T : TypeWeightedRecommendationModel K n) : Prop :=
  ∀ k j, 0 ≤ T.utility k j

/-- Strict positivity of all type weights. -/
def PositiveWeights {K n : ℕ} (T : TypeWeightedRecommendationModel K n) : Prop :=
  ∀ k, 0 < T.weight k

/-- Strict positivity of all reduced utility entries. -/
def PositiveUtilities {K n : ℕ} (T : TypeWeightedRecommendationModel K n) : Prop :=
  ∀ k j, 0 < T.utility k j

/-- Every user type has at least one strictly positive item. -/
def RowHasPositiveItem {K n : ℕ} (T : TypeWeightedRecommendationModel K n) : Prop :=
  ∀ k, ∃ j, 0 < T.utility k j

theorem nonnegativeWeights_of_positiveWeights {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (hWeight : T.PositiveWeights) :
    T.NonnegativeWeights := by
  intro k
  exact (hWeight k).le

theorem nonnegativeUtilities_of_positiveUtilities {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (hUtil : T.PositiveUtilities) :
    T.NonnegativeUtilities := by
  intro k j
  exact (hUtil k j).le

/-- Raw expected utility received by a type `k`. -/
noncomputable def rawTypeUtility {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n) (k : UserType K) : ℝ :=
  AppliedModelingLib.Policy.agentScore ρ T.utility k

/-- Best item utility available to type `k`. -/
noncomputable def bestItemUtility {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (k : UserType K) : ℝ :=
  AppliedModelingLib.finiteMax (T.utility k)

/-- Normalized utility received by type `k`. -/
noncomputable def normalizedTypeUtility {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n) (k : UserType K) : ℝ :=
  rawTypeUtility T ρ k / bestItemUtility T k

/-- Minimum normalized utility over user types. -/
noncomputable def typeFairness {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n) : ℝ :=
  AppliedModelingLib.finiteMin (normalizedTypeUtility T ρ)

/-- Weighted raw utility accumulated by an item. -/
noncomputable def rawItemUtility {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n) (j : Item n) : ℝ :=
  ∑ k, T.weight k * T.utility k j * (ρ k j).toReal

/-- Weighted item normalizer. -/
noncomputable def itemNormalizer {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (j : Item n) : ℝ :=
  ∑ k, T.weight k * T.utility k j

/-- Normalized item utility in the reduced type-level problem. -/
noncomputable def normalizedItemUtility {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n) (j : Item n) : ℝ :=
  let denom := itemNormalizer T j
  if h : denom = 0 then 0 else rawItemUtility T ρ j / denom

/-- Coefficient vector of the item-`j` equality in the reduced LP from
Proposition 2. -/
noncomputable def equalityLPItemNormal {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (j : Item n) :
    TypePolicy.ReducedEqualityLPVariable K n → ℝ
  | Sum.inl (k, j') =>
      if j' = j then T.weight k * T.utility k j / itemNormalizer T j else 0
  | Sum.inr _ => -1

/-- The source basic-feasible-solution antecedent for the concrete reduced LP.
Its active basis is checked against the actual item-equality coefficients. -/
abbrev IsEqualityLPBasicFeasible {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (ρ : TypePolicy K n) (ell : ℝ) : Prop :=
  TypePolicy.ReducedEqualityLPBasicFeasible (equalityLPItemNormal T) ρ ell

/-- Feasibility for the reduced equality-form LP before choosing an active
basis: all item-equalization equations hold. Row sums and nonnegativity are
already packaged by the `TypePolicy` PMF rows. -/
def EqualityLPFeasible {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (ρ : TypePolicy K n) (ell : ℝ) : Prop :=
  ∀ j : Item n,
    (∑ v : TypePolicy.ReducedEqualityLPVariable K n,
      equalityLPItemNormal T j v *
        TypePolicy.reducedEqualityLPCandidate ρ ell v) = 0

/-- Objective optimality in the reduced equality-form LP. -/
def EqualityLPOptimal {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (ρ : TypePolicy K n) (ell : ℝ) : Prop :=
  T.EqualityLPFeasible ρ ell ∧
    ∀ (ρ' : TypePolicy K n) (ell' : ℝ),
      T.EqualityLPFeasible ρ' ell' → ell' ≤ ell

theorem equalityLPFeasible_of_basicFeasible {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (ρ : TypePolicy K n) (ell : ℝ)
    (hbfs : T.IsEqualityLPBasicFeasible ρ ell) :
    T.EqualityLPFeasible ρ ell := by
  rcases hbfs with ⟨hbasis⟩
  exact hbasis.equality_feasible

/-- The reduced item-equation dot product is precisely `I_j(ρ) - ell` when
the item normalizer is nonzero. -/
theorem equalityLPItemNormal_dot_candidate_eq {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (ρ : TypePolicy K n) (ell : ℝ) (j : Item n)
    (hden : itemNormalizer T j ≠ 0) :
    (∑ v : TypePolicy.ReducedEqualityLPVariable K n,
        equalityLPItemNormal T j v *
          TypePolicy.reducedEqualityLPCandidate ρ ell v) =
      normalizedItemUtility T ρ j - ell := by
  classical
  rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  simp [equalityLPItemNormal, TypePolicy.reducedEqualityLPCandidate,
    normalizedItemUtility, rawItemUtility, hden, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro k _hk
  ring

/-- Minimum normalized item utility in the reduced problem. -/
noncomputable def itemFairness {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n) : ℝ :=
  AppliedModelingLib.finiteMin (normalizedItemUtility T ρ)

/-- The policy that recommends every item uniformly to every type. -/
noncomputable def uniformTypePolicy {K n : ℕ} [NeZero n] : TypePolicy K n :=
  fun _ => AppliedModelingLib.uniformPMF (Item n)

@[simp] theorem uniformTypePolicy_apply_toReal {K n : ℕ} [NeZero n]
    (k : UserType K) (j : Item n) :
    ((uniformTypePolicy (K := K) (n := n) k) j).toReal = (n : ℝ)⁻¹ := by
  simpa [uniformTypePolicy, Item] using
    (AppliedModelingLib.uniformPMF_apply_toReal (α := Item n) j)

theorem uniformTypePolicy_apply_toReal_pos {K n : ℕ} [NeZero n]
    (k : UserType K) (j : Item n) :
    0 < ((uniformTypePolicy (K := K) (n := n) k) j).toReal := by
  simpa [uniformTypePolicy] using
    (AppliedModelingLib.uniformPMF_apply_toReal_pos (α := Item n) j)

/--
A real-vector presentation of reduced policies as one standard simplex row per
user type. This mirrors the original-model compactness layer.
-/
abbrev TypePolicySimplexVector (K n : ℕ) :=
  UserType K → stdSimplex ℝ (Item n)

/-- Convert a reduced real simplex vector back to the `PMF`-valued type policy. -/
noncomputable def typePolicyOfSimplexVector {K n : ℕ}
    (x : TypePolicySimplexVector K n) : TypePolicy K n :=
  fun k =>
    RecommendationModel.pmfOfRealItemVector
      ((x k : stdSimplex ℝ (Item n)) : Item n → ℝ)
      (x k).2.1
      (x k).2.2

@[simp] theorem typePolicyOfSimplexVector_apply_toReal {K n : ℕ}
    (x : TypePolicySimplexVector K n) (k : UserType K) (j : Item n) :
    ((typePolicyOfSimplexVector x k) j).toReal =
      ((x k : stdSimplex ℝ (Item n)) : Item n → ℝ) j := by
  simp [typePolicyOfSimplexVector]

/-- Convert a reduced `PMF`-valued type policy into its real simplex-vector presentation. -/
noncomputable def simplexVectorOfTypePolicy {K n : ℕ}
    (ρ : TypePolicy K n) : TypePolicySimplexVector K n :=
  fun k =>
    ⟨fun j => (ρ k j).toReal,
      ⟨fun j => ENNReal.toReal_nonneg,
        AppliedModelingLib.pmfToRealSum (ρ k)⟩⟩

/-- Weighted raw item utility evaluated on the reduced simplex-vector presentation. -/
noncomputable def rawItemUtilityVector {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (x : TypePolicySimplexVector K n) (j : Item n) : ℝ :=
  ∑ k : UserType K,
    (T.weight k * T.utility k j) *
      ((x k : stdSimplex ℝ (Item n)) : Item n → ℝ) j

/-- Normalized item utility evaluated on the reduced simplex-vector presentation. -/
noncomputable def normalizedItemUtilityVector {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (x : TypePolicySimplexVector K n) (j : Item n) : ℝ :=
  let denom := itemNormalizer T j
  if h : denom = 0 then 0 else rawItemUtilityVector T x j / denom

/-- Minimum item fairness evaluated on the reduced simplex-vector presentation. -/
noncomputable def itemFairnessVector {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (x : TypePolicySimplexVector K n) : ℝ :=
  AppliedModelingLib.finiteMin (normalizedItemUtilityVector T x)

theorem rawItemUtility_typePolicyOfSimplexVector_eq {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (x : TypePolicySimplexVector K n) (j : Item n) :
    rawItemUtility T (typePolicyOfSimplexVector x) j =
      rawItemUtilityVector T x j := by
  simp [rawItemUtility, rawItemUtilityVector]

theorem normalizedItemUtility_typePolicyOfSimplexVector_eq {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (x : TypePolicySimplexVector K n) (j : Item n) :
    normalizedItemUtility T (typePolicyOfSimplexVector x) j =
      normalizedItemUtilityVector T x j := by
  unfold normalizedItemUtility normalizedItemUtilityVector
  rw [rawItemUtility_typePolicyOfSimplexVector_eq]

theorem itemFairness_typePolicyOfSimplexVector_eq {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (x : TypePolicySimplexVector K n) :
    itemFairness T (typePolicyOfSimplexVector x) =
      itemFairnessVector T x := by
  unfold itemFairness itemFairnessVector
  apply congrArg
  funext j
  exact normalizedItemUtility_typePolicyOfSimplexVector_eq T x j

theorem rawItemUtilityVector_simplexVectorOfTypePolicy_eq {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (ρ : TypePolicy K n) (j : Item n) :
    rawItemUtilityVector T (simplexVectorOfTypePolicy ρ) j =
      rawItemUtility T ρ j := by
  unfold rawItemUtilityVector rawItemUtility simplexVectorOfTypePolicy
  rfl

theorem normalizedItemUtilityVector_simplexVectorOfTypePolicy_eq {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (ρ : TypePolicy K n) (j : Item n) :
    normalizedItemUtilityVector T (simplexVectorOfTypePolicy ρ) j =
      normalizedItemUtility T ρ j := by
  unfold normalizedItemUtilityVector normalizedItemUtility
  rw [rawItemUtilityVector_simplexVectorOfTypePolicy_eq]

theorem itemFairnessVector_simplexVectorOfTypePolicy_eq {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (ρ : TypePolicy K n) :
    itemFairnessVector T (simplexVectorOfTypePolicy ρ) =
      itemFairness T ρ := by
  unfold itemFairnessVector itemFairness
  apply congrArg
  funext j
  exact normalizedItemUtilityVector_simplexVectorOfTypePolicy_eq T ρ j

theorem rawItemUtilityVector_continuous {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (j : Item n) :
    Continuous (fun x : TypePolicySimplexVector K n =>
      rawItemUtilityVector T x j) := by
  unfold rawItemUtilityVector
  apply continuous_finset_sum
  intro k _hk
  have hrow : Continuous (fun x : TypePolicySimplexVector K n => x k) :=
    continuous_apply k
  have hcoord : Continuous (fun x : TypePolicySimplexVector K n =>
      ((x k : stdSimplex ℝ (Item n)) : Item n → ℝ) j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp hrow)
  exact continuous_const.mul hcoord

theorem normalizedItemUtilityVector_continuous {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (j : Item n) :
    Continuous (fun x : TypePolicySimplexVector K n =>
      normalizedItemUtilityVector T x j) := by
  unfold normalizedItemUtilityVector
  by_cases hden : itemNormalizer T j = 0
  · simpa [hden] using (continuous_const : Continuous
      (fun _ : TypePolicySimplexVector K n => (0 : ℝ)))
  · simpa [hden] using
      (rawItemUtilityVector_continuous T j).div_const (itemNormalizer T j)

theorem itemFairnessVector_continuous {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) :
    Continuous (fun x : TypePolicySimplexVector K n =>
      itemFairnessVector T x) := by
  have hcont : ∀ j : Item n,
      Continuous (fun x : TypePolicySimplexVector K n =>
        normalizedItemUtilityVector T x j) :=
    fun j => normalizedItemUtilityVector_continuous T j
  unfold itemFairnessVector AppliedModelingLib.finiteMin
  fun_prop

/-- Raw type utility evaluated on the reduced simplex-vector presentation. -/
noncomputable def rawTypeUtilityVector {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (x : TypePolicySimplexVector K n) (k : UserType K) : ℝ :=
  ∑ j : Item n,
    ((x k : stdSimplex ℝ (Item n)) : Item n → ℝ) j * T.utility k j

/-- Normalized type utility evaluated on the reduced simplex-vector presentation. -/
noncomputable def normalizedTypeUtilityVector {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (x : TypePolicySimplexVector K n) (k : UserType K) : ℝ :=
  rawTypeUtilityVector T x k / bestItemUtility T k

/-- Minimum type fairness evaluated on the reduced simplex-vector presentation. -/
noncomputable def typeFairnessVector {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (x : TypePolicySimplexVector K n) : ℝ :=
  AppliedModelingLib.finiteMin (normalizedTypeUtilityVector T x)

theorem rawTypeUtility_typePolicyOfSimplexVector_eq {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (x : TypePolicySimplexVector K n) (k : UserType K) :
    rawTypeUtility T (typePolicyOfSimplexVector x) k =
      rawTypeUtilityVector T x k := by
  unfold rawTypeUtility rawTypeUtilityVector AppliedModelingLib.Policy.agentScore
    AppliedModelingLib.pmfExp
  simp [mul_comm]

theorem normalizedTypeUtility_typePolicyOfSimplexVector_eq {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (x : TypePolicySimplexVector K n) (k : UserType K) :
    normalizedTypeUtility T (typePolicyOfSimplexVector x) k =
      normalizedTypeUtilityVector T x k := by
  unfold normalizedTypeUtility normalizedTypeUtilityVector
  rw [rawTypeUtility_typePolicyOfSimplexVector_eq]

theorem typeFairness_typePolicyOfSimplexVector_eq {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (x : TypePolicySimplexVector K n) :
    typeFairness T (typePolicyOfSimplexVector x) =
      typeFairnessVector T x := by
  unfold typeFairness typeFairnessVector
  apply congrArg
  funext k
  exact normalizedTypeUtility_typePolicyOfSimplexVector_eq T x k

theorem rawTypeUtilityVector_simplexVectorOfTypePolicy_eq {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n)
    (ρ : TypePolicy K n) (k : UserType K) :
    rawTypeUtilityVector T (simplexVectorOfTypePolicy ρ) k =
      rawTypeUtility T ρ k := by
  unfold rawTypeUtilityVector rawTypeUtility simplexVectorOfTypePolicy
    AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp
  change (∑ x : Item n, ((ρ k) x).toReal * T.utility k x) =
    ∑ x : Item n, ((ρ k) x).toReal * T.utility k x
  rfl

theorem normalizedTypeUtilityVector_simplexVectorOfTypePolicy_eq
    {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (ρ : TypePolicy K n) (k : UserType K) :
    normalizedTypeUtilityVector T (simplexVectorOfTypePolicy ρ) k =
      normalizedTypeUtility T ρ k := by
  unfold normalizedTypeUtilityVector normalizedTypeUtility
  rw [rawTypeUtilityVector_simplexVectorOfTypePolicy_eq]

theorem typeFairnessVector_simplexVectorOfTypePolicy_eq
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n) :
    typeFairnessVector T (simplexVectorOfTypePolicy ρ) =
      typeFairness T ρ := by
  unfold typeFairnessVector typeFairness
  apply congrArg
  funext k
  exact normalizedTypeUtilityVector_simplexVectorOfTypePolicy_eq T ρ k

theorem rawTypeUtilityVector_continuous {K n : ℕ}
    (T : TypeWeightedRecommendationModel K n) (k : UserType K) :
    Continuous (fun x : TypePolicySimplexVector K n =>
      rawTypeUtilityVector T x k) := by
  unfold rawTypeUtilityVector
  apply continuous_finset_sum
  intro j _hj
  have hrow : Continuous (fun x : TypePolicySimplexVector K n => x k) :=
    continuous_apply k
  have hcoord : Continuous (fun x : TypePolicySimplexVector K n =>
      ((x k : stdSimplex ℝ (Item n)) : Item n → ℝ) j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp hrow)
  exact hcoord.mul continuous_const

theorem normalizedTypeUtilityVector_continuous {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (k : UserType K) :
    Continuous (fun x : TypePolicySimplexVector K n =>
      normalizedTypeUtilityVector T x k) := by
  unfold normalizedTypeUtilityVector
  exact (rawTypeUtilityVector_continuous T k).div_const _

theorem typeFairnessVector_continuous {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) :
    Continuous (fun x : TypePolicySimplexVector K n =>
      typeFairnessVector T x) := by
  have hcont : ∀ k : UserType K,
      Continuous (fun x : TypePolicySimplexVector K n =>
        normalizedTypeUtilityVector T x k) :=
    fun k => normalizedTypeUtilityVector_continuous T k
  unfold typeFairnessVector AppliedModelingLib.finiteMin
  fun_prop

/-- Positive reduced item fairness implies every item is used by some type. -/
theorem item_coverage_of_itemFairness_pos {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hpos : 0 < itemFairness T ρ) :
    ∀ j : Item n, ∃ k : UserType K, ρ k j ≠ 0 := by
  classical
  intro j
  by_contra hnone
  have hall_zero : ∀ k : UserType K, ρ k j = 0 := by
    intro k
    exact Classical.byContradiction (by
      intro hk
      exact hnone ⟨k, hk⟩)
  have hraw_zero : rawItemUtility T ρ j = 0 := by
    unfold rawItemUtility
    simp [hall_zero]
  have hnorm_zero : normalizedItemUtility T ρ j = 0 := by
    unfold normalizedItemUtility
    rw [hraw_zero]
    by_cases hden : itemNormalizer T j = 0
    · simp [hden]
    · simp [hden]
  have hle := AppliedModelingLib.finiteMin_le (normalizedItemUtility T ρ) j
  have hnorm_pos : 0 < normalizedItemUtility T ρ j := lt_of_lt_of_le hpos hle
  rw [hnorm_zero] at hnorm_pos
  exact (lt_irrefl (0 : ℝ)) hnorm_pos

/-- Nonnegative weights/utilities make every reduced raw item utility nonnegative. -/
theorem rawItemUtility_nonneg_of_nonnegative
    {K n : ℕ} (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities)
    (ρ : TypePolicy K n) (j : Item n) :
    0 ≤ rawItemUtility T ρ j := by
  unfold rawItemUtility
  exact Finset.sum_nonneg (by
    intro k _hk
    exact mul_nonneg (mul_nonneg (hWeight k) (hUtil k j))
      ENNReal.toReal_nonneg)

/-- Nonnegative weights/utilities make every reduced item normalizer nonnegative. -/
theorem itemNormalizer_nonneg_of_nonnegative
    {K n : ℕ} (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities)
    (j : Item n) :
    0 ≤ itemNormalizer T j := by
  unfold itemNormalizer
  exact Finset.sum_nonneg (by
    intro k _hk
    exact mul_nonneg (hWeight k) (hUtil k j))

/-- Nonnegative weights/utilities make reduced normalized item utility nonnegative. -/
theorem normalizedItemUtility_nonneg_of_nonnegative
    {K n : ℕ} (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities)
    (ρ : TypePolicy K n) (j : Item n) :
    0 ≤ normalizedItemUtility T ρ j := by
  unfold normalizedItemUtility
  by_cases hden : itemNormalizer T j = 0
  · simp [hden]
  · simpa [hden] using div_nonneg
      (rawItemUtility_nonneg_of_nonnegative T hWeight hUtil ρ j)
      (itemNormalizer_nonneg_of_nonnegative T hWeight hUtil j)

/-- Nonnegative weights/utilities make raw item utility at most its normalizer. -/
theorem rawItemUtility_le_itemNormalizer_of_nonnegative
    {K n : ℕ} (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities)
    (ρ : TypePolicy K n) (j : Item n) :
    rawItemUtility T ρ j ≤ itemNormalizer T j := by
  unfold rawItemUtility itemNormalizer
  exact Finset.sum_le_sum (by
    intro k _hk
    have hcoeff : 0 ≤ T.weight k * T.utility k j :=
      mul_nonneg (hWeight k) (hUtil k j)
    have hprob : ((ρ k) j).toReal ≤ 1 :=
      AppliedModelingLib.pmf_apply_toReal_le_one (ρ k) j
    calc
      T.weight k * T.utility k j * ((ρ k) j).toReal
          ≤ (T.weight k * T.utility k j) * 1 := by
            exact mul_le_mul_of_nonneg_left hprob hcoeff
      _ = T.weight k * T.utility k j := by ring)

/-- Nonnegative weights/utilities make reduced normalized item utility at most one. -/
theorem normalizedItemUtility_le_one_of_nonnegative
    {K n : ℕ} (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities)
    (ρ : TypePolicy K n) (j : Item n) :
    normalizedItemUtility T ρ j ≤ 1 := by
  unfold normalizedItemUtility
  by_cases hden : itemNormalizer T j = 0
  · simp [hden]
  · have hden_nonneg := itemNormalizer_nonneg_of_nonnegative T hWeight hUtil j
    have hden_pos : 0 < itemNormalizer T j := lt_of_le_of_ne hden_nonneg (Ne.symm hden)
    have hraw_le := rawItemUtility_le_itemNormalizer_of_nonnegative T hWeight hUtil ρ j
    simp [hden]
    rw [div_le_iff₀ hden_pos]
    simpa using hraw_le

/-- Nonnegative weights/utilities make reduced minimum item fairness nonnegative. -/
theorem itemFairness_nonneg_of_nonnegative {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities)
    (ρ : TypePolicy K n) :
    0 ≤ itemFairness T ρ := by
  exact AppliedModelingLib.finiteMin_nonneg (normalizedItemUtility T ρ)
    (normalizedItemUtility_nonneg_of_nonnegative T hWeight hUtil ρ)

/-- Strictly positive weights and utilities make each item normalizer positive. -/
theorem itemNormalizer_pos_of_positive
    {K n : ℕ} [NeZero K] (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (j : Item n) :
    0 < itemNormalizer T j := by
  unfold itemNormalizer
  exact Finset.sum_pos (by
    intro k _hk
    exact mul_pos (hWeight k) (hUtil k j)) Finset.univ_nonempty

/-- Equality feasibility in a concrete reduced-LP active basis makes every
normalized item utility equal to the LP objective. -/
theorem normalizedItemUtility_eq_ell_of_equalityLPBasicFeasible
    {K n : ℕ} [NeZero K]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (ρ : TypePolicy K n) (ell : ℝ)
    (hbfs : T.IsEqualityLPBasicFeasible ρ ell) :
    ∀ j : Item n, normalizedItemUtility T ρ j = ell := by
  rcases hbfs with ⟨hbfs⟩
  intro j
  have heq := hbfs.equality_feasible j
  rw [equalityLPItemNormal_dot_candidate_eq T ρ ell j
    (itemNormalizer_pos_of_positive T hWeight hUtil j).ne'] at heq
  exact sub_eq_zero.mp heq

/-- A concrete reduced equality-LP BFS has item-fairness value exactly equal
to its objective coordinate. -/
theorem itemFairness_eq_ell_of_equalityLPBasicFeasible
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (ρ : TypePolicy K n) (ell : ℝ)
    (hbfs : T.IsEqualityLPBasicFeasible ρ ell) :
    itemFairness T ρ = ell := by
  unfold itemFairness
  exact AppliedModelingLib.finiteMin_eq_of_forall
    (normalizedItemUtility T ρ) ell
    (normalizedItemUtility_eq_ell_of_equalityLPBasicFeasible
      T hWeight hUtil ρ ell hbfs)

/-- Under the uniform type policy, strictly positive data gives every item positive raw utility. -/
theorem rawItemUtility_uniform_pos_of_positive
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (j : Item n) :
    0 < rawItemUtility T (uniformTypePolicy (K := K) (n := n)) j := by
  unfold rawItemUtility
  exact Finset.sum_pos (by
    intro k _hk
    exact mul_pos (mul_pos (hWeight k) (hUtil k j))
      (uniformTypePolicy_apply_toReal_pos (K := K) (n := n) k j))
    Finset.univ_nonempty

/-- The uniform type policy has strictly positive normalized item utility. -/
theorem normalizedItemUtility_uniform_pos_of_positive
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (j : Item n) :
    0 < normalizedItemUtility T (uniformTypePolicy (K := K) (n := n)) j := by
  unfold normalizedItemUtility
  have hden_pos := itemNormalizer_pos_of_positive T hWeight hUtil j
  have hraw_pos := rawItemUtility_uniform_pos_of_positive T hWeight hUtil j
  simp [hden_pos.ne.symm, div_pos hraw_pos hden_pos]

/-- The uniform type policy witnesses positive item fairness under strictly positive data. -/
theorem itemFairness_uniform_pos_of_positive
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities) :
    0 < itemFairness T (uniformTypePolicy (K := K) (n := n)) := by
  exact AppliedModelingLib.finiteMin_pos (normalizedItemUtility T
    (uniformTypePolicy (K := K) (n := n)))
    (normalizedItemUtility_uniform_pos_of_positive T hWeight hUtil)

/-- Attainable reduced-problem item fairness levels. -/
def attainableItemFairnessSet {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) : Set ℝ :=
  {r | ∃ ρ : TypePolicy K n, r = itemFairness T ρ}

/-- The reduced analogue of `I^*_min`. -/
noncomputable def optimalItemFairness {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) : ℝ :=
  sSup (attainableItemFairnessSet T)

/-- Nonnegative weights/utilities bound every attainable item-fairness value above by one. -/
theorem attainableItemFairnessSet_bddAbove_of_nonnegative {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities) :
    BddAbove (attainableItemFairnessSet T) := by
  refine ⟨1, ?_⟩
  intro r hr
  obtain ⟨ρ, hr⟩ := hr
  rw [hr]
  let j0 : Item n := Classical.choice inferInstance
  exact (AppliedModelingLib.finiteMin_le (normalizedItemUtility T ρ) j0).trans
    (normalizedItemUtility_le_one_of_nonnegative T hWeight hUtil ρ j0)

/-- Compactness of the reduced finite policy simplex gives an item-fairness maximizer. -/
theorem optimalItemFairness_attained_of_nonnegative
    {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities) :
    ∃ ρ : TypePolicy K n, itemFairness T ρ = optimalItemFairness T := by
  classical
  let X := TypePolicySimplexVector K n
  have hcompact : IsCompact (Set.univ : Set X) := isCompact_univ
  have hnonempty : (Set.univ : Set X).Nonempty := Set.univ_nonempty
  have hcont : ContinuousOn (fun x : X => itemFairnessVector T x) Set.univ :=
    (itemFairnessVector_continuous T).continuousOn
  rcases hcompact.exists_isMaxOn hnonempty hcont with
    ⟨xopt, _hxmem, hxmax⟩
  let ρopt : TypePolicy K n := typePolicyOfSimplexVector xopt
  refine ⟨ρopt, ?_⟩
  have hρopt_eq :
      itemFairness T ρopt = itemFairnessVector T xopt := by
    dsimp [ρopt]
    exact itemFairness_typePolicyOfSimplexVector_eq T xopt
  have hset_nonempty : (attainableItemFairnessSet T).Nonempty := by
    exact ⟨itemFairness T ρopt, ⟨ρopt, rfl⟩⟩
  have hopt_le : optimalItemFairness T ≤ itemFairness T ρopt := by
    unfold optimalItemFairness
    refine csSup_le hset_nonempty ?_
    intro r hr
    obtain ⟨ρ, rfl⟩ := hr
    have hxle :
        itemFairnessVector T (simplexVectorOfTypePolicy ρ) ≤
          itemFairnessVector T xopt :=
      (isMaxOn_iff.mp hxmax) (simplexVectorOfTypePolicy ρ) (Set.mem_univ _)
    rw [itemFairnessVector_simplexVectorOfTypePolicy_eq] at hxle
    rw [← hρopt_eq] at hxle
    exact hxle
  have hle_opt : itemFairness T ρopt ≤ optimalItemFairness T := by
    exact le_csSup
      (attainableItemFairnessSet_bddAbove_of_nonnegative T hWeight hUtil)
      ⟨ρopt, rfl⟩
  exact le_antisymm hle_opt hopt_le

/--
Strictly positive weights and utilities make the reduced optimal item-fairness
value positive. This formalizes the paper's `IF* > 0` lemma for the reduced
type-level problem.
-/
theorem optimalItemFairness_pos_of_positive
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities) :
    0 < optimalItemFairness T := by
  have hWeight_nonneg := nonnegativeWeights_of_positiveWeights T hWeight
  have hUtil_nonneg := nonnegativeUtilities_of_positiveUtilities T hUtil
  have hbdd := attainableItemFairnessSet_bddAbove_of_nonnegative
    T hWeight_nonneg hUtil_nonneg
  have hmem :
      itemFairness T (uniformTypePolicy (K := K) (n := n)) ∈
        attainableItemFairnessSet T := by
    exact ⟨uniformTypePolicy (K := K) (n := n), rfl⟩
  exact lt_of_lt_of_le
    (itemFairness_uniform_pos_of_positive T hWeight hUtil)
    (le_csSup hbdd hmem)

/-- Feasibility for the reduced problem at fairness level `γ`. -/
def feasibleAtLevel {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (γ : ℝ) (ρ : TypePolicy K n) : Prop :=
  γ * optimalItemFairness T ≤ itemFairness T ρ

/-- Attainable reduced-problem type-fairness levels at item-fairness level `γ`. -/
def attainableTypeFairnessAtLevel {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (γ : ℝ) : Set ℝ :=
  {r | ∃ ρ : TypePolicy K n, feasibleAtLevel T γ ρ ∧ r = typeFairness T ρ}

/-- Row positivity makes the type-normalization denominator strictly positive. -/
theorem bestItemUtility_pos_of_rowHasPositiveItem {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (hRow : T.RowHasPositiveItem)
    (k : UserType K) :
    0 < bestItemUtility T k := by
  obtain ⟨j, hj⟩ := hRow k
  exact lt_of_lt_of_le hj (AppliedModelingLib.le_finiteMax (T.utility k) j)

/-- A type's raw expected utility is at most that type's best item utility. -/
theorem rawTypeUtility_le_bestItemUtility {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (k : UserType K) :
    rawTypeUtility T ρ k ≤ bestItemUtility T k := by
  unfold rawTypeUtility bestItemUtility AppliedModelingLib.Policy.agentScore
  exact AppliedModelingLib.pmfExp_le_of_forall_le (ρ k) (T.utility k)
    (AppliedModelingLib.finiteMax (T.utility k))
    (fun j => AppliedModelingLib.le_finiteMax (T.utility k) j)

/-- Positive row normalizers make every normalized type utility at most one. -/
theorem normalizedTypeUtility_le_one_of_rowHasPositiveItem
    {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (hRow : T.RowHasPositiveItem)
    (ρ : TypePolicy K n) (k : UserType K) :
    normalizedTypeUtility T ρ k ≤ 1 := by
  have hraw := rawTypeUtility_le_bestItemUtility T ρ k
  have hbest_pos := bestItemUtility_pos_of_rowHasPositiveItem T hRow k
  unfold normalizedTypeUtility
  rw [div_le_iff₀ hbest_pos]
  simpa using hraw

/-- Minimum type fairness is bounded above by one. -/
theorem typeFairness_le_one_of_rowHasPositiveItem
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (hRow : T.RowHasPositiveItem)
    (ρ : TypePolicy K n) :
    typeFairness T ρ ≤ 1 := by
  classical
  let k0 : UserType K := Classical.choice inferInstance
  exact (AppliedModelingLib.finiteMin_le (normalizedTypeUtility T ρ) k0).trans
    (normalizedTypeUtility_le_one_of_rowHasPositiveItem T hRow ρ k0)

/-- Feasible type-fairness values are bounded above by one under positive row normalizers. -/
theorem attainableTypeFairnessAtLevel_bddAbove_of_rowHasPositiveItem
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (hRow : T.RowHasPositiveItem)
    (γ : ℝ) :
    BddAbove (attainableTypeFairnessAtLevel T γ) := by
  refine ⟨1, ?_⟩
  intro r hr
  obtain ⟨ρ, _hfeas, hr⟩ := hr
  rw [hr]
  exact typeFairness_le_one_of_rowHasPositiveItem T hRow ρ

/-- A canonical reduced policy used only to witness nonempty finite feasible sets. -/
noncomputable def defaultTypePolicy {K n : ℕ} [NeZero n] : TypePolicy K n :=
  AppliedModelingLib.Policy.pure
    (fun _ : UserType K => Classical.choice (inferInstance : Nonempty (Item n)))

/-- The deterministic reduced policy that recommends each type a row-maximizing item. -/
noncomputable def bestItemTypePolicy {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) : TypePolicy K n :=
  AppliedModelingLib.Policy.pure
    (fun k : UserType K =>
      Classical.choose (AppliedModelingLib.exists_finiteMax_eq (T.utility k)))

theorem bestItemTypePolicy_utility_eq_bestItemUtility
    {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (k : UserType K) :
    T.utility k
        (Classical.choose (AppliedModelingLib.exists_finiteMax_eq (T.utility k))) =
      bestItemUtility T k := by
  exact (Classical.choose_spec
    (AppliedModelingLib.exists_finiteMax_eq (T.utility k))).symm

theorem rawTypeUtility_bestItemTypePolicy_eq_bestItemUtility
    {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (k : UserType K) :
    rawTypeUtility T (bestItemTypePolicy T) k = bestItemUtility T k := by
  unfold rawTypeUtility bestItemTypePolicy
  rw [AppliedModelingLib.Policy.agentScore_pure]
  exact bestItemTypePolicy_utility_eq_bestItemUtility T k

theorem rawTypeUtility_pure
    {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (choose : UserType K → Item n)
    (k : UserType K) :
    rawTypeUtility T (AppliedModelingLib.Policy.pure choose) k =
      T.utility k (choose k) := by
  unfold rawTypeUtility
  rw [AppliedModelingLib.Policy.agentScore_pure]

theorem normalizedTypeUtility_bestItemTypePolicy_eq_one
    {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (hRow : T.RowHasPositiveItem)
    (k : UserType K) :
    normalizedTypeUtility T (bestItemTypePolicy T) k = 1 := by
  unfold normalizedTypeUtility
  rw [rawTypeUtility_bestItemTypePolicy_eq_bestItemUtility]
  exact div_self (ne_of_gt (bestItemUtility_pos_of_rowHasPositiveItem T hRow k))

theorem typeFairness_bestItemTypePolicy_eq_one
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (hRow : T.RowHasPositiveItem) :
    typeFairness T (bestItemTypePolicy T) = 1 := by
  unfold typeFairness
  exact AppliedModelingLib.finiteMin_eq_of_forall
    (normalizedTypeUtility T (bestItemTypePolicy T)) 1
    (normalizedTypeUtility_bestItemTypePolicy_eq_one T hRow)

/--
At baseline `γ = 0`, every reduced policy is feasible under nonnegative
weights and utilities.
-/
theorem feasibleAtLevel_zero_of_nonnegative
    {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities)
    (ρ : TypePolicy K n) :
    feasibleAtLevel T 0 ρ := by
  unfold feasibleAtLevel
  simpa using itemFairness_nonneg_of_nonnegative T hWeight hUtil ρ

/-- The baseline reduced feasible value set is nonempty under nonnegativity. -/
theorem attainableTypeFairnessAtLevel_zero_nonempty_of_nonnegative
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities) :
    (attainableTypeFairnessAtLevel T 0).Nonempty := by
  refine ⟨typeFairness T (defaultTypePolicy (K := K) (n := n)), ?_⟩
  exact ⟨defaultTypePolicy (K := K) (n := n),
    feasibleAtLevel_zero_of_nonnegative T hWeight hUtil _, rfl⟩

/--
For any strict fraction `γ < 1`, strictly positive reduced data makes the
`γ`-constrained feasible-value set nonempty. This avoids an attainment theorem
for the item-fairness optimum away from the maximal boundary `γ = 1`.
-/
theorem attainableTypeFairnessAtLevel_nonempty_of_gamma_lt_one
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    {γ : ℝ} (hγ : γ < 1) :
    (attainableTypeFairnessAtLevel T γ).Nonempty := by
  have hopt_pos := optimalItemFairness_pos_of_positive T hWeight hUtil
  have hlt :
      γ * optimalItemFairness T < optimalItemFairness T := by
    simpa using (mul_lt_mul_of_pos_right hγ hopt_pos)
  have hitem_nonempty : (attainableItemFairnessSet T).Nonempty := by
    exact ⟨itemFairness T (uniformTypePolicy (K := K) (n := n)),
      ⟨uniformTypePolicy (K := K) (n := n), rfl⟩⟩
  obtain ⟨r, hrmem, hrgt⟩ :=
    exists_lt_of_lt_csSup hitem_nonempty hlt
  obtain ⟨ρ, hr⟩ := hrmem
  refine ⟨typeFairness T ρ, ?_⟩
  refine ⟨ρ, ?_, rfl⟩
  unfold feasibleAtLevel
  rw [← hr]
  exact le_of_lt hrgt

/--
At the maximal reduced boundary `γ = 1`, compactness supplies a type policy
attaining the reduced item-fairness optimum.
-/
theorem attainableTypeFairnessAtLevel_one_nonempty_of_nonnegative
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities) :
    (attainableTypeFairnessAtLevel T 1).Nonempty := by
  obtain ⟨ρ, hρ⟩ :=
    optimalItemFairness_attained_of_nonnegative T hWeight hUtil
  refine ⟨typeFairness T ρ, ?_⟩
  refine ⟨ρ, ?_, rfl⟩
  unfold feasibleAtLevel
  rw [one_mul, hρ]

/-- The reduced analogue of `U^*_min(γ, w)`. -/
noncomputable def optimalTypeFairnessAtLevel {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (γ : ℝ) : ℝ :=
  sSup (attainableTypeFairnessAtLevel T γ)

/--
The reduced unconstrained user-fairness optimum is `1`, matching the original
model baseline after type aggregation.
-/
theorem optimalTypeFairnessAtLevel_zero_eq_one
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities)
    (hRow : T.RowHasPositiveItem) :
    optimalTypeFairnessAtLevel T 0 = 1 := by
  have hset_nonempty :
      (attainableTypeFairnessAtLevel T 0).Nonempty :=
    attainableTypeFairnessAtLevel_zero_nonempty_of_nonnegative T hWeight hUtil
  have hbdd :
      BddAbove (attainableTypeFairnessAtLevel T 0) :=
    attainableTypeFairnessAtLevel_bddAbove_of_rowHasPositiveItem T hRow 0
  have hbest_mem :
      typeFairness T (bestItemTypePolicy T) ∈
        attainableTypeFairnessAtLevel T 0 := by
    exact ⟨bestItemTypePolicy T,
      feasibleAtLevel_zero_of_nonnegative T hWeight hUtil _, rfl⟩
  apply le_antisymm
  · unfold optimalTypeFairnessAtLevel
    refine csSup_le hset_nonempty ?_
    intro r hr
    obtain ⟨ρ, _hfeas, hr⟩ := hr
    rw [hr]
    exact typeFairness_le_one_of_rowHasPositiveItem T hRow ρ
  · rw [← typeFairness_bestItemTypePolicy_eq_one T hRow]
    unfold optimalTypeFairnessAtLevel
    exact le_csSup hbdd hbest_mem

/-- A type-level policy solves the reduced problem at item-fairness level `γ`. -/
def IsOptimalAtLevel {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (γ : ℝ) (ρ : TypePolicy K n) : Prop :=
  feasibleAtLevel T γ ρ ∧ typeFairness T ρ = optimalTypeFairnessAtLevel T γ

/-- The reduced vector-domain feasible set for the `γ`-constrained problem. -/
def feasibleTypeSimplexVectorAtLevel {K n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (γ : ℝ) :
    Set (TypePolicySimplexVector K n) :=
  {x | γ * optimalItemFairness T ≤ itemFairnessVector T x}

/--
Whenever the reduced `γ`-constrained feasible-value set is nonempty, compactness
of the finite type-policy simplex gives an actual type policy attaining
`U^*_{\min}(γ)`.
-/
theorem exists_isOptimalAtLevel_of_attainableTypeFairnessAtLevel_nonempty
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (γ : ℝ)
    (hFeasNonempty : (attainableTypeFairnessAtLevel T γ).Nonempty) :
    ∃ ρ : TypePolicy K n, IsOptimalAtLevel T γ ρ := by
  classical
  let S : Set (TypePolicySimplexVector K n) :=
    feasibleTypeSimplexVectorAtLevel T γ
  have hS_closed : IsClosed S := by
    dsimp [S, feasibleTypeSimplexVectorAtLevel]
    exact isClosed_le continuous_const (itemFairnessVector_continuous T)
  have hS_compact : IsCompact S :=
    isCompact_univ.of_isClosed_subset hS_closed (Set.subset_univ _)
  have hS_nonempty : S.Nonempty := by
    obtain ⟨_r, ρ, hfeas, _hr⟩ := hFeasNonempty
    refine ⟨simplexVectorOfTypePolicy ρ, ?_⟩
    dsimp [S, feasibleTypeSimplexVectorAtLevel]
    rw [itemFairnessVector_simplexVectorOfTypePolicy_eq]
    exact hfeas
  rcases hS_compact.exists_isMaxOn hS_nonempty
      ((typeFairnessVector_continuous T).continuousOn) with
    ⟨xopt, hxoptS, hxmax⟩
  let ρopt : TypePolicy K n := typePolicyOfSimplexVector xopt
  have hρopt_item :
      itemFairness T ρopt = itemFairnessVector T xopt := by
    dsimp [ρopt]
    exact itemFairness_typePolicyOfSimplexVector_eq T xopt
  have hρopt_type :
      typeFairness T ρopt = typeFairnessVector T xopt := by
    dsimp [ρopt]
    exact typeFairness_typePolicyOfSimplexVector_eq T xopt
  have hρopt_feas : feasibleAtLevel T γ ρopt := by
    unfold feasibleAtLevel
    dsimp [S, feasibleTypeSimplexVectorAtLevel] at hxoptS
    rw [hρopt_item]
    exact hxoptS
  have hρopt_mem :
      typeFairness T ρopt ∈ attainableTypeFairnessAtLevel T γ := by
    exact ⟨ρopt, hρopt_feas, rfl⟩
  have hupper :
      ∀ r ∈ attainableTypeFairnessAtLevel T γ,
        r ≤ typeFairness T ρopt := by
    intro r hr
    obtain ⟨ρ, hfeas, hr⟩ := hr
    have hxρS : simplexVectorOfTypePolicy ρ ∈ S := by
      dsimp [S, feasibleTypeSimplexVectorAtLevel]
      rw [itemFairnessVector_simplexVectorOfTypePolicy_eq]
      exact hfeas
    have hxle :
        typeFairnessVector T (simplexVectorOfTypePolicy ρ) ≤
          typeFairnessVector T xopt :=
      (isMaxOn_iff.mp hxmax) (simplexVectorOfTypePolicy ρ) hxρS
    rw [typeFairnessVector_simplexVectorOfTypePolicy_eq] at hxle
    rw [← hρopt_type] at hxle
    rw [hr]
    exact hxle
  have hbdd : BddAbove (attainableTypeFairnessAtLevel T γ) :=
    ⟨typeFairness T ρopt, hupper⟩
  have hopt_le :
      optimalTypeFairnessAtLevel T γ ≤ typeFairness T ρopt := by
    unfold optimalTypeFairnessAtLevel
    exact csSup_le hFeasNonempty hupper
  have hle_opt :
      typeFairness T ρopt ≤ optimalTypeFairnessAtLevel T γ := by
    unfold optimalTypeFairnessAtLevel
    exact le_csSup hbdd hρopt_mem
  exact ⟨ρopt, hρopt_feas, le_antisymm hle_opt hopt_le⟩

/-- The maximal-boundary reduced type-fairness problem has an optimal policy. -/
theorem exists_isOptimalAtLevel_one_of_nonnegative
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.NonnegativeWeights) (hUtil : T.NonnegativeUtilities) :
    ∃ ρ : TypePolicy K n, IsOptimalAtLevel T 1 ρ :=
  exists_isOptimalAtLevel_of_attainableTypeFairnessAtLevel_nonempty
    T 1
    (attainableTypeFairnessAtLevel_one_nonempty_of_nonnegative
      T hWeight hUtil)

/--
An optimal reduced policy upper-bounds the type fairness of every feasible
policy at the same item-fairness level.
-/
theorem typeFairness_le_of_isOptimalAtLevel
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (hRow : T.RowHasPositiveItem)
    {γ : ℝ} {ρ ρ' : TypePolicy K n}
    (hopt : IsOptimalAtLevel T γ ρ)
    (hfeas' : feasibleAtLevel T γ ρ') :
    typeFairness T ρ' ≤ typeFairness T ρ := by
  have hbdd :
      BddAbove (attainableTypeFairnessAtLevel T γ) :=
    attainableTypeFairnessAtLevel_bddAbove_of_rowHasPositiveItem T hRow γ
  have hmem :
      typeFairness T ρ' ∈ attainableTypeFairnessAtLevel T γ :=
    ⟨ρ', hfeas', rfl⟩
  rw [hopt.2]
  exact le_csSup hbdd hmem

end TypeWeightedRecommendationModel

/--
A witness connecting the original user-level model with a chosen type-level reduction.
The equality clauses are intentionally exact, so Codex can later prove preservation of
utilities, fairness functionals, and feasible regions by rewriting.
-/
structure ReductionWitness (m n K : ℕ) where
  data : RecommendationModel.SymmetricData m n K
  reduced : TypeWeightedRecommendationModel K n
  utility_agrees : ∀ u j,
    data.model.utility u j = reduced.utility (data.types.toType u) j
  weight_eq_typeWeight : ∀ k,
    reduced.weight k = RecommendationModel.UserTypeAssignment.typeWeight data.types k

/-- The canonical type-level reduction constructed from the source symmetric
data, with type weights equal to population shares rather than raw counts. -/
noncomputable def RecommendationModel.SymmetricData.canonicalReduction
    {m n K : ℕ}
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types) :
    ReductionWitness m n K where
  data := S
  reduced := {
    utility := fun k j => S.model.utility (reps.repr k) j
    weight := UserTypeAssignment.typeWeight S.types
  }
  utility_agrees := by
    intro u j
    have hrow :
        S.model.utility u =
          S.model.utility (reps.repr (S.types.toType u)) :=
      S.agreeWithinTypes u (reps.repr (S.types.toType u))
        (reps.repr_spec (S.types.toType u)).symm
    exact congrFun hrow j
  weight_eq_typeWeight := by
    intro k
    rfl

/--
Construct the canonical reduction from the source-level condition that every
declared user type is represented by at least one user. Representatives are
chosen internally and are not an additional paper-facing certificate.
-/
noncomputable def RecommendationModel.SymmetricData.canonicalReductionOfSurjective
    {m n K : ℕ}
    (S : RecommendationModel.SymmetricData m n K)
    (hTypes : Function.Surjective S.types.toType) :
    ReductionWitness m n K :=
  S.canonicalReduction
    (AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypes)

namespace ReductionWitness

/-- Lift a reduced-policy candidate back to a user-level policy. -/
def liftedPolicy {m n K : ℕ}
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) : Policy m n :=
  UserTypeAssignment.liftTypePolicy R.data.types ρ

@[simp] theorem liftedPolicy_apply {m n K : ℕ}
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) (u : User m) :
    liftedPolicy R ρ u = ρ (R.data.types.toType u) := rfl

/-- Every lifted reduced-policy candidate is type-symmetric on users. -/
theorem liftedPolicy_isTypeSymmetric {m n K : ℕ}
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) :
    UserTypeAssignment.IsTypeSymmetric R.data.types (liftedPolicy R ρ) :=
  UserTypeAssignment.liftTypePolicy_isTypeSymmetric _ _



/--
If each user type has a chosen representative, then every type-symmetric user-level
policy comes from a genuine reduced type-level policy.
-/
theorem exists_typePolicy_of_isTypeSymmetric {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ) :
    ∃ ρK : TypePolicy K n, liftedPolicy R ρK = ρ := by
  simpa [liftedPolicy] using
    (UserTypeAssignment.isTypeSymmetric_iff_exists_liftTypePolicy R.data.types reps ρ).mp hρ

end ReductionWitness

/--
A clean target proposition for Proposition 1: every symmetric optimal user-level policy
should come from a type-level policy in the reduced problem.
-/
def LPReductionTarget {m n K : ℕ} [NeZero m] [NeZero n]
    (R : ReductionWitness m n K) (γ : ℝ) : Prop :=
  ∀ ρ,
    ρ ∈ RecommendationModel.symmetricOptimalPolicies R.data γ →
      ∃ ρK : TypePolicy K n, ReductionWitness.liftedPolicy R ρK = ρ

/--
A clean target proposition for Proposition 2: optimal reduced policies have sparse
support in the precise sense already encoded in `TypePolicy.SparseShape`.
-/
def ReducedSparseOptimalityTarget {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (γ : ℝ) : Prop :=
  ∀ ρ : TypePolicy K n,
    TypeWeightedRecommendationModel.IsOptimalAtLevel T γ ρ → TypePolicy.SparseShape ρ

/--
With chosen representatives for user types, the abstract LP-reduction target follows
immediately from the classwise lifting theorem.
-/
theorem lpReductionTarget_of_representatives {m n K : ℕ} [NeZero m] [NeZero n]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) :
    LPReductionTarget R γ := by
  intro ρ hρ
  exact ReductionWitness.exists_typePolicy_of_isTypeSymmetric R reps hρ.1

end GCG24UserItemFairness
