import GCG24UserItemFairness.LPReduction

open scoped BigOperators
open AppliedModelingLib

namespace GCG24UserItemFairness

namespace RecommendationModel.SymmetricData

/-- Under a type-symmetric policy, same-type users have the same raw utility. -/
theorem rawUserUtility_eq_of_sameType {m n K : ℕ}
    (S : RecommendationModel.SymmetricData m n K)
    {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric S.types ρ)
    {u u' : User m} (hType : S.types.toType u = S.types.toType u') :
    RecommendationModel.rawUserUtility S.model ρ u =
      RecommendationModel.rawUserUtility S.model ρ u' := by
  unfold RecommendationModel.rawUserUtility AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp
  refine Finset.sum_congr rfl ?_
  intro j _
  have hrow : S.model.utility u j = S.model.utility u' j := by
    exact congrFun (S.agreeWithinTypes u u' hType) j
  have hpol : ρ u = ρ u' := hρ u u' hType
  rw [hrow, hpol]

/-- Same-type users have the same best-item normalizer. -/
theorem bestItemUtility_eq_of_sameType {m n K : ℕ} [NeZero n]
    (S : RecommendationModel.SymmetricData m n K)
    {u u' : User m} (hType : S.types.toType u = S.types.toType u') :
    RecommendationModel.bestItemUtility S.model u =
      RecommendationModel.bestItemUtility S.model u' := by
  have hrow : S.model.utility u = S.model.utility u' := S.agreeWithinTypes u u' hType
  unfold RecommendationModel.bestItemUtility
  rw [hrow]

/-- Under a type-symmetric policy, same-type users have the same normalized utility. -/
theorem normalizedUserUtility_eq_of_sameType {m n K : ℕ} [NeZero n]
    (S : RecommendationModel.SymmetricData m n K)
    {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric S.types ρ)
    {u u' : User m} (hType : S.types.toType u = S.types.toType u') :
    RecommendationModel.normalizedUserUtility S.model ρ u =
      RecommendationModel.normalizedUserUtility S.model ρ u' := by
  unfold RecommendationModel.normalizedUserUtility
  rw [rawUserUtility_eq_of_sameType (S := S) (ρ := ρ) hρ hType]
  rw [bestItemUtility_eq_of_sameType (S := S) hType]

end RecommendationModel.SymmetricData

namespace ReductionWitness

/-- Row positivity in the original symmetric model transfers to the reduced model. -/
theorem reduced_rowHasPositiveItem_of_rowHasPositiveItem
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem) :
    R.reduced.RowHasPositiveItem := by
  intro k
  obtain ⟨j, hj⟩ := hRow (reps.repr k)
  refine ⟨j, ?_⟩
  rw [R.utility_agrees (reps.repr k) j] at hj
  simpa [reps.repr_spec k] using hj

/-- Type weights in the reduced model are nonnegative population shares. -/
theorem reduced_nonnegativeWeights {m n K : ℕ}
    (R : ReductionWitness m n K) :
    R.reduced.NonnegativeWeights := by
  intro k
  rw [R.weight_eq_typeWeight k]
  exact RecommendationModel.UserTypeAssignment.typeWeight_nonneg R.data.types k

/-- Chosen representatives make every reduced type weight strictly positive. -/
theorem reduced_positiveWeights_of_representatives {m n K : ℕ}
    [NeZero m]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    R.reduced.PositiveWeights := by
  intro k
  rw [R.weight_eq_typeWeight k]
  unfold RecommendationModel.UserTypeAssignment.typeWeight
    RecommendationModel.UserTypeAssignment.typeCard
  have hmem :
      reps.repr k ∈
        (Finset.univ.filter fun u => R.data.types.toType u = k) := by
    simp [reps.repr_spec k]
  exact div_pos
    (by exact_mod_cast Finset.card_pos.mpr ⟨reps.repr k, hmem⟩)
    (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))

/-- Original entrywise utility nonnegativity transfers to the reduced model. -/
theorem reduced_nonnegativeUtilities_of_nonnegative
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hNonneg : R.data.model.Nonnegative) :
    R.reduced.NonnegativeUtilities := by
  intro k j
  have h := hNonneg (reps.repr k) j
  rw [R.utility_agrees (reps.repr k) j] at h
  simpa [reps.repr_spec k] using h

/-- Original entrywise strict positivity transfers to the reduced model. -/
theorem reduced_positiveUtilities_of_positive
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive) :
    R.reduced.PositiveUtilities := by
  intro k j
  have h := hPos (reps.repr k) j
  rw [R.utility_agrees (reps.repr k) j] at h
  simpa [reps.repr_spec k] using h

/--
A lifted reduced policy gives each original user exactly the raw utility of that
user's type in the reduced model.
-/
theorem rawUserUtility_liftedPolicy_eq_rawTypeUtility {m n K : ℕ}
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) (u : User m) :
    RecommendationModel.rawUserUtility R.data.model (R.liftedPolicy ρ) u =
      TypeWeightedRecommendationModel.rawTypeUtility R.reduced ρ (R.data.types.toType u) := by
  unfold RecommendationModel.rawUserUtility TypeWeightedRecommendationModel.rawTypeUtility
    AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp ReductionWitness.liftedPolicy
    UserTypeAssignment.liftTypePolicy AppliedModelingLib.Policy.liftAlong
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [R.utility_agrees u j]

/-- Best-item normalizers are preserved by the reduction for each original user. -/
theorem bestItemUtility_eq_bestTypeUtility {m n K : ℕ} [NeZero n]
    (R : ReductionWitness m n K) (u : User m) :
    RecommendationModel.bestItemUtility R.data.model u =
      TypeWeightedRecommendationModel.bestItemUtility R.reduced (R.data.types.toType u) := by
  have hrow : R.data.model.utility u = R.reduced.utility (R.data.types.toType u) := by
    funext j
    exact R.utility_agrees u j
  unfold RecommendationModel.bestItemUtility TypeWeightedRecommendationModel.bestItemUtility
  rw [hrow]

/-- Normalized user utility is preserved pointwise under lifting from the reduced model. -/
theorem normalizedUserUtility_liftedPolicy_eq_normalizedTypeUtility {m n K : ℕ} [NeZero n]
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) (u : User m) :
    RecommendationModel.normalizedUserUtility R.data.model (R.liftedPolicy ρ) u =
      TypeWeightedRecommendationModel.normalizedTypeUtility R.reduced ρ (R.data.types.toType u) := by
  unfold RecommendationModel.normalizedUserUtility
    TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [rawUserUtility_liftedPolicy_eq_rawTypeUtility (R := R) (ρ := ρ) (u := u)]
  rw [bestItemUtility_eq_bestTypeUtility (R := R) (u := u)]

/--
Lifted reduced policies preserve item raw utility up to the common population
scale.  The reduced weights are population shares, so multiplying the reduced
sum by the number of users recovers the source sum.
-/
theorem rawItemUtility_liftedPolicy_eq_card_mul_rawItemUtility {m n K : ℕ}
    [NeZero m]
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) (j : Item n) :
    RecommendationModel.rawItemUtility R.data.model (R.liftedPolicy ρ) j =
      (m : ℝ) * TypeWeightedRecommendationModel.rawItemUtility R.reduced ρ j := by
  classical
  unfold RecommendationModel.rawItemUtility TypeWeightedRecommendationModel.rawItemUtility
    ReductionWitness.liftedPolicy UserTypeAssignment.liftTypePolicy AppliedModelingLib.Policy.liftAlong
  have hm : (m : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne m
  calc
    ∑ u : User m, R.data.model.utility u j * (ρ (R.data.types.toType u) j).toReal
        = ∑ u : User m,
            R.reduced.utility (R.data.types.toType u) j *
              (ρ (R.data.types.toType u) j).toReal := by
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [R.utility_agrees u j]
    _ = ∑ k : UserType K,
          (RecommendationModel.UserTypeAssignment.typeCard R.data.types k : ℝ) *
            (R.reduced.utility k j * (ρ k j).toReal) := by
          exact (AppliedModelingLib.Policy.sum_fiber_card_mul
            (τ := R.data.types.toType)
            (f := fun k : UserType K => R.reduced.utility k j * (ρ k j).toReal)).symm
    _ = (m : ℝ) * ∑ k : UserType K,
          R.reduced.weight k * R.reduced.utility k j * (ρ k j).toReal := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [R.weight_eq_typeWeight k]
          simp only [RecommendationModel.UserTypeAssignment.typeWeight]
          field_simp [hm]

/--
Lifted reduced policies preserve item normalizers up to the same common
population scale as their raw item utilities.
-/
theorem itemNormalizer_eq_card_mul_itemNormalizer {m n K : ℕ}
    [NeZero m]
    (R : ReductionWitness m n K) (j : Item n) :
    RecommendationModel.itemNormalizer R.data.model j =
      (m : ℝ) * TypeWeightedRecommendationModel.itemNormalizer R.reduced j := by
  classical
  unfold RecommendationModel.itemNormalizer TypeWeightedRecommendationModel.itemNormalizer
  have hm : (m : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne m
  calc
    ∑ u : User m, R.data.model.utility u j
        = ∑ u : User m, R.reduced.utility (R.data.types.toType u) j := by
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [R.utility_agrees u j]
    _ = ∑ k : UserType K,
          (RecommendationModel.UserTypeAssignment.typeCard R.data.types k : ℝ) *
            R.reduced.utility k j := by
          exact (AppliedModelingLib.Policy.sum_fiber_card_mul
            (τ := R.data.types.toType)
            (f := fun k : UserType K => R.reduced.utility k j)).symm
    _ = (m : ℝ) * ∑ k : UserType K,
        R.reduced.weight k * R.reduced.utility k j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [R.weight_eq_typeWeight k]
          simp only [RecommendationModel.UserTypeAssignment.typeWeight]
          field_simp [hm]

/-- Lifted reduced policies preserve normalized item utility pointwise. -/
theorem normalizedItemUtility_liftedPolicy_eq_normalizedItemUtility {m n K : ℕ}
    [NeZero m]
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) (j : Item n) :
    RecommendationModel.normalizedItemUtility R.data.model (R.liftedPolicy ρ) j =
      TypeWeightedRecommendationModel.normalizedItemUtility R.reduced ρ j := by
  unfold RecommendationModel.normalizedItemUtility
    TypeWeightedRecommendationModel.normalizedItemUtility
  rw [rawItemUtility_liftedPolicy_eq_card_mul_rawItemUtility
    (R := R) (ρ := ρ) (j := j)]
  rw [itemNormalizer_eq_card_mul_itemNormalizer (R := R) (j := j)]
  have hm : (m : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne m
  by_cases hden : TypeWeightedRecommendationModel.itemNormalizer R.reduced j = 0
  · simp [hden]
  · simp [hm, hden]
    field_simp [hm, hden]

/-- The source user-coordinate item-equality row for a lifted reduced policy is
the corresponding reduced equality-LP row. -/
theorem userReduced_itemEqualityExpression_eq_reduced_dot
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (ρ : TypePolicy K n) (ell : ℝ) (j : Item n) :
    RecommendationModel.propositionOneItemEqualityExpression
        R.data.model j (R.liftedPolicy ρ) ell =
      (∑ v : TypePolicy.ReducedEqualityLPVariable K n,
        TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced j v *
          TypePolicy.reducedEqualityLPCandidate ρ ell v) := by
  have hWeight : R.reduced.PositiveWeights :=
    R.reduced_positiveWeights_of_representatives reps
  have hUtil : R.reduced.PositiveUtilities :=
    R.reduced_positiveUtilities_of_positive reps hPos
  calc
    RecommendationModel.propositionOneItemEqualityExpression
        R.data.model j (R.liftedPolicy ρ) ell
        = RecommendationModel.normalizedItemUtility
            R.data.model (R.liftedPolicy ρ) j - ell := by
          rw [RecommendationModel.propositionOneItemEqualityExpression_eq_normalized_sub
            R.data.model hPos]
    _ = TypeWeightedRecommendationModel.normalizedItemUtility
            R.reduced ρ j - ell := by
          rw [normalizedItemUtility_liftedPolicy_eq_normalizedItemUtility
            (R := R) (ρ := ρ) (j := j)]
    _ = (∑ v : TypePolicy.ReducedEqualityLPVariable K n,
        TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced j v *
          TypePolicy.reducedEqualityLPCandidate ρ ell v) := by
          exact (TypeWeightedRecommendationModel.equalityLPItemNormal_dot_candidate_eq
            R.reduced ρ ell j
            (TypeWeightedRecommendationModel.itemNormalizer_pos_of_positive
              R.reduced hWeight hUtil j).ne').symm

/-- The objective coordinate is unchanged by the source/reduced LP coordinate
map. -/
theorem userReduced_objective_eq {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (ρ : TypePolicy K n) (ell : ℝ) :
    RecommendationModel.UserSymmetricEqualityLP.reduceUserSymmetricEqualityLP
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        reps (R.liftedPolicy ρ) ell (Sum.inr ()) =
      TypePolicy.reducedEqualityLPCandidate ρ ell (Sum.inr ()) := by
  exact congrFun
    (RecommendationModel.UserSymmetricEqualityLP.reduceUserSymmetricEqualityLP_liftReducedEqualityLP
      (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
      reps ρ ell)
    (Sum.inr ())

/-- For a type-symmetric user policy, feasibility in the source user-coordinate
LP is equivalent to feasibility of the descended reduced equality LP. -/
theorem userReduced_feasible_iff
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (ρ : Policy m n) (ell : ℝ)
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ) :
    (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data).Feasible ρ ell ↔
      TypeWeightedRecommendationModel.EqualityLPFeasible R.reduced
        (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell := by
  constructor
  · intro hfeas j
    have htransport :=
      userReduced_itemEqualityExpression_eq_reduced_dot
        (R := R) (reps := reps) hPos
        (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell j
    rw [← htransport]
    have hlift :
        UserTypeAssignment.liftTypePolicy R.data.types
            (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) = ρ :=
      UserTypeAssignment.liftTypePolicy_descendTypePolicy_eq_of_isTypeSymmetric
        R.data.types reps ρ hρ
    change RecommendationModel.propositionOneItemEqualityExpression R.data.model j
        (UserTypeAssignment.liftTypePolicy R.data.types
          (UserTypeAssignment.descendTypePolicy R.data.types reps ρ)) ell = 0
    rw [hlift]
    exact hfeas.2.2.2 j
  · intro hred
    refine ⟨?_, ?_, hρ, ?_⟩
    · intro u
      exact AppliedModelingLib.pmfToRealSum (ρ u)
    · intro u j
      exact ENNReal.toReal_nonneg
    · intro j
      have htransport :=
        userReduced_itemEqualityExpression_eq_reduced_dot
          (R := R) (reps := reps) hPos
          (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell j
      have hlift :
          UserTypeAssignment.liftTypePolicy R.data.types
              (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) = ρ :=
        UserTypeAssignment.liftTypePolicy_descendTypePolicy_eq_of_isTypeSymmetric
          R.data.types reps ρ hρ
      rw [← hlift]
      change RecommendationModel.propositionOneItemEqualityExpression R.data.model j
          (R.liftedPolicy
            (UserTypeAssignment.descendTypePolicy R.data.types reps ρ)) ell = 0
      rw [htransport]
      exact hred j

/-- Objective optimality transports between the source user-coordinate equality
LP on `S_symm` and the reduced equality LP. -/
theorem userReduced_optimal_iff
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (ρ : Policy m n) (ell : ℝ)
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ) :
    (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data).Optimal ρ ell ↔
      TypeWeightedRecommendationModel.EqualityLPOptimal R.reduced
        (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell := by
  constructor
  · intro hopt
    refine ⟨(userReduced_feasible_iff
      (R := R) (reps := reps) hPos ρ ell hρ).mp hopt.1, ?_⟩
    intro ρK ell' hred
    have hsym_lift :
        UserTypeAssignment.IsTypeSymmetric R.data.types (R.liftedPolicy ρK) :=
      R.liftedPolicy_isTypeSymmetric ρK
    have hLiftFeas :
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data).Feasible
          (R.liftedPolicy ρK) ell' := by
      refine (userReduced_feasible_iff
        (R := R) (reps := reps) hPos (R.liftedPolicy ρK) ell' hsym_lift).mpr ?_
      simpa [ReductionWitness.liftedPolicy] using hred
    exact hopt.2 (R.liftedPolicy ρK) ell' hLiftFeas
  · intro hopt
    refine ⟨(userReduced_feasible_iff
      (R := R) (reps := reps) hPos ρ ell hρ).mpr hopt.1, ?_⟩
    intro ρ' ell' hfeas'
    have hsym' : UserTypeAssignment.IsTypeSymmetric R.data.types ρ' :=
      hfeas'.2.2.1
    have hred' :
        TypeWeightedRecommendationModel.EqualityLPFeasible R.reduced
          (UserTypeAssignment.descendTypePolicy R.data.types reps ρ') ell' :=
      (userReduced_feasible_iff
        (R := R) (reps := reps) hPos ρ' ell' hsym').mp hfeas'
    exact hopt.2
      (UserTypeAssignment.descendTypePolicy R.data.types reps ρ') ell' hred'

/-- Item-equality active rows correspond between a lifted reduced candidate and
the source user-coordinate LP. -/
theorem userReduced_itemActive_lift_iff
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (ρ : TypePolicy K n) (ell : ℝ) (j : Item n) :
    RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        (R.liftedPolicy ρ) ell (Sum.inl (Sum.inl (Sum.inl j))) ↔
      TypePolicy.ReducedEqualityLPConstraintActive
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        ρ ell (Sum.inl (Sum.inl j)) := by
  rw [RecommendationModel.UserSymmetricEqualityLP.ConstraintActive,
    TypePolicy.ReducedEqualityLPConstraintActive]
  change RecommendationModel.propositionOneItemEqualityExpression
      R.data.model j (R.liftedPolicy ρ) ell = 0 ↔
    (∑ v : TypePolicy.ReducedEqualityLPVariable K n,
      TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced j v *
        TypePolicy.reducedEqualityLPCandidate ρ ell v) = 0
  rw [userReduced_itemEqualityExpression_eq_reduced_dot
    (R := R) (reps := reps) hPos ρ ell j]

/-- A source user-simplex active row at any user is the corresponding reduced
type-simplex active row after lifting. -/
theorem userReduced_simplexActive_lift_iff
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (ρ : TypePolicy K n) (ell : ℝ) (u : User m) :
    RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        (R.liftedPolicy ρ) ell (Sum.inl (Sum.inl (Sum.inr u))) ↔
      TypePolicy.ReducedEqualityLPConstraintActive
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        ρ ell (Sum.inl (Sum.inr (R.data.types.toType u))) := by
  simp [RecommendationModel.UserSymmetricEqualityLP.ConstraintActive,
    TypePolicy.ReducedEqualityLPConstraintActive, liftedPolicy,
    UserTypeAssignment.liftTypePolicy]

/-- Binding nonnegativity rows duplicate by type under the lift from reduced
coordinates to source user coordinates. -/
theorem userReduced_nonnegativityActive_lift_iff
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (ρ : TypePolicy K n) (ell : ℝ) (u : User m) (j : Item n) :
    RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        (R.liftedPolicy ρ) ell (Sum.inr (u, j)) ↔
      TypePolicy.ReducedEqualityLPConstraintActive
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        ρ ell (Sum.inr (R.data.types.toType u, j)) := by
  simp [RecommendationModel.UserSymmetricEqualityLP.ConstraintActive,
    TypePolicy.ReducedEqualityLPConstraintActive, liftedPolicy,
    UserTypeAssignment.liftTypePolicy]

/-- Every type-symmetry row of the source LP is active on a lifted reduced
candidate. These rows have no reduced-LP counterpart; they are the redundant
source rows that the later rank argument must eliminate. -/
theorem userReduced_typeSymmetryActive_lift
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (ρ : TypePolicy K n) (ell : ℝ)
    (c : UserTypeAssignment.TypeSymmetryLinearConstraintIndex m n) :
    RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        (R.liftedPolicy ρ) ell (Sum.inl (Sum.inr c)) := by
  change UserTypeAssignment.typeSymmetryLinearExpression R.data.types c
      (R.liftedPolicy ρ) = 0
  exact
    (UserTypeAssignment.satisfiesTypeSymmetryLinearConstraints_iff_isTypeSymmetric
      R.data.types (R.liftedPolicy ρ)).mpr
      (R.liftedPolicy_isTypeSymmetric ρ) c

/-- Item-equality active rows correspond when a type-symmetric source candidate
is descended to reduced coordinates. -/
theorem userReduced_itemActive_descend_iff
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (ρ : Policy m n) (ell : ℝ)
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (j : Item n) :
    TypePolicy.ReducedEqualityLPConstraintActive
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell
        (Sum.inl (Sum.inl j)) ↔
      RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        ρ ell (Sum.inl (Sum.inl (Sum.inl j))) := by
  have htransport :=
    userReduced_itemEqualityExpression_eq_reduced_dot
      (R := R) (reps := reps) hPos
      (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell j
  have hlift :
      R.liftedPolicy
          (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) = ρ := by
    exact UserTypeAssignment.liftTypePolicy_descendTypePolicy_eq_of_isTypeSymmetric
      R.data.types reps ρ hρ
  rw [RecommendationModel.UserSymmetricEqualityLP.ConstraintActive,
    TypePolicy.ReducedEqualityLPConstraintActive]
  change
    (∑ v : TypePolicy.ReducedEqualityLPVariable K n,
      TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced j v *
        TypePolicy.reducedEqualityLPCandidate
          (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell v) = 0 ↔
      RecommendationModel.propositionOneItemEqualityExpression
        R.data.model j ρ ell = 0
  rw [← htransport, hlift]

/-- A reduced type-simplex active row is the source user-simplex active row at
the chosen representative of that type. -/
theorem userReduced_simplexActive_descend_representative_iff
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (ρ : Policy m n) (ell : ℝ) (k : UserType K) :
    TypePolicy.ReducedEqualityLPConstraintActive
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell
        (Sum.inl (Sum.inr k)) ↔
      RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        ρ ell (Sum.inl (Sum.inl (Sum.inr (reps.repr k)))) := by
  simp [RecommendationModel.UserSymmetricEqualityLP.ConstraintActive,
    TypePolicy.ReducedEqualityLPConstraintActive,
    UserTypeAssignment.descendTypePolicy]

/-- A reduced binding nonnegativity row is the source binding nonnegativity row
at the chosen representative of that type. -/
theorem userReduced_nonnegativityActive_descend_representative_iff
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (ρ : Policy m n) (ell : ℝ) (k : UserType K) (j : Item n) :
    TypePolicy.ReducedEqualityLPConstraintActive
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell
        (Sum.inr (k, j)) ↔
      RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        ρ ell (Sum.inr (reps.repr k, j)) := by
  simp [RecommendationModel.UserSymmetricEqualityLP.ConstraintActive,
    TypePolicy.ReducedEqualityLPConstraintActive,
    UserTypeAssignment.descendTypePolicy]

/-- Map each reduced equality-LP row to the representative source row that
checks the same item equality, type simplex row, or binding type-item
nonnegativity row. Source type-symmetry rows are intentionally not in the image;
they are redundant rows to be handled by the rank transport theorem. -/
def representativeSourceConstraint
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    TypePolicy.ReducedEqualityLPConstraint K n →
      RecommendationModel.UserSymmetricEqualityLP.Constraint m n K
  | Sum.inl (Sum.inl j) => Sum.inl (Sum.inl (Sum.inl j))
  | Sum.inl (Sum.inr k) => Sum.inl (Sum.inl (Sum.inr (reps.repr k)))
  | Sum.inr (k, j) => Sum.inr (reps.repr k, j)

/-- Representative users for distinct declared types are distinct. -/
theorem typeRepresentatives_repr_injective
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    Function.Injective reps.repr := by
  intro k k' hrepr
  have htype := congrArg R.data.types.toType hrepr
  simpa [reps.repr_spec k, reps.repr_spec k'] using htype

/-- The representative row map embeds reduced row indices into source row
indices. It does not cover source type-symmetry rows or duplicate nonnegativity
rows. -/
theorem representativeSourceConstraint_injective
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    Function.Injective (representativeSourceConstraint R reps) := by
  intro c c' h
  rcases c with (j | k) | ⟨k, j⟩
  · rcases c' with (j' | k') | ⟨k', j'⟩
    · simpa [representativeSourceConstraint] using h
    · simp [representativeSourceConstraint] at h
    · simp [representativeSourceConstraint] at h
  · rcases c' with (j' | k') | ⟨k', j'⟩
    · simp [representativeSourceConstraint] at h
    · have hrepr : reps.repr k = reps.repr k' := by
        simpa [representativeSourceConstraint] using h
      have hk := typeRepresentatives_repr_injective R reps hrepr
      simpa [hk]
    · simp [representativeSourceConstraint] at h
  · rcases c' with (j' | k') | ⟨k', j'⟩
    · simp [representativeSourceConstraint] at h
    · simp [representativeSourceConstraint] at h
    · have hpair : (reps.repr k, j) = (reps.repr k', j') := by
        simpa [representativeSourceConstraint] using h
      have hrepr : reps.repr k = reps.repr k' := congrArg Prod.fst hpair
      have hk := typeRepresentatives_repr_injective R reps hrepr
      have hj : j = j' := congrArg Prod.snd hpair
      cases hk
      cases hj
      rfl

/-- Image cardinality for a reduced row set under the representative source-row
embedding. -/
theorem representativeSourceConstraint_image_card
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (basis : Finset (TypePolicy.ReducedEqualityLPConstraint K n)) :
    (basis.image (representativeSourceConstraint R reps)).card = basis.card := by
  exact Finset.card_image_of_injective basis
    (representativeSourceConstraint_injective R reps)

/-- The representative source rows associated with a reduced row set. -/
noncomputable def representativeSourceBasis
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (basis : Finset (TypePolicy.ReducedEqualityLPConstraint K n)) :
    Finset (RecommendationModel.UserSymmetricEqualityLP.Constraint m n K) :=
  basis.image (representativeSourceConstraint R reps)

theorem representativeSourceBasis_card
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (basis : Finset (TypePolicy.ReducedEqualityLPConstraint K n)) :
    (representativeSourceBasis R reps basis).card = basis.card := by
  simpa [representativeSourceBasis] using
    representativeSourceConstraint_image_card R reps basis

/-- Pull a source normal vector on user coordinates back to reduced
type-coordinates by summing user-coordinate coefficients over each type fiber
and preserving the objective-coordinate coefficient. This is the transpose of
the lift map on candidates. -/
noncomputable def sourceNormalPullback
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (a : RecommendationModel.UserSymmetricEqualityLP.Variable m n → ℝ) :
    TypePolicy.ReducedEqualityLPVariable K n → ℝ
  | Sum.inl (k, j) =>
      (Finset.univ.filter (fun u : User m => R.data.types.toType u = k)).sum
        (fun u => a (Sum.inl (u, j)))
  | Sum.inr e => a (Sum.inr e)

/-- The source-normal pullback is linear in the source normal vector. -/
noncomputable def sourceNormalPullbackLinear
    {m n K : ℕ}
    (R : ReductionWitness m n K) :
    (RecommendationModel.UserSymmetricEqualityLP.Variable m n → ℝ) →ₗ[ℝ]
      (TypePolicy.ReducedEqualityLPVariable K n → ℝ) where
  toFun := sourceNormalPullback R
  map_add' := by
    intro a b
    funext v
    rcases v with ⟨k, j⟩ | e
    · simp [sourceNormalPullback, Pi.add_apply, Finset.sum_add_distrib]
    · simp [sourceNormalPullback]
  map_smul' := by
    intro r a
    funext v
    rcases v with ⟨k, j⟩ | e
    · simp [sourceNormalPullback, Pi.smul_apply, Finset.mul_sum]
    · simp [sourceNormalPullback]

@[simp] theorem sourceNormalPullbackLinear_apply
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (a : RecommendationModel.UserSymmetricEqualityLP.Variable m n → ℝ) :
    sourceNormalPullbackLinear R a = sourceNormalPullback R a := rfl

/-- A section of `sourceNormalPullback`: place each reduced type-item
coefficient on the chosen representative user for that type and put zero on all
other users, preserving the objective coefficient. -/
noncomputable def sourceNormalSection
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (b : TypePolicy.ReducedEqualityLPVariable K n → ℝ) :
    RecommendationModel.UserSymmetricEqualityLP.Variable m n → ℝ
  | Sum.inl (u, j) =>
      if u = reps.repr (R.data.types.toType u) then
        b (Sum.inl (R.data.types.toType u, j))
      else 0
  | Sum.inr e => b (Sum.inr e)

/-- The explicit section is a right inverse to the source-normal pullback. -/
theorem sourceNormalPullback_sourceNormalSection
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (b : TypePolicy.ReducedEqualityLPVariable K n → ℝ) :
    sourceNormalPullback R (sourceNormalSection R reps b) = b := by
  classical
  funext v
  rcases v with ⟨k, j⟩ | e
  · let fiber :=
      Finset.univ.filter (fun u : User m => R.data.types.toType u = k)
    have hsum :
        fiber.sum
          (fun u : User m =>
            if u = reps.repr (R.data.types.toType u) then
              b (Sum.inl (R.data.types.toType u, j))
            else 0) =
          b (Sum.inl (k, j)) := by
      simpa [fiber, reps.repr_spec k] using
        (Finset.sum_eq_single
          (s := fiber)
          (f := fun u : User m =>
            if u = reps.repr (R.data.types.toType u) then
              b (Sum.inl (R.data.types.toType u, j))
            else 0)
          (reps.repr k)
          (by
            intro u hu hne
            have htype : R.data.types.toType u = k := by
              simpa [fiber] using hu
            have hne_rep : u ≠ reps.repr (R.data.types.toType u) := by
              intro hu_rep
              apply hne
              calc
                u = reps.repr (R.data.types.toType u) := hu_rep
                _ = reps.repr k := by rw [htype]
            simp [hne_rep])
          (by
            intro hnot
            exfalso
            apply hnot
            simp [fiber, reps.repr_spec k]))
    simpa [sourceNormalPullback, sourceNormalSection, fiber] using hsum
  · simp [sourceNormalPullback, sourceNormalSection]

/-- The source-normal pullback is surjective onto reduced normal vectors. -/
theorem sourceNormalPullbackLinear_surjective
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    Function.Surjective (sourceNormalPullbackLinear R) := by
  intro b
  refine ⟨sourceNormalSection R reps b, ?_⟩
  simpa using sourceNormalPullback_sourceNormalSection R reps b

/-- The source user-coordinate equality LP has exactly `m * n + 1` scalar
coordinates: one coordinate for each original user-item pair plus the objective
coordinate. -/
theorem sourceVariable_finrank
    {m n : ℕ} :
    Module.finrank ℝ
      (RecommendationModel.UserSymmetricEqualityLP.Variable m n → ℝ) =
      m * n + 1 := by
  classical
  rw [Module.finrank_fintype_fun_eq_card]
  simp [RecommendationModel.UserSymmetricEqualityLP.Variable, User, Item]

/-- The reduced equality LP has exactly `n * K + 1` scalar coordinates:
one coordinate for each type-item pair plus the objective coordinate. -/
theorem reducedEqualityLPVariable_finrank
    {K n : ℕ} :
    Module.finrank ℝ (TypePolicy.ReducedEqualityLPVariable K n → ℝ) =
      n * K + 1 := by
  classical
  rw [Module.finrank_fintype_fun_eq_card]
  simp [TypePolicy.ReducedEqualityLPVariable, UserType, Item, Nat.mul_comm]

/-- A source active basis spans the whole source dual coordinate space. This is
the semantic rank content of the source active-basis fields, independent of any
paper-facing theorem name. -/
theorem sourceActiveBasis_sourceNormal_span_top
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    {ρ : Policy m n} {ell : ℝ}
    (hsource : RecommendationModel.UserSymmetricEqualityLP.ActiveBasis
      (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data) ρ ell) :
    Submodule.span ℝ
        (Set.range fun c : {c // c ∈ hsource.basis} =>
          RecommendationModel.UserSymmetricEqualityLP.constraintNormal
            (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
            c.1) =
      ⊤ := by
  classical
  have hcardSubtype :
      Fintype.card {c // c ∈ hsource.basis} = hsource.basis.card := by
    simpa using hsource.basis.card_attach
  have hcard :
      Fintype.card {c // c ∈ hsource.basis} =
        Module.finrank ℝ
          (RecommendationModel.UserSymmetricEqualityLP.Variable m n → ℝ) := by
    rw [hcardSubtype, hsource.basis_card, sourceVariable_finrank]
  exact hsource.basis_independent.span_eq_top_of_card_eq_finrank' hcard

/-- Pulling back the normals in a source active basis spans the whole reduced
dual coordinate space. This records that the quotient normal map has enough
semantic rank before any choice of reduced active row subset is made. -/
theorem sourceActiveBasis_sourceNormalPullback_span_top
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {ρ : Policy m n} {ell : ℝ}
    (hsource : RecommendationModel.UserSymmetricEqualityLP.ActiveBasis
      (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data) ρ ell) :
    Submodule.span ℝ
        (Set.range fun c : {c // c ∈ hsource.basis} =>
          sourceNormalPullback R
            (RecommendationModel.UserSymmetricEqualityLP.constraintNormal
              (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
              c.1)) =
      ⊤ := by
  classical
  let f := sourceNormalPullbackLinear R
  let sourceNormals :=
    fun c : {c // c ∈ hsource.basis} =>
      RecommendationModel.UserSymmetricEqualityLP.constraintNormal
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        c.1
  have hspan :
      Submodule.span ℝ (Set.range sourceNormals) = ⊤ :=
    sourceActiveBasis_sourceNormal_span_top (R := R) hsource
  calc
    Submodule.span ℝ (Set.range fun c : {c // c ∈ hsource.basis} =>
        sourceNormalPullback R
          (RecommendationModel.UserSymmetricEqualityLP.constraintNormal
            (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
            c.1))
        =
      Submodule.map f (Submodule.span ℝ (Set.range sourceNormals)) := by
        rw [Submodule.map_span]
        congr 1
        ext b
        constructor
        · intro hb
          rcases hb with ⟨c, rfl⟩
          exact ⟨sourceNormals c, ⟨c, rfl⟩, rfl⟩
        · intro hb
          rcases hb with ⟨a, ⟨c, rfl⟩, rfl⟩
          exact ⟨c, rfl⟩
    _ = Submodule.map f ⊤ := by rw [hspan]
    _ = LinearMap.range f := by simp [f]
    _ = ⊤ := LinearMap.range_eq_top.mpr
      (sourceNormalPullbackLinear_surjective R reps)

/-- The source item-equality normal pulls back to the population-weighted
reduced item-equality normal. -/
theorem sourceNormalPullback_itemEqualityNormal
    {m n K : ℕ} [NeZero m]
    (R : ReductionWitness m n K) (j : Item n) :
    sourceNormalPullback R
        (RecommendationModel.UserSymmetricEqualityLP.itemEqualityNormal
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data) j) =
      TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced j := by
  classical
  funext v
  rcases v with ⟨k, j'⟩ | e
  · by_cases hitem : j' = j
    · subst j'
      have hfiber :
          ((Finset.univ.filter (fun u : User m =>
              R.data.types.toType u = k)).sum
            (fun u =>
              R.data.model.utility u j /
                RecommendationModel.itemNormalizer R.data.model j)) =
            (RecommendationModel.UserTypeAssignment.typeCard R.data.types k : ℝ) *
              (R.reduced.utility k j /
                RecommendationModel.itemNormalizer R.data.model j) := by
        calc
          ((Finset.univ.filter (fun u : User m =>
              R.data.types.toType u = k)).sum
            (fun u =>
              R.data.model.utility u j /
                RecommendationModel.itemNormalizer R.data.model j))
              =
            (Finset.univ.filter (fun u : User m =>
              R.data.types.toType u = k)).sum
              (fun _ =>
                R.reduced.utility k j /
                  RecommendationModel.itemNormalizer R.data.model j) := by
                refine Finset.sum_congr rfl ?_
                intro u hu
                have htype : R.data.types.toType u = k := by
                  simpa using hu
                rw [R.utility_agrees u j, htype]
          _ = (RecommendationModel.UserTypeAssignment.typeCard R.data.types k : ℝ) *
                (R.reduced.utility k j /
                  RecommendationModel.itemNormalizer R.data.model j) := by
                simp [RecommendationModel.UserTypeAssignment.typeCard, nsmul_eq_mul]
      calc
        sourceNormalPullback R
            (RecommendationModel.UserSymmetricEqualityLP.itemEqualityNormal
              (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data) j)
            (Sum.inl (k, j))
            =
              (RecommendationModel.UserTypeAssignment.typeCard R.data.types k : ℝ) *
                (R.reduced.utility k j /
                  RecommendationModel.itemNormalizer R.data.model j) := by
                simpa [sourceNormalPullback,
                  RecommendationModel.UserSymmetricEqualityLP.itemEqualityNormal] using hfiber
        _ = R.reduced.weight k * R.reduced.utility k j /
              TypeWeightedRecommendationModel.itemNormalizer R.reduced j := by
              rw [R.weight_eq_typeWeight k]
              rw [itemNormalizer_eq_card_mul_itemNormalizer (R := R) (j := j)]
              simp only [RecommendationModel.UserTypeAssignment.typeWeight]
              have hm : (m : ℝ) ≠ 0 := by
                exact_mod_cast NeZero.ne m
              by_cases hden : TypeWeightedRecommendationModel.itemNormalizer R.reduced j = 0
              · simp [hden]
              · field_simp [hm, hden]
        _ = TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced j
              (Sum.inl (k, j)) := by
              simp [TypeWeightedRecommendationModel.equalityLPItemNormal]
    · simp [sourceNormalPullback,
        RecommendationModel.UserSymmetricEqualityLP.itemEqualityNormal,
        TypeWeightedRecommendationModel.equalityLPItemNormal, hitem]
  · simp [sourceNormalPullback,
      RecommendationModel.UserSymmetricEqualityLP.itemEqualityNormal,
      TypeWeightedRecommendationModel.equalityLPItemNormal]

/-- A representative source user-simplex normal pulls back to the corresponding
reduced type-simplex normal. -/
theorem sourceNormalPullback_representative_simplexNormal
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (k : UserType K) :
    sourceNormalPullback R
        (RecommendationModel.UserSymmetricEqualityLP.constraintNormal
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
          (representativeSourceConstraint R reps (Sum.inl (Sum.inr k)))) =
      TypePolicy.reducedEqualityLPConstraintNormal
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        (Sum.inl (Sum.inr k)) := by
  classical
  funext v
  rcases v with ⟨k0, j0⟩ | e
  · by_cases hk : k0 = k
    · subst k0
      simp [sourceNormalPullback, representativeSourceConstraint,
        RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
        TypePolicy.reducedEqualityLPConstraintNormal, reps.repr_spec k]
    · have hzero :
        ((Finset.univ.filter (fun u : User m => R.data.types.toType u = k0)).sum
          (fun u : User m => if u = reps.repr k then (1 : ℝ) else 0)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro u hu
        have htype : R.data.types.toType u = k0 := by
          simpa using hu
        have hne : u ≠ reps.repr k := by
          intro hu_eq
          apply hk
          calc
            k0 = R.data.types.toType u := htype.symm
            _ = R.data.types.toType (reps.repr k) := by rw [hu_eq]
            _ = k := reps.repr_spec k
        simp [hne]
      simp [sourceNormalPullback, representativeSourceConstraint,
        RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
        TypePolicy.reducedEqualityLPConstraintNormal, hk, hzero]
  · simp [sourceNormalPullback, representativeSourceConstraint,
      RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
      TypePolicy.reducedEqualityLPConstraintNormal]

/-- Any source user-simplex normal pulls back to the reduced simplex row for
that user's type, making the duplicate source rows explicit. -/
theorem sourceNormalPullback_simplexNormal
    {m n K : ℕ}
    (R : ReductionWitness m n K) (u0 : User m) :
    sourceNormalPullback R
        (RecommendationModel.UserSymmetricEqualityLP.constraintNormal
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
          (Sum.inl (Sum.inl (Sum.inr u0)))) =
      TypePolicy.reducedEqualityLPConstraintNormal
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        (Sum.inl (Sum.inr (R.data.types.toType u0))) := by
  classical
  funext v
  rcases v with ⟨k0, j0⟩ | e
  · by_cases hk : k0 = R.data.types.toType u0
    · subst k0
      simp [sourceNormalPullback,
        RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
        TypePolicy.reducedEqualityLPConstraintNormal]
    · have hzero :
        ((Finset.univ.filter (fun u : User m => R.data.types.toType u = k0)).sum
          (fun u : User m => if u = u0 then (1 : ℝ) else 0)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro u hu
        have htype : R.data.types.toType u = k0 := by
          simpa using hu
        have hne : u ≠ u0 := by
          intro hu_eq
          apply hk
          calc
            k0 = R.data.types.toType u := htype.symm
            _ = R.data.types.toType u0 := by rw [hu_eq]
        simp [hne]
      simp [sourceNormalPullback,
        RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
        TypePolicy.reducedEqualityLPConstraintNormal, hk, hzero]
  · simp [sourceNormalPullback,
      RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
      TypePolicy.reducedEqualityLPConstraintNormal]

/-- A representative source nonnegativity normal pulls back to the corresponding
reduced type-item nonnegativity normal. -/
theorem sourceNormalPullback_representative_nonnegativityNormal
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (k : UserType K) (j : Item n) :
    sourceNormalPullback R
        (RecommendationModel.UserSymmetricEqualityLP.constraintNormal
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
          (representativeSourceConstraint R reps (Sum.inr (k, j)))) =
      TypePolicy.reducedEqualityLPConstraintNormal
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        (Sum.inr (k, j)) := by
  classical
  funext v
  rcases v with ⟨k0, j0⟩ | e
  · by_cases hk : k0 = k
    · subst k0
      by_cases hj : j0 = j
      · subst j0
        simp [sourceNormalPullback, representativeSourceConstraint,
          RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
          TypePolicy.reducedEqualityLPConstraintNormal, reps.repr_spec k]
      · simp [sourceNormalPullback, representativeSourceConstraint,
          RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
          TypePolicy.reducedEqualityLPConstraintNormal, hj]
    · have hzero :
        ((Finset.univ.filter (fun u : User m => R.data.types.toType u = k0)).sum
          (fun u : User m =>
            if u = reps.repr k ∧ j0 = j then (1 : ℝ) else 0)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro u hu
        have htype : R.data.types.toType u = k0 := by
          simpa using hu
        have hne : u ≠ reps.repr k := by
          intro hu_eq
          apply hk
          calc
            k0 = R.data.types.toType u := htype.symm
            _ = R.data.types.toType (reps.repr k) := by rw [hu_eq]
            _ = k := reps.repr_spec k
        simp [hne]
      simp [sourceNormalPullback, representativeSourceConstraint,
        RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
        TypePolicy.reducedEqualityLPConstraintNormal, hk, hzero]
  · simp [sourceNormalPullback, representativeSourceConstraint,
      RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
      TypePolicy.reducedEqualityLPConstraintNormal]

/-- Any source nonnegativity normal pulls back to the reduced nonnegativity row
for that user's type and item. -/
theorem sourceNormalPullback_nonnegativityNormal
    {m n K : ℕ}
    (R : ReductionWitness m n K) (u0 : User m) (j : Item n) :
    sourceNormalPullback R
        (RecommendationModel.UserSymmetricEqualityLP.constraintNormal
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
          (Sum.inr (u0, j))) =
      TypePolicy.reducedEqualityLPConstraintNormal
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        (Sum.inr (R.data.types.toType u0, j)) := by
  classical
  funext v
  rcases v with ⟨k0, j0⟩ | e
  · by_cases hk : k0 = R.data.types.toType u0
    · subst k0
      by_cases hj : j0 = j
      · subst j0
        simp [sourceNormalPullback,
          RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
          TypePolicy.reducedEqualityLPConstraintNormal]
      · simp [sourceNormalPullback,
          RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
          TypePolicy.reducedEqualityLPConstraintNormal, hj]
    · have hzero :
        ((Finset.univ.filter (fun u : User m => R.data.types.toType u = k0)).sum
          (fun u : User m =>
            if u = u0 ∧ j0 = j then (1 : ℝ) else 0)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro u hu
        have htype : R.data.types.toType u = k0 := by
          simpa using hu
        have hne : u ≠ u0 := by
          intro hu_eq
          apply hk
          calc
            k0 = R.data.types.toType u := htype.symm
            _ = R.data.types.toType u0 := by rw [hu_eq]
        simp [hne]
      simp [sourceNormalPullback,
        RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
        TypePolicy.reducedEqualityLPConstraintNormal, hk, hzero]
  · simp [sourceNormalPullback,
      RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
      TypePolicy.reducedEqualityLPConstraintNormal]

/-- Source type-symmetry normals pull back to zero on reduced coordinates. They
are quotient-kernel rows, not reduced LP rows. -/
theorem sourceNormalPullback_typeSymmetryNormal
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (c : UserTypeAssignment.TypeSymmetryLinearConstraintIndex m n) :
    sourceNormalPullback R
        (RecommendationModel.UserSymmetricEqualityLP.constraintNormal
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
          (Sum.inl (Sum.inr c))) = 0 := by
  classical
  rcases c with ⟨u1, u2, jc⟩
  funext v
  rcases v with ⟨k, j0⟩ | e
  · by_cases htype : R.data.types.toType u1 = R.data.types.toType u2
    · by_cases hj : j0 = jc
      · subst j0
        by_cases hk : k = R.data.types.toType u1
        · subst k
          let fiber :=
            Finset.univ.filter
              (fun u : User m => R.data.types.toType u = R.data.types.toType u1)
          have hsum1 :
              fiber.sum (fun u : User m => if u = u1 then (1 : ℝ) else 0) = 1 := by
            simpa using
              (Finset.sum_eq_single
                (s := fiber)
                (f := fun u : User m => if u = u1 then (1 : ℝ) else 0)
                u1
                (by
                  intro u _hu hne
                  simp [hne])
                (by
                  intro hnot
                  exfalso
                  apply hnot
                  simp [fiber]))
          have hsum2 :
              fiber.sum (fun u : User m => if u = u2 then (1 : ℝ) else 0) = 1 := by
            simpa using
              (Finset.sum_eq_single
                (s := fiber)
                (f := fun u : User m => if u = u2 then (1 : ℝ) else 0)
                u2
                (by
                  intro u _hu hne
                  simp [hne])
                (by
                  intro hnot
                  exfalso
                  apply hnot
                  simp [fiber, htype.symm]))
          calc
            sourceNormalPullback R
                (RecommendationModel.UserSymmetricEqualityLP.constraintNormal
                  (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
                  (Sum.inl (Sum.inr (u1, u2, jc)))) (Sum.inl (R.data.types.toType u1, jc))
                =
                  fiber.sum
                    (fun u : User m =>
                      (if u = u1 then (1 : ℝ) else 0) -
                        (if u = u2 then (1 : ℝ) else 0)) := by
                    simp [sourceNormalPullback,
                      RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
                      UserTypeAssignment.typeSymmetryLinearCoefficient, htype, fiber]
            _ = fiber.sum (fun u : User m => if u = u1 then (1 : ℝ) else 0) -
                  fiber.sum (fun u : User m => if u = u2 then (1 : ℝ) else 0) := by
                    rw [Finset.sum_sub_distrib]
            _ = 0 := by
                    rw [hsum1, hsum2]
                    norm_num
        · have hzero :
            ((Finset.univ.filter (fun u : User m => R.data.types.toType u = k)).sum
              (fun u : User m =>
                (if u = u1 then (1 : ℝ) else 0) -
                  (if u = u2 then (1 : ℝ) else 0))) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro u hu
            have hku : R.data.types.toType u = k := by
              simpa using hu
            have hne1 : u ≠ u1 := by
              intro hu1
              apply hk
              calc
                k = R.data.types.toType u := hku.symm
                _ = R.data.types.toType u1 := by rw [hu1]
            have hne2 : u ≠ u2 := by
              intro hu2
              apply hk
              calc
                k = R.data.types.toType u := hku.symm
                _ = R.data.types.toType u2 := by rw [hu2]
                _ = R.data.types.toType u1 := htype.symm
            simp [hne1, hne2]
          simpa [sourceNormalPullback,
            RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
            UserTypeAssignment.typeSymmetryLinearCoefficient, htype, hzero]
      · simp [sourceNormalPullback,
          RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
          UserTypeAssignment.typeSymmetryLinearCoefficient, hj]
    · have htype' :
        ¬(RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data).types.toType u1 =
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data).types.toType u2 := by
        simpa using htype
      simp [sourceNormalPullback,
        RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
        UserTypeAssignment.typeSymmetryLinearCoefficient, htype']
  · simp [sourceNormalPullback,
      RecommendationModel.UserSymmetricEqualityLP.constraintNormal]

/-- The reduced row, if any, represented by a source user-coordinate LP row
after quotienting by user types. Type-symmetry rows map to `none` because their
normals lie in the pullback kernel. -/
def sourceConstraintReducedImage
    {m n K : ℕ}
    (R : ReductionWitness m n K) :
    RecommendationModel.UserSymmetricEqualityLP.Constraint m n K →
      Option (TypePolicy.ReducedEqualityLPConstraint K n)
  | Sum.inl (Sum.inl (Sum.inl j)) => some (Sum.inl (Sum.inl j))
  | Sum.inl (Sum.inl (Sum.inr u)) => some (Sum.inl (Sum.inr (R.data.types.toType u)))
  | Sum.inl (Sum.inr _c) => none
  | Sum.inr (u, j) => some (Sum.inr (R.data.types.toType u, j))

/-- Every source row normal pulls back either to its quotient reduced-row normal
or to zero for source type-symmetry rows. -/
theorem sourceNormalPullback_constraintNormal
    {m n K : ℕ} [NeZero m]
    (R : ReductionWitness m n K)
    (c : RecommendationModel.UserSymmetricEqualityLP.Constraint m n K) :
    sourceNormalPullback R
        (RecommendationModel.UserSymmetricEqualityLP.constraintNormal
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data) c) =
      match sourceConstraintReducedImage R c with
      | some cRed =>
          TypePolicy.reducedEqualityLPConstraintNormal
            (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced) cRed
      | none => 0 := by
  rcases c with ((j | u) | cSymm) | ⟨u, j⟩
  · simpa [sourceConstraintReducedImage,
      RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
      TypePolicy.reducedEqualityLPConstraintNormal] using
      sourceNormalPullback_itemEqualityNormal (R := R) j
  · simpa [sourceConstraintReducedImage] using
      sourceNormalPullback_simplexNormal (R := R) u
  · simpa [sourceConstraintReducedImage] using
      sourceNormalPullback_typeSymmetryNormal (R := R) cSymm
  · simpa [sourceConstraintReducedImage] using
      sourceNormalPullback_nonnegativityNormal (R := R) u j

/-- The reduced rows obtained by quotienting a source row set through
`sourceConstraintReducedImage`. This deliberately keeps only the semantic image:
duplicate source user rows collapse to one reduced row, and type-symmetry rows
are discarded. -/
noncomputable def sourceReducedRowImage
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (basis : Finset (RecommendationModel.UserSymmetricEqualityLP.Constraint m n K)) :
    Finset (TypePolicy.ReducedEqualityLPConstraint K n) :=
  Finset.univ.filter fun cRed =>
    ∃ c ∈ basis, sourceConstraintReducedImage R c = some cRed

theorem mem_sourceReducedRowImage
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (basis : Finset (RecommendationModel.UserSymmetricEqualityLP.Constraint m n K))
    (cRed : TypePolicy.ReducedEqualityLPConstraint K n) :
    cRed ∈ sourceReducedRowImage R basis ↔
      ∃ c ∈ basis, sourceConstraintReducedImage R c = some cRed := by
  classical
  simp [sourceReducedRowImage]

/-- Activity transports from any source row to its quotient reduced row. This
does not assert that the quotient image has enough rows or is independent. -/
theorem sourceConstraintReducedImage_active_descend
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (ρ : Policy m n) (ell : ℝ)
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (c : RecommendationModel.UserSymmetricEqualityLP.Constraint m n K)
    (cRed : TypePolicy.ReducedEqualityLPConstraint K n)
    (himage : sourceConstraintReducedImage R c = some cRed)
    (hactive :
      RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        ρ ell c) :
    TypePolicy.ReducedEqualityLPConstraintActive
      (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
      (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell cRed := by
  rcases c with ((j | u) | cSymm) | ⟨u, j⟩
  · have hcRed : cRed = Sum.inl (Sum.inl j) := by
      simpa [sourceConstraintReducedImage] using (Option.some.inj himage).symm
    subst cRed
    exact
      (userReduced_itemActive_descend_iff
        (R := R) (reps := reps) hPos ρ ell hρ j).mpr hactive
  · have hcRed : cRed = Sum.inl (Sum.inr (R.data.types.toType u)) := by
      simpa [sourceConstraintReducedImage] using (Option.some.inj himage).symm
    subst cRed
    simpa [TypePolicy.ReducedEqualityLPConstraintActive] using
      AppliedModelingLib.pmfToRealSum
        ((UserTypeAssignment.descendTypePolicy R.data.types reps ρ)
          (R.data.types.toType u))
  · simp [sourceConstraintReducedImage] at himage
  · have hcRed : cRed = Sum.inr (R.data.types.toType u, j) := by
      simpa [sourceConstraintReducedImage] using (Option.some.inj himage).symm
    subst cRed
    have hrow : ρ (reps.repr (R.data.types.toType u)) = ρ u := by
      exact hρ (reps.repr (R.data.types.toType u)) u
        (by simpa using reps.repr_spec (R.data.types.toType u))
    simpa [RecommendationModel.UserSymmetricEqualityLP.ConstraintActive,
      TypePolicy.ReducedEqualityLPConstraintActive,
      UserTypeAssignment.descendTypePolicy, hrow] using hactive

/-- The quotient image of an active source row set consists of active reduced
rows. This is a rank-transport input only; it still carries no independence or
cardinality claim. -/
theorem sourceReducedRowImage_active_descend
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (ρ : Policy m n) (ell : ℝ)
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    {basis : Finset (RecommendationModel.UserSymmetricEqualityLP.Constraint m n K)}
    (hbasis_active :
      ∀ c ∈ basis,
        RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
          ρ ell c) :
    ∀ cRed ∈ sourceReducedRowImage R basis,
      TypePolicy.ReducedEqualityLPConstraintActive
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell cRed := by
  intro cRed hcRed
  rcases (mem_sourceReducedRowImage R basis cRed).mp hcRed with
    ⟨c, hcBasis, himage⟩
  exact sourceConstraintReducedImage_active_descend
    (R := R) (reps := reps) hPos ρ ell hρ c cRed himage
    (hbasis_active c hcBasis)

/-- A source active basis supplies reduced equality feasibility after descending
the type-symmetric source candidate. -/
theorem sourceActiveBasis_equalityLPFeasible_descend
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    {ρ : Policy m n} {ell : ℝ}
    (hsource : RecommendationModel.UserSymmetricEqualityLP.ActiveBasis
      (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data) ρ ell) :
    TypeWeightedRecommendationModel.EqualityLPFeasible R.reduced
      (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell := by
  exact
    (userReduced_feasible_iff
      (R := R) (reps := reps) hPos ρ ell hsource.feasible.2.2.1).mp
      hsource.feasible

/-- The quotient image of a source active basis consists of active reduced rows.
This derives the activity part of the reduced BFS candidate from source data,
but still makes no cardinality or independence claim. -/
theorem sourceActiveBasis_reducedRowImage_active_descend
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    {ρ : Policy m n} {ell : ℝ}
    (hsource : RecommendationModel.UserSymmetricEqualityLP.ActiveBasis
      (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data) ρ ell) :
    ∀ cRed ∈ sourceReducedRowImage R hsource.basis,
      TypePolicy.ReducedEqualityLPConstraintActive
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell cRed := by
  exact sourceReducedRowImage_active_descend
    (R := R) (reps := reps) hPos ρ ell hsource.feasible.2.2.1
    hsource.basis_active

/-- The quotient image of a source active basis spans the whole reduced dual
space. This is the rank statement needed before extracting a reduced
full-cardinality independent active subset. -/
theorem sourceActiveBasis_reducedRowImage_normal_span_top
    {m n K : ℕ} [NeZero m]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {ρ : Policy m n} {ell : ℝ}
    (hsource : RecommendationModel.UserSymmetricEqualityLP.ActiveBasis
      (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data) ρ ell) :
    Submodule.span ℝ
        (Set.range fun cRed : {c // c ∈ sourceReducedRowImage R hsource.basis} =>
          TypePolicy.reducedEqualityLPConstraintNormal
            (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
            cRed.1) =
      ⊤ := by
  classical
  let redNormal :=
    fun cRed : TypePolicy.ReducedEqualityLPConstraint K n =>
      TypePolicy.reducedEqualityLPConstraintNormal
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        cRed
  have hpull :
      Submodule.span ℝ
          (Set.range fun c : {c // c ∈ hsource.basis} =>
            sourceNormalPullback R
              (RecommendationModel.UserSymmetricEqualityLP.constraintNormal
                (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
                c.1)) =
        ⊤ :=
    sourceActiveBasis_sourceNormalPullback_span_top
      (R := R) (reps := reps) hsource
  apply le_antisymm le_top
  rw [← hpull]
  apply Submodule.span_le.mpr
  rintro a ⟨c, rfl⟩
  change sourceNormalPullback R
      (RecommendationModel.UserSymmetricEqualityLP.constraintNormal
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        c.1) ∈
    Submodule.span ℝ
      (Set.range fun cRed : {c // c ∈ sourceReducedRowImage R hsource.basis} =>
        TypePolicy.reducedEqualityLPConstraintNormal
          (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
          cRed.1)
  rw [sourceNormalPullback_constraintNormal]
  cases himage : sourceConstraintReducedImage R c.1 with
  | none =>
      simp
  | some cRed =>
      apply Submodule.subset_span
      refine ⟨⟨cRed, ?_⟩, ?_⟩
      · exact (mem_sourceReducedRowImage R hsource.basis cRed).mpr
          ⟨c.1, c.2, himage⟩
      · rfl

/-- The active quotient rows contain `n * K + 1` independent reduced normal
vectors. This is the finite-dimensional extraction step from the spanning
rank statement; a later theorem chooses corresponding row indices and packages
the reduced active-basis structure. -/
theorem sourceActiveBasis_exists_independent_reducedRowImage_normals
    {m n K : ℕ} [NeZero m]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {ρ : Policy m n} {ell : ℝ}
    (hsource : RecommendationModel.UserSymmetricEqualityLP.ActiveBasis
      (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data) ρ ell) :
    ∃ normals : Finset (TypePolicy.ReducedEqualityLPVariable K n → ℝ),
      (normals : Set (TypePolicy.ReducedEqualityLPVariable K n → ℝ)) ⊆
        Set.range
          (fun cRed : {c // c ∈ sourceReducedRowImage R hsource.basis} =>
            TypePolicy.reducedEqualityLPConstraintNormal
              (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
              cRed.1) ∧
      normals.card = n * K + 1 ∧
      LinearIndepOn ℝ id
        (normals : Set (TypePolicy.ReducedEqualityLPVariable K n → ℝ)) := by
  classical
  let reducedNormalSet :
      Set (TypePolicy.ReducedEqualityLPVariable K n → ℝ) :=
    Set.range
      (fun cRed : {c // c ∈ sourceReducedRowImage R hsource.basis} =>
        TypePolicy.reducedEqualityLPConstraintNormal
          (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
          cRed.1)
  have hspan :
      Submodule.span ℝ reducedNormalSet = ⊤ := by
    simpa [reducedNormalSet] using
      sourceActiveBasis_reducedRowImage_normal_span_top
        (R := R) (reps := reps) hsource
  obtain ⟨normals, hsubset, hcard, _hspanNormals, hind⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn ℝ reducedNormalSet
  refine ⟨normals, hsubset, ?_, hind⟩
  rw [hcard, hspan, finrank_top, reducedEqualityLPVariable_finrank]

/-- The quotient image of a source active basis has at least the reduced LP
dimension many semantic rows. This is a consequence of spanning the reduced
dual; it is not a cardinality assumption smuggled into the statement. -/
theorem sourceActiveBasis_reducedRowImage_card_ge
    {m n K : ℕ} [NeZero m]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {ρ : Policy m n} {ell : ℝ}
    (hsource : RecommendationModel.UserSymmetricEqualityLP.ActiveBasis
      (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data) ρ ell) :
    n * K + 1 ≤ (sourceReducedRowImage R hsource.basis).card := by
  classical
  let redNormal :=
    fun cRed : {c // c ∈ sourceReducedRowImage R hsource.basis} =>
      TypePolicy.reducedEqualityLPConstraintNormal
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        cRed.1
  have hspan :
      Submodule.span ℝ (Set.range redNormal) = ⊤ :=
    sourceActiveBasis_reducedRowImage_normal_span_top
      (R := R) (reps := reps) hsource
  have hfinrank_le_image :
      Module.finrank ℝ (Submodule.span ℝ (Set.range redNormal)) ≤
        ((sourceReducedRowImage R hsource.basis).attach.image redNormal).card := by
    simpa using
      (finrank_span_le_card (R := ℝ)
        (M := TypePolicy.ReducedEqualityLPVariable K n → ℝ)
        (Set.range redNormal))
  have himage_le_domain :
      ((sourceReducedRowImage R hsource.basis).attach.image redNormal).card ≤
        (sourceReducedRowImage R hsource.basis).card := by
    calc
      ((sourceReducedRowImage R hsource.basis).attach.image redNormal).card ≤
          (sourceReducedRowImage R hsource.basis).attach.card :=
            Finset.card_image_le
      _ = (sourceReducedRowImage R hsource.basis).card := by
            simp
  calc
    n * K + 1 =
        Module.finrank ℝ (TypePolicy.ReducedEqualityLPVariable K n → ℝ) := by
          rw [reducedEqualityLPVariable_finrank]
    _ = Module.finrank ℝ (Submodule.span ℝ (Set.range redNormal)) := by
          rw [hspan, finrank_top]
    _ ≤ ((sourceReducedRowImage R hsource.basis).attach.image redNormal).card :=
          hfinrank_le_image
    _ ≤ (sourceReducedRowImage R hsource.basis).card := himage_le_domain

/-- A source active basis descends to reduced basic feasibility by extracting
an independent full-cardinality subset of the active quotient rows. -/
theorem sourceActiveBasis_reducedBasicFeasible_descend
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    {ρ : Policy m n} {ell : ℝ}
    (hsource : RecommendationModel.UserSymmetricEqualityLP.ActiveBasis
      (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data) ρ ell) :
    TypePolicy.ReducedEqualityLPBasicFeasible
      (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
      (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell := by
  classical
  let redNormal :=
    fun cRed : TypePolicy.ReducedEqualityLPConstraint K n =>
      TypePolicy.reducedEqualityLPConstraintNormal
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        cRed
  obtain ⟨normals, hnormals_subset, hnormals_card, hnormals_ind⟩ :=
    sourceActiveBasis_exists_independent_reducedRowImage_normals
      (R := R) (reps := reps) hsource
  let chooseRow :
      normals →
        {c // c ∈ sourceReducedRowImage R hsource.basis} :=
    fun x =>
      Classical.choose (hnormals_subset x.2)
  have chooseRow_spec :
      ∀ x : normals, redNormal (chooseRow x).1 = x.1 := by
    intro x
    exact Classical.choose_spec (hnormals_subset x.2)
  have chooseRow_injective :
      Function.Injective (fun x : normals => (chooseRow x).1) := by
    intro x y hxy
    apply Subtype.ext
    calc
      x.1 = redNormal (chooseRow x).1 := (chooseRow_spec x).symm
      _ = redNormal (chooseRow y).1 := congrArg redNormal hxy
      _ = y.1 := chooseRow_spec y
  let basis : Finset (TypePolicy.ReducedEqualityLPConstraint K n) :=
    normals.attach.image (fun x : normals => (chooseRow x).1)
  have hbasis_subset :
      basis ⊆ sourceReducedRowImage R hsource.basis := by
    intro c hc
    rcases Finset.mem_image.mp hc with ⟨x, _hx, rfl⟩
    exact (chooseRow x).2
  have hbasis_card : basis.card = normals.card := by
    simpa [basis] using
      Finset.card_image_of_injective normals.attach chooseRow_injective
  have hbasis_card_target : basis.card = n * K + 1 := by
    rw [hbasis_card, hnormals_card]
  let toBasis : normals → {c // c ∈ basis} :=
    fun x =>
      ⟨(chooseRow x).1, by
        exact Finset.mem_image.mpr ⟨x, Finset.mem_attach _ _, rfl⟩⟩
  have htoBasis_injective : Function.Injective toBasis := by
    intro x y hxy
    apply chooseRow_injective
    exact congrArg (fun z : {c // c ∈ basis} => z.1) hxy
  have htoBasis_surjective : Function.Surjective toBasis := by
    intro c
    rcases Finset.mem_image.mp c.2 with ⟨x, _hx, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx
  let e : normals ≃ {c // c ∈ basis} :=
    Equiv.ofBijective toBasis ⟨htoBasis_injective, htoBasis_surjective⟩
  have hnormals_independent :
      LinearIndependent ℝ
        (fun x : normals => (x : TypePolicy.ReducedEqualityLPVariable K n → ℝ)) := by
    simpa [LinearIndepOn] using hnormals_ind
  have hbasis_independent :
      LinearIndependent ℝ
        (fun c : {c // c ∈ basis} => redNormal c.1) := by
    apply (linearIndependent_equiv e).mp
    change LinearIndependent ℝ
      (fun x : normals => redNormal (toBasis x).1)
    simpa [toBasis, redNormal, chooseRow_spec] using hnormals_independent
  refine ⟨?_⟩
  refine
    { equality_feasible :=
        sourceActiveBasis_equalityLPFeasible_descend
          (R := R) (reps := reps) hPos hsource
      basis := basis
      basis_card := hbasis_card_target
      basis_independent := ?_
      basis_active := ?_ }
  · simpa [redNormal] using hbasis_independent
  · intro c hc
    exact sourceActiveBasis_reducedRowImage_active_descend
      (R := R) (reps := reps) hPos hsource c (hbasis_subset hc)

/-- Every reduced-row normal is the pullback of the corresponding
representative source-row normal. This packages the weighted item-row identity
with the representative simplex and nonnegativity row identities. -/
theorem sourceNormalPullback_representativeSourceConstraintNormal
    {m n K : ℕ} [NeZero m]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (c : TypePolicy.ReducedEqualityLPConstraint K n) :
    sourceNormalPullback R
        (RecommendationModel.UserSymmetricEqualityLP.constraintNormal
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
          (representativeSourceConstraint R reps c)) =
      TypePolicy.reducedEqualityLPConstraintNormal
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced) c := by
  rcases c with (j | k) | ⟨k, j⟩
  · simpa [representativeSourceConstraint,
      RecommendationModel.UserSymmetricEqualityLP.constraintNormal,
      TypePolicy.reducedEqualityLPConstraintNormal] using
      sourceNormalPullback_itemEqualityNormal (R := R) j
  · exact sourceNormalPullback_representative_simplexNormal
      (R := R) (reps := reps) k
  · exact sourceNormalPullback_representative_nonnegativityNormal
      (R := R) (reps := reps) k j

/-- Activity of every mapped reduced row is preserved after lifting to source
coordinates. -/
theorem userReduced_representativeSourceConstraintActive_lift_iff
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (ρ : TypePolicy K n) (ell : ℝ)
    (c : TypePolicy.ReducedEqualityLPConstraint K n) :
    RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        (R.liftedPolicy ρ) ell
        (representativeSourceConstraint R reps c) ↔
      TypePolicy.ReducedEqualityLPConstraintActive
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        ρ ell c := by
  rcases c with (j | k) | ⟨k, j⟩
  · exact userReduced_itemActive_lift_iff
      (R := R) (reps := reps) hPos ρ ell j
  · simpa [representativeSourceConstraint, reps.repr_spec k] using
      userReduced_simplexActive_lift_iff
        (R := R) ρ ell (reps.repr k)
  · simpa [representativeSourceConstraint, reps.repr_spec k] using
      userReduced_nonnegativityActive_lift_iff
        (R := R) ρ ell (reps.repr k) j

/-- Activity of every mapped reduced row is preserved when a type-symmetric
source candidate is descended to reduced coordinates. -/
theorem userReduced_representativeSourceConstraintActive_descend_iff
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (ρ : Policy m n) (ell : ℝ)
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (c : TypePolicy.ReducedEqualityLPConstraint K n) :
    TypePolicy.ReducedEqualityLPConstraintActive
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell c ↔
      RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        ρ ell (representativeSourceConstraint R reps c) := by
  rcases c with (j | k) | ⟨k, j⟩
  · exact userReduced_itemActive_descend_iff
      (R := R) (reps := reps) hPos ρ ell hρ j
  · exact userReduced_simplexActive_descend_representative_iff
      (R := R) (reps := reps) ρ ell k
  · exact userReduced_nonnegativityActive_descend_representative_iff
      (R := R) (reps := reps) ρ ell k j

/-- A reduced active row set maps to active representative source rows for the
lifted source candidate. This is only an activity statement, not an independence
or full-source-basis statement. -/
theorem representativeSourceBasis_active_lift
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    {ρ : TypePolicy K n} {ell : ℝ}
    (hbasis : TypePolicy.ReducedEqualityLPActiveBasis
      (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced) ρ ell) :
    ∀ c ∈ representativeSourceBasis R reps hbasis.basis,
      RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        (R.liftedPolicy ρ) ell c := by
  intro c hc
  change c ∈ hbasis.basis.image (representativeSourceConstraint R reps) at hc
  rcases Finset.mem_image.mp hc with ⟨cRed, hcRed, rfl⟩
  exact
    (userReduced_representativeSourceConstraintActive_lift_iff
      (R := R) (reps := reps) hPos ρ ell cRed).mpr
      (hbasis.basis_active cRed hcRed)

/-- For a type-symmetric source candidate, all same-type source nonnegativity
rows have the same active status as the corresponding reduced row. -/
theorem userReduced_nonnegativityActive_descend_iff
    {m n K : ℕ}
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (ρ : Policy m n) (ell : ℝ)
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (u : User m) (j : Item n) :
    RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
        (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
        ρ ell (Sum.inr (u, j)) ↔
      TypePolicy.ReducedEqualityLPConstraintActive
        (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
        (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell
        (Sum.inr (R.data.types.toType u, j)) := by
  have hrow : ρ (reps.repr (R.data.types.toType u)) = ρ u := by
    exact hρ (reps.repr (R.data.types.toType u)) u
      (by simpa using reps.repr_spec (R.data.types.toType u))
  simp [RecommendationModel.UserSymmetricEqualityLP.ConstraintActive,
    TypePolicy.ReducedEqualityLPConstraintActive,
    UserTypeAssignment.descendTypePolicy, hrow]

/-- The semantic active-row correspondence between the source user-coordinate LP
restricted to `S_symm` and the reduced type-coordinate LP. This theorem only
transports row activity; it deliberately does not assert rank or BFS transport. -/
theorem userReduced_activeRows_correspond
    {m n K : ℕ} [NeZero m] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (ρ : Policy m n) (ell : ℝ)
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ) :
    (∀ j : Item n,
        TypePolicy.ReducedEqualityLPConstraintActive
          (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
          (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell
          (Sum.inl (Sum.inl j)) ↔
        RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
          ρ ell (Sum.inl (Sum.inl (Sum.inl j)))) ∧
      (∀ k : UserType K,
        TypePolicy.ReducedEqualityLPConstraintActive
          (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
          (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell
          (Sum.inl (Sum.inr k)) ↔
        RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
          ρ ell (Sum.inl (Sum.inl (Sum.inr (reps.repr k))))) ∧
      (∀ u : User m, ∀ j : Item n,
        RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
          ρ ell (Sum.inr (u, j)) ↔
        TypePolicy.ReducedEqualityLPConstraintActive
          (TypeWeightedRecommendationModel.equalityLPItemNormal R.reduced)
          (UserTypeAssignment.descendTypePolicy R.data.types reps ρ) ell
          (Sum.inr (R.data.types.toType u, j))) ∧
      (∀ c : UserTypeAssignment.TypeSymmetryLinearConstraintIndex m n,
        RecommendationModel.UserSymmetricEqualityLP.ConstraintActive
          (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData R.data)
          ρ ell (Sum.inl (Sum.inr c))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    exact userReduced_itemActive_descend_iff
      (R := R) (reps := reps) hPos ρ ell hρ j
  · intro k
    exact userReduced_simplexActive_descend_representative_iff
      (R := R) (reps := reps) ρ ell k
  · intro u j
    exact userReduced_nonnegativityActive_descend_iff
      (R := R) (reps := reps) ρ ell hρ u j
  · intro c
    change UserTypeAssignment.typeSymmetryLinearExpression R.data.types c ρ = 0
    exact
      (UserTypeAssignment.satisfiesTypeSymmetryLinearConstraints_iff_isTypeSymmetric
        R.data.types ρ).mpr hρ c

/-- Lifted reduced policies preserve minimum item fairness. -/
theorem itemFairness_liftedPolicy_eq_itemFairness {m n K : ℕ} [NeZero m] [NeZero n]
    (R : ReductionWitness m n K) (ρ : TypePolicy K n) :
    RecommendationModel.itemFairness R.data.model (R.liftedPolicy ρ) =
      TypeWeightedRecommendationModel.itemFairness R.reduced ρ := by
  unfold RecommendationModel.itemFairness TypeWeightedRecommendationModel.itemFairness
    AppliedModelingLib.finiteMin
  exact Finset.inf'_congr Finset.univ_nonempty rfl
    (by
      intro j _
      exact normalizedItemUtility_liftedPolicy_eq_normalizedItemUtility
        (R := R) (ρ := ρ) (j := j))

/--
With representatives for every user type, lifted reduced policies preserve
minimum user fairness.
-/
theorem userFairness_liftedPolicy_eq_typeFairness {m n K : ℕ}
    [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (ρ : TypePolicy K n) :
    RecommendationModel.userFairness R.data.model (R.liftedPolicy ρ) =
      TypeWeightedRecommendationModel.typeFairness R.reduced ρ := by
  let f : UserType K → ℝ :=
    fun k => TypeWeightedRecommendationModel.normalizedTypeUtility R.reduced ρ k
  calc
    RecommendationModel.userFairness R.data.model (R.liftedPolicy ρ)
        = AppliedModelingLib.finiteMin
            (fun u : User m => f (R.data.types.toType u)) := by
          unfold RecommendationModel.userFairness AppliedModelingLib.finiteMin f
          exact Finset.inf'_congr Finset.univ_nonempty rfl
            (by
              intro u _
              exact normalizedUserUtility_liftedPolicy_eq_normalizedTypeUtility
                (R := R) (ρ := ρ) (u := u))
    _ = AppliedModelingLib.finiteMin f := by
          exact AppliedModelingLib.Policy.finiteMin_comp_of_fiberRepresentatives
            R.data.types.toType reps f
    _ = TypeWeightedRecommendationModel.typeFairness R.reduced ρ := by
          rfl

/--
If the reduced and original optimal values agree, reduced optimality lifts to
original optimality.  This isolates the remaining LP-value equality seam.
-/
theorem isOptimalAtLevel_liftedPolicy_of_reduced
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) (ρ : TypePolicy K n)
    (hItemOpt :
      RecommendationModel.optimalItemFairness R.data.model =
        TypeWeightedRecommendationModel.optimalItemFairness R.reduced)
    (hUserOpt :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ) :
    RecommendationModel.IsOptimalAtLevel R.data.model γ (R.liftedPolicy ρ) := by
  constructor
  · unfold RecommendationModel.feasibleAtLevel
    rw [hItemOpt]
    rw [itemFairness_liftedPolicy_eq_itemFairness (R := R) (ρ := ρ)]
    exact hopt.1
  · rw [userFairness_liftedPolicy_eq_typeFairness (R := R) (reps := reps) (ρ := ρ)]
    rw [hUserOpt]
    exact hopt.2

/--
Every type-symmetric user-level policy has a reduced representative preserving
both fairness functionals exactly.
-/
theorem exists_typePolicy_preserving_fairness_of_isTypeSymmetric
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        RecommendationModel.itemFairness R.data.model ρ =
          TypeWeightedRecommendationModel.itemFairness R.reduced ρK ∧
        RecommendationModel.userFairness R.data.model ρ =
          TypeWeightedRecommendationModel.typeFairness R.reduced ρK := by
  obtain ⟨ρK, hlift⟩ :=
    ReductionWitness.exists_typePolicy_of_isTypeSymmetric R reps hρ
  refine ⟨ρK, hlift, ?_, ?_⟩
  · rw [← hlift]
    exact itemFairness_liftedPolicy_eq_itemFairness (R := R) (ρ := ρK)
  · rw [← hlift]
    exact userFairness_liftedPolicy_eq_typeFairness
      (R := R) (reps := reps) (ρ := ρK)

/--
The item-fairness values attainable by symmetric user-level policies are exactly
the values attainable by reduced type-level policies.
-/
theorem symmetricAttainableItemFairnessSet_eq_reduced
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    RecommendationModel.symmetricAttainableItemFairnessSet R.data =
      TypeWeightedRecommendationModel.attainableItemFairnessSet R.reduced := by
  ext r
  constructor
  · intro hr
    obtain ⟨ρ, hsym, hr⟩ := hr
    obtain ⟨ρK, _hlift, hitem, _huser⟩ :=
      exists_typePolicy_preserving_fairness_of_isTypeSymmetric
        (R := R) (reps := reps) hsym
    refine ⟨ρK, ?_⟩
    rw [hr]
    exact hitem
  · intro hr
    obtain ⟨ρK, hr⟩ := hr
    refine ⟨R.liftedPolicy ρK, R.liftedPolicy_isTypeSymmetric ρK, ?_⟩
    rw [hr]
    exact (itemFairness_liftedPolicy_eq_itemFairness
      (R := R) (ρ := ρK)).symm

/-- Symmetric user-level optimal item fairness equals reduced optimal item fairness. -/
theorem symmetricOptimalItemFairness_eq_reduced
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    RecommendationModel.symmetricOptimalItemFairness R.data =
      TypeWeightedRecommendationModel.optimalItemFairness R.reduced := by
  unfold RecommendationModel.symmetricOptimalItemFairness
    TypeWeightedRecommendationModel.optimalItemFairness
  rw [symmetricAttainableItemFairnessSet_eq_reduced (R := R) (reps := reps)]

/--
Conversely, if a user-level optimum is type-symmetric and the original/reduced
optimal values agree, then it descends to a reduced optimum.
-/
theorem exists_reducedOptimalAtLevel_of_original_symmetric_optimal
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hItemOpt :
      RecommendationModel.optimalItemFairness R.data.model =
        TypeWeightedRecommendationModel.optimalItemFairness R.reduced)
    (hUserOpt :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρK := by
  obtain ⟨ρK, hlift, hitem, huser⟩ :=
    exists_typePolicy_preserving_fairness_of_isTypeSymmetric
      (R := R) (reps := reps) hρ
  refine ⟨ρK, hlift, ?_⟩
  constructor
  · unfold TypeWeightedRecommendationModel.feasibleAtLevel
    have hfeas := hopt.1
    unfold RecommendationModel.feasibleAtLevel at hfeas
    rw [hItemOpt] at hfeas
    rw [hitem] at hfeas
    exact hfeas
  · have hufair := hopt.2
    rw [hUserOpt] at hufair
    rw [huser] at hufair
    exact hufair

end ReductionWitness

end GCG24UserItemFairness
