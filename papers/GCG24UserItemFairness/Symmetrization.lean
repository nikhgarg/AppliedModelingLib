import GCG24UserItemFairness.ReductionPreservation
import AppliedModelingLib.Applications.RecommenderSystems.PolicyAveraging
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

open scoped BigOperators
open AppliedModelingLib

namespace GCG24UserItemFairness

namespace UserTypeAssignment

/-- The finite set of users assigned to type `k`. -/
def fiberUsers {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (k : UserType K) :
    Finset (User m) :=
  (Finset.univ : Finset (User m)).filter fun u => τ.toType u = k

/-- Chosen representatives imply every type fiber is nonempty. -/
theorem fiberUsers_nonempty {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (k : UserType K) :
    (fiberUsers τ k).Nonempty := by
  classical
  refine ⟨reps.repr k, ?_⟩
  simp [fiberUsers, reps.repr_spec k]

/--
Average an arbitrary user-level policy over each user type, producing a
type-level policy.
-/
noncomputable def averageTypePolicy {m n K : ℕ} [NeZero K]
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n) : TypePolicy K n :=
  fun k =>
    AppliedModelingLib.Policy.averageOn ρ (fiberUsers τ k)
      (fiberUsers_nonempty τ reps k)

/-- The averaged type policy has action probabilities equal to fiber averages. -/
theorem averageTypePolicy_apply_toReal {m n K : ℕ} [NeZero K]
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n)
    (k : UserType K) (j : Item n) :
    ((averageTypePolicy τ reps ρ k) j).toReal =
      (∑ u ∈ fiberUsers τ k, (ρ u j).toReal) /
        ((fiberUsers τ k).card : ℝ) := by
  exact AppliedModelingLib.Policy.averageOn_apply_toReal ρ (fiberUsers τ k)
    (fiberUsers_nonempty τ reps k) j

/-- Summing over fibers recovers the original user sum. -/
theorem sum_fiberUsers {m K : ℕ} [NeZero K]
    (τ : RecommendationModel.UserTypeAssignment m K) (f : User m → ℝ) :
    (∑ k : UserType K, ∑ u ∈ fiberUsers τ k, f u) =
      ∑ u : User m, f u := by
  classical
  unfold fiberUsers
  simpa using
    (Finset.sum_fiberwise
      (s := (Finset.univ : Finset (User m))) (g := τ.toType) (f := f))

/--
Weighted sums are preserved by replacing every user policy with the average
policy of its type.
-/
theorem sum_weighted_averageTypePolicy_apply_toReal
    {m n K : ℕ} [NeZero K]
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n)
    (w : UserType K → ℝ) (j : Item n) :
    (∑ u : User m, w (τ.toType u) *
        (((averageTypePolicy τ reps ρ (τ.toType u)) j).toReal)) =
      ∑ u : User m, w (τ.toType u) * (ρ u j).toReal := by
  classical
  calc
    ∑ u : User m, w (τ.toType u) *
        (((averageTypePolicy τ reps ρ (τ.toType u)) j).toReal)
        = ∑ k : UserType K,
            ∑ u ∈ fiberUsers τ k,
              w k * (((averageTypePolicy τ reps ρ k) j).toReal) := by
          rw [← sum_fiberUsers τ (fun u => w (τ.toType u) *
            (((averageTypePolicy τ reps ρ (τ.toType u)) j).toReal))]
          refine Finset.sum_congr rfl ?_
          intro k _
          refine Finset.sum_congr rfl ?_
          intro u hu
          have htype : τ.toType u = k := by
            simpa [fiberUsers] using hu
          rw [htype]
    _ = ∑ k : UserType K,
            ∑ u ∈ fiberUsers τ k,
              w k * (ρ u j).toReal := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [averageTypePolicy_apply_toReal]
          have hcard_nat : (fiberUsers τ k).card ≠ 0 :=
            Finset.card_ne_zero.mpr (fiberUsers_nonempty τ reps k)
          have hcard_real : ((fiberUsers τ k).card : ℝ) ≠ 0 := by
            exact_mod_cast hcard_nat
          calc
            ∑ u ∈ fiberUsers τ k,
                w k * ((∑ u ∈ fiberUsers τ k, (ρ u j).toReal) /
                  ((fiberUsers τ k).card : ℝ))
                = ((fiberUsers τ k).card : ℝ) *
                    (w k * ((∑ u ∈ fiberUsers τ k, (ρ u j).toReal) /
                      ((fiberUsers τ k).card : ℝ))) := by
                    simp [nsmul_eq_mul]
            _ = w k * (∑ u ∈ fiberUsers τ k, (ρ u j).toReal) := by
                    field_simp [hcard_real]
            _ = ∑ u ∈ fiberUsers τ k, w k * (ρ u j).toReal := by
                    rw [Finset.mul_sum]
    _ = ∑ k : UserType K,
            ∑ u ∈ fiberUsers τ k,
              w (τ.toType u) * (ρ u j).toReal := by
          refine Finset.sum_congr rfl ?_
          intro k _
          refine Finset.sum_congr rfl ?_
          intro u hu
          have htype : τ.toType u = k := by
            simpa [fiberUsers] using hu
          rw [htype]
    _ = ∑ u : User m, w (τ.toType u) * (ρ u j).toReal := by
          exact sum_fiberUsers τ (fun u => w (τ.toType u) * (ρ u j).toReal)

/-- Lift the type-averaged policy back to users. -/
noncomputable def symmetrizedPolicy {m n K : ℕ} [NeZero K]
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n) : Policy m n :=
  liftTypePolicy τ (averageTypePolicy τ reps ρ)

theorem symmetrizedPolicy_isTypeSymmetric {m n K : ℕ} [NeZero K]
    (τ : RecommendationModel.UserTypeAssignment m K)
    (reps : TypeRepresentatives τ) (ρ : Policy m n) :
    IsTypeSymmetric τ (symmetrizedPolicy τ reps ρ) := by
  exact liftTypePolicy_isTypeSymmetric τ (averageTypePolicy τ reps ρ)

end UserTypeAssignment

namespace RecommendationModel.SymmetricData

/-- Symmetrize a policy by averaging over identical user-type fibers. -/
noncomputable def symmetrizedPolicy {m n K : ℕ} [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (ρ : Policy m n) : Policy m n :=
  UserTypeAssignment.symmetrizedPolicy S.types reps ρ

theorem symmetrizedPolicy_isTypeSymmetric {m n K : ℕ} [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (ρ : Policy m n) :
    UserTypeAssignment.IsTypeSymmetric S.types (S.symmetrizedPolicy reps ρ) := by
  exact UserTypeAssignment.symmetrizedPolicy_isTypeSymmetric S.types reps ρ

/--
Symmetrizing a policy replaces each user's raw utility by the average raw
utility of the original users in the same type fiber.
-/
theorem rawUserUtility_symmetrizedPolicy_eq_average
    {m n K : ℕ} [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (ρ : Policy m n) (u : User m) :
    RecommendationModel.rawUserUtility S.model (S.symmetrizedPolicy reps ρ) u =
      (∑ u' ∈ UserTypeAssignment.fiberUsers S.types (S.types.toType u),
        RecommendationModel.rawUserUtility S.model ρ u') /
          ((UserTypeAssignment.fiberUsers S.types (S.types.toType u)).card : ℝ) := by
  classical
  let k : UserType K := S.types.toType u
  let fiber : Finset (User m) := UserTypeAssignment.fiberUsers S.types k
  have hfiber_nonempty : fiber.Nonempty := by
    exact UserTypeAssignment.fiberUsers_nonempty S.types reps k
  have hcard_nat : fiber.card ≠ 0 := Finset.card_ne_zero.mpr hfiber_nonempty
  have hcard : (fiber.card : ℝ) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hsame : ∀ u' ∈ fiber, S.model.utility u' = S.model.utility u := by
    intro u' hu'
    have htype : S.types.toType u' = S.types.toType u := by
      have htype' : S.types.toType u' = k := by
        simpa [fiber, UserTypeAssignment.fiberUsers] using hu'
      simpa [k] using htype'
    exact S.agreeWithinTypes u' u htype
  unfold RecommendationModel.rawUserUtility AppliedModelingLib.Policy.agentScore
    AppliedModelingLib.pmfExp
  calc
    ∑ j : Item n, ((S.symmetrizedPolicy reps ρ u) j).toReal * S.model.utility u j
        = ∑ j : Item n,
            (((UserTypeAssignment.averageTypePolicy S.types reps ρ k) j).toReal) *
              S.model.utility u j := by
          rfl
    _ = ∑ j : Item n,
            (((∑ u' ∈ fiber, (ρ u' j).toReal) / (fiber.card : ℝ)) *
              S.model.utility u j) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [UserTypeAssignment.averageTypePolicy_apply_toReal]
    _ = ∑ j : Item n,
            (∑ u' ∈ fiber, (ρ u' j).toReal * S.model.utility u j) /
              (fiber.card : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [← Finset.sum_mul]
          field_simp [hcard]
    _ = (∑ j : Item n,
            ∑ u' ∈ fiber, (ρ u' j).toReal * S.model.utility u j) /
              (fiber.card : ℝ) := by
          rw [Finset.sum_div]
    _ = (∑ u' ∈ fiber,
            ∑ j : Item n, (ρ u' j).toReal * S.model.utility u j) /
              (fiber.card : ℝ) := by
          rw [Finset.sum_comm]
    _ = (∑ u' ∈ fiber,
            ∑ j : Item n, (ρ u' j).toReal * S.model.utility u' j) /
              (fiber.card : ℝ) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro u' hu'
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [congrFun (hsame u' hu') j]
    _ = (∑ u' ∈ UserTypeAssignment.fiberUsers S.types (S.types.toType u),
            ∑ j : Item n, (ρ u' j).toReal * S.model.utility u' j) /
              (((UserTypeAssignment.fiberUsers S.types (S.types.toType u))).card : ℝ) := by
          simp [fiber, k]

/--
After normalizing by the row maximum, symmetrizing also replaces each user's
normalized utility by the average normalized utility in its type fiber.
-/
theorem normalizedUserUtility_symmetrizedPolicy_eq_average
    {m n K : ℕ} [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (hRow : S.model.RowHasPositiveItem)
    (ρ : Policy m n) (u : User m) :
    RecommendationModel.normalizedUserUtility S.model (S.symmetrizedPolicy reps ρ) u =
      (∑ u' ∈ UserTypeAssignment.fiberUsers S.types (S.types.toType u),
        RecommendationModel.normalizedUserUtility S.model ρ u') /
          ((UserTypeAssignment.fiberUsers S.types (S.types.toType u)).card : ℝ) := by
  classical
  let k : UserType K := S.types.toType u
  let fiber : Finset (User m) := UserTypeAssignment.fiberUsers S.types k
  have hfiber_nonempty : fiber.Nonempty := by
    exact UserTypeAssignment.fiberUsers_nonempty S.types reps k
  have hcard_nat : fiber.card ≠ 0 := Finset.card_ne_zero.mpr hfiber_nonempty
  have hcard : (fiber.card : ℝ) ≠ 0 := by
    exact_mod_cast hcard_nat
  have hbest_pos :
      0 < RecommendationModel.bestItemUtility S.model u :=
    RecommendationModel.bestItemUtility_pos_of_rowHasPositiveItem S.model hRow u
  have hbest_ne :
      RecommendationModel.bestItemUtility S.model u ≠ 0 := ne_of_gt hbest_pos
  have hbest_same :
      ∀ u' ∈ fiber,
        RecommendationModel.bestItemUtility S.model u' =
          RecommendationModel.bestItemUtility S.model u := by
    intro u' hu'
    have htype : S.types.toType u' = S.types.toType u := by
      have htype' : S.types.toType u' = k := by
        simpa [fiber, UserTypeAssignment.fiberUsers] using hu'
      simpa [k] using htype'
    exact S.bestItemUtility_eq_of_sameType htype
  unfold RecommendationModel.normalizedUserUtility
  rw [rawUserUtility_symmetrizedPolicy_eq_average
    (S := S) (reps := reps) (ρ := ρ) (u := u)]
  calc
    ((∑ u' ∈ UserTypeAssignment.fiberUsers S.types (S.types.toType u),
          RecommendationModel.rawUserUtility S.model ρ u') /
        ((UserTypeAssignment.fiberUsers S.types (S.types.toType u)).card : ℝ)) /
        RecommendationModel.bestItemUtility S.model u
        = ((∑ u' ∈ fiber,
          RecommendationModel.rawUserUtility S.model ρ u') /
            RecommendationModel.bestItemUtility S.model u) /
          (fiber.card : ℝ) := by
          field_simp [fiber, k, hcard, hbest_ne]
          ring
    _ = (∑ u' ∈ fiber,
          RecommendationModel.rawUserUtility S.model ρ u' /
            RecommendationModel.bestItemUtility S.model u) /
          (fiber.card : ℝ) := by
          rw [Finset.sum_div]
    _ = (∑ u' ∈ fiber,
          RecommendationModel.rawUserUtility S.model ρ u' /
            RecommendationModel.bestItemUtility S.model u') /
          (fiber.card : ℝ) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro u' hu'
          rw [hbest_same u' hu']
    _ = (∑ u' ∈ UserTypeAssignment.fiberUsers S.types (S.types.toType u),
          RecommendationModel.rawUserUtility S.model ρ u' /
            RecommendationModel.bestItemUtility S.model u') /
          ((UserTypeAssignment.fiberUsers S.types (S.types.toType u)).card : ℝ) := by
          simp [fiber, k]

/--
Symmetrizing over identical user-type fibers weakly improves the minimum
normalized user utility. This is the key dominance step behind removing the
user-optimum equality assumption in the LP reduction.
-/
theorem userFairness_le_userFairness_symmetrizedPolicy
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (hRow : S.model.RowHasPositiveItem)
    (ρ : Policy m n) :
    RecommendationModel.userFairness S.model ρ ≤
      RecommendationModel.userFairness S.model (S.symmetrizedPolicy reps ρ) := by
  classical
  unfold RecommendationModel.userFairness AppliedModelingLib.finiteMin
  apply Finset.le_inf'
  intro u _
  rw [normalizedUserUtility_symmetrizedPolicy_eq_average
    (S := S) (reps := reps) (hRow := hRow) (ρ := ρ) (u := u)]
  let fiber : Finset (User m) :=
    UserTypeAssignment.fiberUsers S.types (S.types.toType u)
  let a : ℝ :=
    (Finset.univ : Finset (User m)).inf' Finset.univ_nonempty
      (fun u' => RecommendationModel.normalizedUserUtility S.model ρ u')
  have hfiber_nonempty : fiber.Nonempty := by
    exact UserTypeAssignment.fiberUsers_nonempty S.types reps (S.types.toType u)
  have hcard_pos : 0 < (fiber.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hfiber_nonempty)
  have hterm :
      ∀ u' ∈ fiber,
        a ≤ RecommendationModel.normalizedUserUtility S.model ρ u' := by
    intro u' _hu'
    exact Finset.inf'_le
      (s := (Finset.univ : Finset (User m)))
      (f := fun u' => RecommendationModel.normalizedUserUtility S.model ρ u')
      (by simp)
  have hsum :
      (fiber.card : ℝ) * a ≤
        ∑ u' ∈ fiber, RecommendationModel.normalizedUserUtility S.model ρ u' := by
    calc
      (fiber.card : ℝ) * a = ∑ u' ∈ fiber, a := by
        simp [nsmul_eq_mul, mul_comm]
      _ ≤ ∑ u' ∈ fiber,
          RecommendationModel.normalizedUserUtility S.model ρ u' := by
        exact Finset.sum_le_sum hterm
  change a ≤
    (∑ u' ∈ fiber, RecommendationModel.normalizedUserUtility S.model ρ u') /
      (fiber.card : ℝ)
  rw [le_div_iff₀ hcard_pos]
  simpa [mul_comm] using hsum

/-- Symmetrizing over identical user-type fibers preserves each item's raw utility. -/
theorem rawItemUtility_symmetrizedPolicy_eq {m n K : ℕ} [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (ρ : Policy m n) (j : Item n) :
    RecommendationModel.rawItemUtility S.model (S.symmetrizedPolicy reps ρ) j =
      RecommendationModel.rawItemUtility S.model ρ j := by
  classical
  let w : UserType K → ℝ := fun k => S.model.utility (reps.repr k) j
  have hutil : ∀ u : User m, S.model.utility u j = w (S.types.toType u) := by
    intro u
    unfold w
    have hrow :
        S.model.utility u = S.model.utility (reps.repr (S.types.toType u)) :=
      S.agreeWithinTypes u (reps.repr (S.types.toType u)) (by
        simpa using (reps.repr_spec (S.types.toType u)).symm)
    exact congrFun hrow j
  unfold RecommendationModel.rawItemUtility
  calc
    ∑ u : User m, S.model.utility u j * ((S.symmetrizedPolicy reps ρ u) j).toReal
        = ∑ u : User m, w (S.types.toType u) *
            (((UserTypeAssignment.averageTypePolicy S.types reps ρ
              (S.types.toType u)) j).toReal) := by
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [hutil u]
          rfl
    _ = ∑ u : User m, w (S.types.toType u) * (ρ u j).toReal := by
          exact UserTypeAssignment.sum_weighted_averageTypePolicy_apply_toReal
            S.types reps ρ w j
    _ = ∑ u : User m, S.model.utility u j * (ρ u j).toReal := by
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [hutil u]

/-- Symmetrizing over identical user-type fibers preserves each normalized item utility. -/
theorem normalizedItemUtility_symmetrizedPolicy_eq {m n K : ℕ} [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (ρ : Policy m n) (j : Item n) :
    RecommendationModel.normalizedItemUtility S.model (S.symmetrizedPolicy reps ρ) j =
      RecommendationModel.normalizedItemUtility S.model ρ j := by
  unfold RecommendationModel.normalizedItemUtility
  rw [rawItemUtility_symmetrizedPolicy_eq (S := S) (reps := reps) (ρ := ρ) (j := j)]

/-- Symmetrizing over identical user-type fibers preserves minimum item fairness. -/
theorem itemFairness_symmetrizedPolicy_eq {m n K : ℕ} [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (ρ : Policy m n) :
    RecommendationModel.itemFairness S.model (S.symmetrizedPolicy reps ρ) =
      RecommendationModel.itemFairness S.model ρ := by
  unfold RecommendationModel.itemFairness AppliedModelingLib.finiteMin
  exact Finset.inf'_congr Finset.univ_nonempty rfl
    (by
      intro j _
      exact normalizedItemUtility_symmetrizedPolicy_eq
        (S := S) (reps := reps) (ρ := ρ) (j := j))

/--
The averaging step in Proposition 2, part 1: symmetrizing an optimal policy
over identical user-type fibers preserves feasibility and remains optimal. The
proof follows the paper's argument: item fairness is unchanged, while minimum
normalized user utility weakly improves.
-/
theorem isOptimalAtLevel_symmetrizedPolicy_of_isOptimalAtLevel
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (hRow : S.model.RowHasPositiveItem)
    {γ : ℝ} {ρ : Policy m n}
    (hopt : RecommendationModel.IsOptimalAtLevel S.model γ ρ) :
    RecommendationModel.IsOptimalAtLevel S.model γ
      (S.symmetrizedPolicy reps ρ) := by
  constructor
  · have hfeas := hopt.1
    unfold RecommendationModel.feasibleAtLevel at hfeas ⊢
    rw [itemFairness_symmetrizedPolicy_eq (S := S) (reps := reps) (ρ := ρ)]
    exact hfeas
  · have hsym_feas :
        RecommendationModel.feasibleAtLevel S.model γ
          (S.symmetrizedPolicy reps ρ) := by
      have hfeas := hopt.1
      unfold RecommendationModel.feasibleAtLevel at hfeas ⊢
      rw [itemFairness_symmetrizedPolicy_eq (S := S) (reps := reps) (ρ := ρ)]
      exact hfeas
    have hsym_mem :
        RecommendationModel.userFairness S.model (S.symmetrizedPolicy reps ρ) ∈
          RecommendationModel.attainableUserFairnessAtLevel S.model γ := by
      exact ⟨S.symmetrizedPolicy reps ρ, hsym_feas, rfl⟩
    have hbdd :
        BddAbove (RecommendationModel.attainableUserFairnessAtLevel S.model γ) :=
      RecommendationModel.attainableUserFairnessAtLevel_bddAbove_of_rowHasPositiveItem
        S.model hRow γ
    have hsym_le_opt :
        RecommendationModel.userFairness S.model (S.symmetrizedPolicy reps ρ) ≤
          RecommendationModel.optimalUserFairnessAtLevel S.model γ := by
      unfold RecommendationModel.optimalUserFairnessAtLevel
      exact le_csSup hbdd hsym_mem
    have hopt_le_sym :
        RecommendationModel.optimalUserFairnessAtLevel S.model γ ≤
          RecommendationModel.userFairness S.model (S.symmetrizedPolicy reps ρ) := by
      rw [← hopt.2]
      exact userFairness_le_userFairness_symmetrizedPolicy S reps hRow ρ
    exact le_antisymm hsym_le_opt hopt_le_sym

/--
Proposition 2, part 1, as an existence statement: from any supplied optimum,
averaging over equal utility rows gives an optimal policy in `S_symm`.
-/
theorem exists_typeSymmetric_isOptimalAtLevel_of_isOptimalAtLevel
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (hRow : S.model.RowHasPositiveItem)
    {γ : ℝ} {ρ : Policy m n}
    (hopt : RecommendationModel.IsOptimalAtLevel S.model γ ρ) :
    ∃ ρsym : Policy m n,
      UserTypeAssignment.IsTypeSymmetric S.types ρsym ∧
        RecommendationModel.IsOptimalAtLevel S.model γ ρsym := by
  exact ⟨S.symmetrizedPolicy reps ρ,
    S.symmetrizedPolicy_isTypeSymmetric reps ρ,
    S.isOptimalAtLevel_symmetrizedPolicy_of_isOptimalAtLevel reps hRow hopt⟩

/--
Every item-fairness value attainable by an arbitrary policy is attainable by a
type-symmetric policy, and conversely.
-/
theorem attainableItemFairnessSet_eq_symmetricAttainableItemFairnessSet
    {m n K : ℕ} [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types) :
    RecommendationModel.attainableItemFairnessSet S.model =
      RecommendationModel.symmetricAttainableItemFairnessSet S := by
  ext r
  constructor
  · intro hr
    obtain ⟨ρ, hr⟩ := hr
    refine ⟨S.symmetrizedPolicy reps ρ,
      S.symmetrizedPolicy_isTypeSymmetric reps ρ, ?_⟩
    rw [hr]
    exact (itemFairness_symmetrizedPolicy_eq
      (S := S) (reps := reps) (ρ := ρ)).symm
  · intro hr
    obtain ⟨ρ, _hρ, hr⟩ := hr
    exact ⟨ρ, hr⟩

/-- Original and symmetric optimum item fairness values are equal. -/
theorem optimalItemFairness_eq_symmetricOptimalItemFairness
    {m n K : ℕ} [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types) :
    RecommendationModel.optimalItemFairness S.model =
      RecommendationModel.symmetricOptimalItemFairness S := by
  unfold RecommendationModel.optimalItemFairness
    RecommendationModel.symmetricOptimalItemFairness
  rw [attainableItemFairnessSet_eq_symmetricAttainableItemFairnessSet
    (S := S) (reps := reps)]

end RecommendationModel.SymmetricData

namespace ReductionWitness

/-- Original and reduced optimum item fairness values are equal. -/
theorem optimalItemFairness_eq_reduced
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    RecommendationModel.optimalItemFairness R.data.model =
      TypeWeightedRecommendationModel.optimalItemFairness R.reduced := by
  calc
    RecommendationModel.optimalItemFairness R.data.model
        = RecommendationModel.symmetricOptimalItemFairness R.data := by
          exact R.data.optimalItemFairness_eq_symmetricOptimalItemFairness reps
    _ = TypeWeightedRecommendationModel.optimalItemFairness R.reduced := by
          exact R.symmetricOptimalItemFairness_eq_reduced reps

/--
Original and reduced feasible user-fairness suprema agree once the standard
supremum side conditions are available. The nontrivial proof content is:
original policies can be symmetrized without hurting user fairness or item
feasibility, and symmetric policies descend to the reduced model exactly.
-/
theorem optimalUserFairnessAtLevel_eq_reduced_of_bddAbove_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hOrigBdd :
      BddAbove (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ))
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hRedBdd :
      BddAbove (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ)) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ := by
  classical
  apply le_antisymm
  · unfold RecommendationModel.optimalUserFairnessAtLevel
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
    refine csSup_le hOrigNonempty ?_
    intro r hr
    obtain ⟨ρ, hfeas, hr⟩ := hr
    let ρsym : Policy m n := R.data.symmetrizedPolicy reps ρ
    have hsym :
        UserTypeAssignment.IsTypeSymmetric R.data.types ρsym :=
      R.data.symmetrizedPolicy_isTypeSymmetric reps ρ
    have hfeas_sym :
        RecommendationModel.feasibleAtLevel R.data.model γ ρsym := by
      unfold RecommendationModel.feasibleAtLevel at hfeas ⊢
      rw [R.data.itemFairness_symmetrizedPolicy_eq (reps := reps) (ρ := ρ)]
      exact hfeas
    obtain ⟨ρK, _hlift, hitem, huser⟩ :=
      R.exists_typePolicy_preserving_fairness_of_isTypeSymmetric reps hsym
    have hred_feas :
        TypeWeightedRecommendationModel.feasibleAtLevel R.reduced γ ρK := by
      unfold RecommendationModel.feasibleAtLevel at hfeas_sym
      unfold TypeWeightedRecommendationModel.feasibleAtLevel
      rw [← R.optimalItemFairness_eq_reduced reps]
      rw [← hitem]
      exact hfeas_sym
    have hred_mem :
        TypeWeightedRecommendationModel.typeFairness R.reduced ρK ∈
          TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
            R.reduced γ := by
      exact ⟨ρK, hred_feas, rfl⟩
    have hle_user :
        RecommendationModel.userFairness R.data.model ρ ≤
          TypeWeightedRecommendationModel.typeFairness R.reduced ρK := by
      calc
        RecommendationModel.userFairness R.data.model ρ
            ≤ RecommendationModel.userFairness R.data.model ρsym := by
              exact R.data.userFairness_le_userFairness_symmetrizedPolicy
                reps hRow ρ
        _ = TypeWeightedRecommendationModel.typeFairness R.reduced ρK := huser
    rw [hr]
    exact hle_user.trans (le_csSup hRedBdd hred_mem)
  · unfold RecommendationModel.optimalUserFairnessAtLevel
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
    refine csSup_le hRedNonempty ?_
    intro r hr
    obtain ⟨ρK, hfeas, hr⟩ := hr
    have horig_feas :
        RecommendationModel.feasibleAtLevel R.data.model γ (R.liftedPolicy ρK) := by
      unfold TypeWeightedRecommendationModel.feasibleAtLevel at hfeas
      unfold RecommendationModel.feasibleAtLevel
      rw [R.optimalItemFairness_eq_reduced reps]
      rw [R.itemFairness_liftedPolicy_eq_itemFairness ρK]
      exact hfeas
    have horig_mem :
        RecommendationModel.userFairness R.data.model (R.liftedPolicy ρK) ∈
          RecommendationModel.attainableUserFairnessAtLevel R.data.model γ := by
      exact ⟨R.liftedPolicy ρK, horig_feas, rfl⟩
    have huser :
        RecommendationModel.userFairness R.data.model (R.liftedPolicy ρK) =
          TypeWeightedRecommendationModel.typeFairness R.reduced ρK :=
      R.userFairness_liftedPolicy_eq_typeFairness reps ρK
    rw [hr, ← huser]
    exact le_csSup hOrigBdd horig_mem

/--
Original and reduced feasible user-fairness suprema agree under row positivity
and nonempty feasible value sets. Boundedness follows automatically from the
normalized-utility upper bound `≤ 1`.
-/
theorem optimalUserFairnessAtLevel_eq_reduced_of_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ := by
  have hOrigBdd :
      BddAbove (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ) :=
    RecommendationModel.attainableUserFairnessAtLevel_bddAbove_of_rowHasPositiveItem
      R.data.model hRow γ
  have hRedRow : R.reduced.RowHasPositiveItem :=
    R.reduced_rowHasPositiveItem_of_rowHasPositiveItem reps hRow
  have hRedBdd :
      BddAbove (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ) :=
    TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel_bddAbove_of_rowHasPositiveItem
      R.reduced hRedRow γ
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_bddAbove_nonempty
    reps hRow γ hOrigNonempty hOrigBdd hRedNonempty hRedBdd

/--
For strict item-fairness fractions `γ < 1`, the original/reduced optimal
user-fairness values agree under the paper's positive-utility assumption. The
feasible-value nonemptiness side conditions are discharged by the `sSup`
approximation property for the item-fairness optimum.
-/
theorem optimalUserFairnessAtLevel_eq_reduced_of_gamma_lt_one
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (γ : ℝ) (hγ : γ < 1) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ := by
  have hRow : R.data.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive R.data.model hPos
  have hNonneg : R.data.model.Nonnegative :=
    RecommendationModel.nonnegative_of_positive R.data.model hPos
  have hCol : R.data.model.ColumnHasPositiveDemand :=
    RecommendationModel.columnHasPositiveDemand_of_positive R.data.model hPos
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel
        R.data.model γ).Nonempty :=
    RecommendationModel.attainableUserFairnessAtLevel_nonempty_of_gamma_lt_one
      R.data.model hNonneg hCol hγ
  have hRedWeight : R.reduced.PositiveWeights :=
    R.reduced_positiveWeights_of_representatives reps
  have hRedUtil : R.reduced.PositiveUtilities :=
    R.reduced_positiveUtilities_of_positive reps hPos
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty :=
    TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel_nonempty_of_gamma_lt_one
      R.reduced hRedWeight hRedUtil hγ
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
    reps hRow γ hOrigNonempty hRedNonempty

/--
At the maximal item-fairness boundary `γ = 1`, compactness supplies feasible
and optimal policies on both the original and reduced finite policy simplexes.
-/
theorem optimalUserFairnessAtLevel_eq_reduced_one_of_positive
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced 1 := by
  have hRow : R.data.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive R.data.model hPos
  have hNonneg : R.data.model.Nonnegative :=
    RecommendationModel.nonnegative_of_positive R.data.model hPos
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel
        R.data.model 1).Nonempty :=
    RecommendationModel.attainableUserFairnessAtLevel_one_nonempty_of_nonnegative
      R.data.model hNonneg
  have hRedWeight : R.reduced.PositiveWeights :=
    R.reduced_positiveWeights_of_representatives reps
  have hRedUtil : R.reduced.PositiveUtilities :=
    R.reduced_positiveUtilities_of_positive reps hPos
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced 1).Nonempty :=
    TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel_one_nonempty_of_nonnegative
      R.reduced
      (TypeWeightedRecommendationModel.nonnegativeWeights_of_positiveWeights
        R.reduced hRedWeight)
      (TypeWeightedRecommendationModel.nonnegativeUtilities_of_positiveUtilities
        R.reduced hRedUtil)
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
    reps hRow 1 hOrigNonempty hRedNonempty

/--
If a reduced optimum is supplied, its lifted policy witnesses original
feasibility. Hence reduced-to-original optimality needs no separate feasible-set
nonemptiness assumptions.
-/
theorem isOptimalAtLevel_liftedPolicy_of_reduced_auto_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) (ρ : TypePolicy K n)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ) :
    RecommendationModel.IsOptimalAtLevel R.data.model γ (R.liftedPolicy ρ) := by
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty := by
    exact ⟨TypeWeightedRecommendationModel.typeFairness R.reduced ρ,
      ⟨ρ, hopt.1, rfl⟩⟩
  have hOrigFeas :
      RecommendationModel.feasibleAtLevel R.data.model γ (R.liftedPolicy ρ) := by
    unfold RecommendationModel.feasibleAtLevel
    rw [R.optimalItemFairness_eq_reduced reps]
    rw [R.itemFairness_liftedPolicy_eq_itemFairness ρ]
    exact hopt.1
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty := by
    exact ⟨RecommendationModel.userFairness R.data.model (R.liftedPolicy ρ),
      ⟨R.liftedPolicy ρ, hOrigFeas, rfl⟩⟩
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hRow γ hOrigNonempty hRedNonempty
  exact R.isOptimalAtLevel_liftedPolicy_of_reduced reps γ ρ
    (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
If a symmetric original optimum is supplied, its reduced representative
witnesses reduced feasibility. Hence original-to-reduced optimality needs no
separate feasible-set nonemptiness assumptions.
-/
theorem exists_reducedOptimalAtLevel_of_original_symmetric_optimal_auto_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρK := by
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty := by
    exact ⟨RecommendationModel.userFairness R.data.model ρ,
      ⟨ρ, hopt.1, rfl⟩⟩
  obtain ⟨ρK, hlift, hitem, _huser⟩ :=
    R.exists_typePolicy_preserving_fairness_of_isTypeSymmetric reps hρ
  have hRedFeas :
      TypeWeightedRecommendationModel.feasibleAtLevel R.reduced γ ρK := by
    unfold TypeWeightedRecommendationModel.feasibleAtLevel
    rw [← R.optimalItemFairness_eq_reduced reps]
    rw [← hitem]
    exact hopt.1
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty := by
    exact ⟨TypeWeightedRecommendationModel.typeFairness R.reduced ρK,
      ⟨ρK, hRedFeas, rfl⟩⟩
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hRow γ hOrigNonempty hRedNonempty
  exact R.exists_reducedOptimalAtLevel_of_original_symmetric_optimal
    reps γ hρ (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

end ReductionWitness

end GCG24UserItemFairness
