import AppliedModelingLib.Applications.RecommenderSystems.Policy

open scoped BigOperators
open AppliedModelingLib

namespace GCG24UserItemFairness

/-- Users are indexed by `Fin m`. -/
abbrev User (m : ℕ) := Fin m

/-- Items are indexed by `Fin n`. -/
abbrev Item (n : ℕ) := Fin n

/-- A recommendation policy maps each user to a PMF over items. -/
abbrev Policy (m n : ℕ) := AppliedModelingLib.Policy (User m) (Item n)

/-- The policy that recommends every item uniformly to every user. -/
noncomputable def uniformPolicy {m n : ℕ} [NeZero n] : Policy m n :=
  fun _ => AppliedModelingLib.uniformPMF (Item n)

@[simp] theorem uniformPolicy_apply_toReal {m n : ℕ} [NeZero n]
    (u : User m) (j : Item n) :
    ((uniformPolicy (m := m) (n := n) u) j).toReal = (n : ℝ)⁻¹ := by
  simpa [uniformPolicy, Item] using
    (AppliedModelingLib.uniformPMF_apply_toReal (α := Item n) j)

theorem uniformPolicy_apply_toReal_pos {m n : ℕ} [NeZero n]
    (u : User m) (j : Item n) :
    0 < ((uniformPolicy (m := m) (n := n) u) j).toReal := by
  simpa [uniformPolicy] using
    (AppliedModelingLib.uniformPMF_apply_toReal_pos (α := Item n) j)

/--
A finite recommendation model with shared user/item utility matrix `w`.
This matches the theoretical setup in the user-item fairness paper.
-/
structure RecommendationModel (m n : ℕ) where
  utility : User m → Item n → ℝ

namespace RecommendationModel

/-- Entrywise nonnegativity of the utility matrix. -/
def Nonnegative {m n : ℕ} (W : RecommendationModel m n) : Prop :=
  ∀ u j, 0 ≤ W.utility u j

/-- Entrywise strict positivity of the utility matrix, matching the paper's main model. -/
def Positive {m n : ℕ} (W : RecommendationModel m n) : Prop :=
  ∀ u j, 0 < W.utility u j

/-- Every user has at least one strictly positive item. -/
def RowHasPositiveItem {m n : ℕ} (W : RecommendationModel m n) : Prop :=
  ∀ u, ∃ j, 0 < W.utility u j

/-- Every item has strictly positive total demand under the utility matrix. -/
def ColumnHasPositiveDemand {m n : ℕ} (W : RecommendationModel m n) : Prop :=
  ∀ j, 0 < ∑ u, W.utility u j

theorem nonnegative_of_positive {m n : ℕ}
    (W : RecommendationModel m n) (hPos : W.Positive) :
    W.Nonnegative := by
  intro u j
  exact (hPos u j).le

theorem rowHasPositiveItem_of_positive {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hPos : W.Positive) :
    W.RowHasPositiveItem := by
  intro u
  let j0 : Item n := Classical.choice inferInstance
  exact ⟨j0, hPos u j0⟩

theorem columnHasPositiveDemand_of_positive {m n : ℕ} [NeZero m]
    (W : RecommendationModel m n) (hPos : W.Positive) :
    W.ColumnHasPositiveDemand := by
  intro j
  exact Finset.sum_pos (by
    intro u _hu
    exact hPos u j) Finset.univ_nonempty

/-- Raw user utility `∑_j w_ij ρ_ij`. -/
noncomputable def rawUserUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) : ℝ :=
  AppliedModelingLib.Policy.agentScore ρ W.utility u

/-- The best achievable item for user `u`, i.e. `max_j w_ij`. -/
noncomputable def bestItemUtility {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (u : User m) : ℝ :=
  finiteMax (W.utility u)

/-- Normalized user utility `U_i(ρ)`. -/
noncomputable def normalizedUserUtility {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) : ℝ :=
  rawUserUtility W ρ u / bestItemUtility W u

/-- Minimum normalized user utility `U_min(ρ)`. -/
noncomputable def userFairness {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) : ℝ :=
  finiteMin (normalizedUserUtility W ρ)

/-- Row positivity makes the user-normalization denominator strictly positive. -/
theorem bestItemUtility_pos_of_rowHasPositiveItem {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hRow : W.RowHasPositiveItem) (u : User m) :
    0 < bestItemUtility W u := by
  obtain ⟨j, hj⟩ := hRow u
  exact lt_of_lt_of_le hj (AppliedModelingLib.le_finiteMax (W.utility u) j)

/-- Minimum user fairness is bounded above by every user's normalized utility. -/
theorem userFairness_le_normalizedUserUtility {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) :
    userFairness W ρ ≤ normalizedUserUtility W ρ u := by
  exact AppliedModelingLib.finiteMin_le (normalizedUserUtility W ρ) u

/-- A user's raw expected utility is at most that user's best item utility. -/
theorem rawUserUtility_le_bestItemUtility {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) :
    rawUserUtility W ρ u ≤ bestItemUtility W u := by
  unfold rawUserUtility bestItemUtility AppliedModelingLib.Policy.agentScore
  exact AppliedModelingLib.pmfExp_le_of_forall_le (ρ u) (W.utility u)
    (AppliedModelingLib.finiteMax (W.utility u))
    (fun j => AppliedModelingLib.le_finiteMax (W.utility u) j)

/-- Positive row normalizers make every normalized user utility at most one. -/
theorem normalizedUserUtility_le_one_of_rowHasPositiveItem {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hRow : W.RowHasPositiveItem)
    (ρ : Policy m n) (u : User m) :
    normalizedUserUtility W ρ u ≤ 1 := by
  have hraw := rawUserUtility_le_bestItemUtility W ρ u
  have hbest_pos := bestItemUtility_pos_of_rowHasPositiveItem W hRow u
  unfold normalizedUserUtility
  rw [div_le_iff₀ hbest_pos]
  simpa using hraw

/-- Minimum user fairness is bounded above by one. -/
theorem userFairness_le_one_of_rowHasPositiveItem {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hRow : W.RowHasPositiveItem)
    (ρ : Policy m n) :
    userFairness W ρ ≤ 1 := by
  classical
  let u0 : User m := Classical.choice inferInstance
  exact (userFairness_le_normalizedUserUtility W ρ u0).trans
    (normalizedUserUtility_le_one_of_rowHasPositiveItem W hRow ρ u0)

/-- Raw utility accumulated by item `j` under policy `ρ`. -/
noncomputable def rawItemUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) : ℝ :=
  ∑ u, W.utility u j * (ρ u j).toReal

/-- Normalizer `∑_i w_ij` for item `j`. -/
noncomputable def itemNormalizer {m n : ℕ}
    (W : RecommendationModel m n) (j : Item n) : ℝ :=
  ∑ u, W.utility u j

/-- Normalized item utility `I_j(ρ)`. If the denominator is `0`, we set the value to `0`. -/
noncomputable def normalizedItemUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) : ℝ :=
  let denom := itemNormalizer W j
  if h : denom = 0 then 0 else rawItemUtility W ρ j / denom

/-- Minimum normalized item utility `I_min(ρ)`. -/
noncomputable def itemFairness {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) : ℝ :=
  finiteMin (normalizedItemUtility W ρ)

/-- Nonnegative utilities make every raw item utility nonnegative. -/
theorem rawItemUtility_nonneg_of_nonnegative {m n : ℕ}
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative)
    (ρ : Policy m n) (j : Item n) :
    0 ≤ rawItemUtility W ρ j := by
  unfold rawItemUtility
  exact Finset.sum_nonneg (by
    intro u _hu
    exact mul_nonneg (hNonneg u j) ENNReal.toReal_nonneg)

/-- Nonnegative utilities make every item normalizer nonnegative. -/
theorem itemNormalizer_nonneg_of_nonnegative {m n : ℕ}
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) (j : Item n) :
    0 ≤ itemNormalizer W j := by
  unfold itemNormalizer
  exact Finset.sum_nonneg (by
    intro u _hu
    exact hNonneg u j)

/-- Nonnegative utilities make raw item utility at most its normalizer. -/
theorem rawItemUtility_le_itemNormalizer_of_nonnegative {m n : ℕ}
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative)
    (ρ : Policy m n) (j : Item n) :
    rawItemUtility W ρ j ≤ itemNormalizer W j := by
  unfold rawItemUtility itemNormalizer
  exact Finset.sum_le_sum (by
    intro u _hu
    have hprob : ((ρ u) j).toReal ≤ 1 :=
      AppliedModelingLib.pmf_apply_toReal_le_one (ρ u) j
    calc
      W.utility u j * ((ρ u) j).toReal
          ≤ W.utility u j * 1 := by
            exact mul_le_mul_of_nonneg_left hprob (hNonneg u j)
      _ = W.utility u j := by ring)

/-- Nonnegative utilities make every normalized item utility nonnegative. -/
theorem normalizedItemUtility_nonneg_of_nonnegative {m n : ℕ}
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative)
    (ρ : Policy m n) (j : Item n) :
    0 ≤ normalizedItemUtility W ρ j := by
  unfold normalizedItemUtility
  by_cases hden : itemNormalizer W j = 0
  · simp [hden]
  · simpa [hden] using div_nonneg
      (rawItemUtility_nonneg_of_nonnegative W hNonneg ρ j)
      (itemNormalizer_nonneg_of_nonnegative W hNonneg j)

/-- Nonnegative utilities make every normalized item utility at most one. -/
theorem normalizedItemUtility_le_one_of_nonnegative {m n : ℕ}
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative)
    (ρ : Policy m n) (j : Item n) :
    normalizedItemUtility W ρ j ≤ 1 := by
  unfold normalizedItemUtility
  by_cases hden : itemNormalizer W j = 0
  · simp [hden]
  · have hden_nonneg := itemNormalizer_nonneg_of_nonnegative W hNonneg j
    have hden_pos : 0 < itemNormalizer W j := lt_of_le_of_ne hden_nonneg (Ne.symm hden)
    have hraw_le := rawItemUtility_le_itemNormalizer_of_nonnegative W hNonneg ρ j
    simp [hden]
    rw [div_le_iff₀ hden_pos]
    simpa using hraw_le

/-- Nonnegative utilities make minimum item fairness nonnegative. -/
theorem itemFairness_nonneg_of_nonnegative {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative)
    (ρ : Policy m n) :
  0 ≤ itemFairness W ρ := by
  exact AppliedModelingLib.finiteMin_nonneg (normalizedItemUtility W ρ)
    (normalizedItemUtility_nonneg_of_nonnegative W hNonneg ρ)

/-- Nonnegative utilities make minimum item fairness at most one. -/
theorem itemFairness_le_one_of_nonnegative {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative)
    (ρ : Policy m n) :
    itemFairness W ρ ≤ 1 := by
  let j0 : Item n := Classical.choice inferInstance
  exact (AppliedModelingLib.finiteMin_le (normalizedItemUtility W ρ) j0).trans
    (normalizedItemUtility_le_one_of_nonnegative W hNonneg ρ j0)

/-- Under the uniform policy, item raw utility is a uniform share of the item normalizer. -/
theorem rawItemUtility_uniformPolicy_eq {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (j : Item n) :
    rawItemUtility W (uniformPolicy (m := m) (n := n)) j =
      itemNormalizer W j * (n : ℝ)⁻¹ := by
  unfold rawItemUtility itemNormalizer
  calc
    ∑ u : User m, W.utility u j *
        ((uniformPolicy (m := m) (n := n) u) j).toReal
        = ∑ u : User m, W.utility u j * (n : ℝ)⁻¹ := by
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [uniformPolicy_apply_toReal]
    _ = (∑ u : User m, W.utility u j) * (n : ℝ)⁻¹ := by
          rw [Finset.sum_mul]

/-- Positive item demand gives strictly positive uniform-policy normalized item utility. -/
theorem normalizedItemUtility_uniformPolicy_pos_of_columnHasPositiveDemand
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hCol : W.ColumnHasPositiveDemand)
    (j : Item n) :
    0 < normalizedItemUtility W (uniformPolicy (m := m) (n := n)) j := by
  unfold normalizedItemUtility
  have hden_pos : 0 < itemNormalizer W j := hCol j
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast (NeZero.pos n)
  have hraw_pos :
      0 < rawItemUtility W (uniformPolicy (m := m) (n := n)) j := by
    rw [rawItemUtility_uniformPolicy_eq]
    exact mul_pos hden_pos (inv_pos.mpr hn_pos)
  simp [hden_pos.ne.symm, div_pos hraw_pos hden_pos]

/-- Positive item demand gives strictly positive uniform-policy item fairness. -/
theorem itemFairness_uniformPolicy_pos_of_columnHasPositiveDemand
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hCol : W.ColumnHasPositiveDemand) :
    0 < itemFairness W (uniformPolicy (m := m) (n := n)) := by
  exact AppliedModelingLib.finiteMin_pos
    (normalizedItemUtility W (uniformPolicy (m := m) (n := n)))
    (normalizedItemUtility_uniformPolicy_pos_of_columnHasPositiveDemand W hCol)

/--
The paper's set `S_symm` is built from users sharing utility rows.
This predicate records that utilities are identical within each user type.
-/
structure UserTypeAssignment (m K : ℕ) where
  toType : User m → Fin K

/-- Utilities agree within user types. -/
def UtilitiesAgreeWithinTypes {m n K : ℕ}
    (W : RecommendationModel m n) (τ : UserTypeAssignment m K) : Prop :=
  ∀ u u', τ.toType u = τ.toType u' → W.utility u = W.utility u'

/--
The reverse source convention for a utility-row type partition: equal utility
rows receive the same declared type. Together with `UtilitiesAgreeWithinTypes`,
this says that declared types are exactly the utility-row equivalence classes.
-/
def UserTypeAssignment.UtilityRowsDetermineTypes {m n K : ℕ}
    (W : RecommendationModel m n) (τ : UserTypeAssignment m K) : Prop :=
  ∀ u u', W.utility u = W.utility u' → τ.toType u = τ.toType u'

/-- The source definition of a policy symmetric across equal utility rows. -/
def UtilityRowSymmetric {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) : Prop :=
  ∀ u u', W.utility u = W.utility u' → ρ u = ρ u'

end RecommendationModel
end GCG24UserItemFairness
