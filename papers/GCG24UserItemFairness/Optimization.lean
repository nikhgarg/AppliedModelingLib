import GCG24UserItemFairness.Basic
import Mathlib.Analysis.Convex.StdSimplex

open scoped BigOperators
open AppliedModelingLib

namespace GCG24UserItemFairness

/-- The set of recommendation-model values in which the estimated and true utilities differ. -/
structure EstimatedRecommendationModel (m n : ℕ) where
  trueModel : RecommendationModel m n
  estimatedUtility : User m → Item n → ℝ

namespace EstimatedRecommendationModel

/-- The recommendation model induced by the platform's estimated utility matrix. -/
def estimatedModel {m n : ℕ} (E : EstimatedRecommendationModel m n) : RecommendationModel m n where
  utility := E.estimatedUtility

end EstimatedRecommendationModel

namespace RecommendationModel

/-- Attainable minimum item-fairness values. -/
def attainableItemFairnessSet {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) : Set ℝ :=
  {r | ∃ ρ : Policy m n, r = itemFairness W ρ}

/-- `I^*_min(w)` in the paper. -/
noncomputable def optimalItemFairness {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) : ℝ :=
  sSup (attainableItemFairnessSet W)

/--
The standard LP epigraph form of item-fairness maximization: `λ` is no larger
than every normalized item utility under policy `ρ`.
-/
def itemFairnessLPFeasible {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (ell : ℝ) : Prop :=
  ∀ j : Item n, ell ≤ normalizedItemUtility W ρ j

/--
The equality-form item-fairness LP used in Appendix C, Lemma 2 of the paper:
all normalized item utilities are exactly the objective variable `ell`.
-/
def itemFairnessEqualityLPFeasible {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (ell : ℝ) : Prop :=
  ∀ j : Item n, normalizedItemUtility W ρ j = ell

/-- Feasible objective values in the LP epigraph form of item-fairness maximization. -/
def itemFairnessLPValueSet {m n : ℕ}
    (W : RecommendationModel m n) : Set ℝ :=
  {ell | ∃ ρ : Policy m n, itemFairnessLPFeasible W ρ ell}

/-- Feasible objective values in the paper's equality-form item-fairness LP. -/
def itemFairnessEqualityLPValueSet {m n : ℕ}
    (W : RecommendationModel m n) : Set ℝ :=
  {ell | ∃ ρ : Policy m n, itemFairnessEqualityLPFeasible W ρ ell}

/-- The optimal value of the LP epigraph form of item-fairness maximization. -/
noncomputable def optimalItemFairnessLPValue {m n : ℕ}
    (W : RecommendationModel m n) : ℝ :=
  sSup (itemFairnessLPValueSet W)

/-- The optimal value of the paper's equality-form item-fairness LP. -/
noncomputable def optimalItemFairnessEqualityLPValue {m n : ℕ}
    (W : RecommendationModel m n) : ℝ :=
  sSup (itemFairnessEqualityLPValueSet W)

/-- The LP epigraph constraints are equivalent to `λ ≤ I_min(ρ,w)`. -/
theorem itemFairnessLPFeasible_iff_le_itemFairness
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (ell : ℝ) :
    itemFairnessLPFeasible W ρ ell ↔ ell ≤ itemFairness W ρ := by
  constructor
  · intro h
    unfold itemFairness AppliedModelingLib.finiteMin
    apply Finset.le_inf'
    intro j _hj
    exact h j
  · intro h j
    exact h.trans (AppliedModelingLib.finiteMin_le (normalizedItemUtility W ρ) j)

/-- Equality-form LP feasibility pins `ell` to the policy's item-fairness value. -/
theorem itemFairness_eq_of_itemFairnessEqualityLPFeasible
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (ell : ℝ)
    (h : itemFairnessEqualityLPFeasible W ρ ell) :
    itemFairness W ρ = ell := by
  unfold itemFairness
  exact AppliedModelingLib.finiteMin_eq_of_forall
    (normalizedItemUtility W ρ) ell h

/-- Equality-form LP feasibility implies the epigraph LP constraints. -/
theorem itemFairnessLPFeasible_of_itemFairnessEqualityLPFeasible
    {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (ell : ℝ)
    (h : itemFairnessEqualityLPFeasible W ρ ell) :
    itemFairnessLPFeasible W ρ ell := by
  intro j
  exact le_of_eq (h j).symm

/-- Nonnegative utilities bound every attainable original item-fairness value above by one. -/
theorem attainableItemFairnessSet_bddAbove_of_nonnegative {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    BddAbove (attainableItemFairnessSet W) := by
  refine ⟨1, ?_⟩
  intro r hr
  obtain ⟨ρ, hr⟩ := hr
  rw [hr]
  exact itemFairness_le_one_of_nonnegative W hNonneg ρ

/-- The LP epigraph value set is nonempty, witnessed by any policy's own minimum item utility. -/
theorem itemFairnessLPValueSet_nonempty {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) :
    (itemFairnessLPValueSet W).Nonempty := by
  refine ⟨itemFairness W (uniformPolicy (m := m) (n := n)), ?_⟩
  exact ⟨uniformPolicy (m := m) (n := n),
    (itemFairnessLPFeasible_iff_le_itemFairness
      W (uniformPolicy (m := m) (n := n))
      (itemFairness W (uniformPolicy (m := m) (n := n)))).mpr le_rfl⟩

/-- Nonnegative utilities bound the LP epigraph objective values above by one. -/
theorem itemFairnessLPValueSet_bddAbove_of_nonnegative
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    BddAbove (itemFairnessLPValueSet W) := by
  refine ⟨1, ?_⟩
  intro ell hell
  obtain ⟨ρ, hρ⟩ := hell
  have hle_item :
      ell ≤ itemFairness W ρ :=
    (itemFairnessLPFeasible_iff_le_itemFairness W ρ ell).mp hρ
  exact hle_item.trans (itemFairness_le_one_of_nonnegative W hNonneg ρ)

/-- Nonnegative utilities bound equality-form LP objective values above by one. -/
theorem itemFairnessEqualityLPValueSet_bddAbove_of_nonnegative
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    BddAbove (itemFairnessEqualityLPValueSet W) := by
  refine ⟨1, ?_⟩
  intro ell hell
  obtain ⟨ρ, hρ⟩ := hell
  have hitem : itemFairness W ρ = ell :=
    itemFairness_eq_of_itemFairnessEqualityLPFeasible W ρ ell hρ
  rw [← hitem]
  exact itemFairness_le_one_of_nonnegative W hNonneg ρ

/--
Appendix C, Lemma 2 in max-min LP epigraph form: maximizing `λ` subject to
`λ ≤ I_j(ρ,w)` for every item has the same value as `I^*_min(w)`.
-/
theorem optimalItemFairnessLPValue_eq_optimalItemFairness_of_nonnegative
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    optimalItemFairnessLPValue W = optimalItemFairness W := by
  have hLPNonempty := itemFairnessLPValueSet_nonempty W
  have hLPBdd := itemFairnessLPValueSet_bddAbove_of_nonnegative W hNonneg
  have hItemNonempty : (attainableItemFairnessSet W).Nonempty := by
    exact ⟨itemFairness W (uniformPolicy (m := m) (n := n)),
      ⟨uniformPolicy (m := m) (n := n), rfl⟩⟩
  have hItemBdd := attainableItemFairnessSet_bddAbove_of_nonnegative W hNonneg
  apply le_antisymm
  · unfold optimalItemFairnessLPValue
    refine csSup_le hLPNonempty ?_
    intro ell hell
    obtain ⟨ρ, hρ⟩ := hell
    have hle_item :
        ell ≤ itemFairness W ρ :=
      (itemFairnessLPFeasible_iff_le_itemFairness W ρ ell).mp hρ
    have hitem_mem :
        itemFairness W ρ ∈ attainableItemFairnessSet W := by
      exact ⟨ρ, rfl⟩
    exact hle_item.trans (le_csSup hItemBdd hitem_mem)
  · unfold optimalItemFairness
    refine csSup_le hItemNonempty ?_
    intro r hr
    obtain ⟨ρ, hr⟩ := hr
    rw [hr]
    have hlp_mem :
        itemFairness W ρ ∈ itemFairnessLPValueSet W := by
      exact ⟨ρ,
        (itemFairnessLPFeasible_iff_le_itemFairness
          W ρ (itemFairness W ρ)).mpr le_rfl⟩
    exact le_csSup hLPBdd hlp_mem

/--
The paper's local optimality condition for Appendix C, Lemma 2: there is no
policy that strictly improves every normalized item utility.
-/
def ItemFairnessNoStrictPointwiseImprovement {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) : Prop :=
  ¬ ∃ ρ' : Policy m n,
    ∀ j : Item n,
      normalizedItemUtility W ρ j < normalizedItemUtility W ρ' j

/--
The remaining constructive step in Appendix C, Lemma 2's source proof: if an
optimal policy has a slack item, one can perturb probability mass away from
that slack item and strictly improve the minimum item-fairness objective. The
slack item's own value may decrease; the paper only needs it to stay above the
old minimum.
-/
def ItemFairnessSlackImprovementProperty {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) : Prop :=
  ∀ j : Item n,
    itemFairness W ρ < normalizedItemUtility W ρ j →
      ∃ ρ' : Policy m n,
        itemFairness W ρ < itemFairness W ρ'

/-- A nonzero policy coordinate has strictly positive real probability. -/
theorem policy_toReal_pos_of_ne_zero {m n : ℕ}
    (ρ : Policy m n) {u : User m} {j : Item n}
    (h : ρ u j ≠ 0) :
    0 < (ρ u j).toReal := by
  have htoReal_ne : (ρ u j).toReal ≠ 0 := by
    intro hzero
    have hzero_or_top :=
      (ENNReal.toReal_eq_zero_iff (ρ u j)).mp hzero
    rcases hzero_or_top with hzero_enn | htop
    · exact h hzero_enn
    · exact (ρ u).apply_ne_top j htop
  exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm htoReal_ne)

/-- Positive item fairness implies every item is recommended by some user. -/
theorem item_coverage_of_itemFairness_pos {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n)
    (hpos : 0 < itemFairness W ρ) :
    ∀ j : Item n, ∃ u : User m, ρ u j ≠ 0 := by
  classical
  intro j
  by_contra hnone
  have hall_zero : ∀ u : User m, ρ u j = 0 := by
    intro u
    exact Classical.byContradiction (by
      intro hu
      exact hnone ⟨u, hu⟩)
  have hraw_zero : rawItemUtility W ρ j = 0 := by
    unfold rawItemUtility
    simp [hall_zero]
  have hnorm_zero : normalizedItemUtility W ρ j = 0 := by
    unfold normalizedItemUtility
    rw [hraw_zero]
    by_cases hden : itemNormalizer W j = 0
    · simp [hden]
    · simp [hden]
  have hle := AppliedModelingLib.finiteMin_le (normalizedItemUtility W ρ) j
  have hnorm_pos : 0 < normalizedItemUtility W ρ j := lt_of_lt_of_le hpos hle
  rw [hnorm_zero] at hnorm_pos
  exact (lt_irrefl (0 : ℝ)) hnorm_pos

/-- Items attaining the current minimum normalized item utility. -/
noncomputable def itemFairnessMinimizerSet {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) : Finset (Item n) :=
  Finset.univ.filter
    (fun j : Item n => normalizedItemUtility W ρ j = itemFairness W ρ)

theorem mem_itemFairnessMinimizerSet_iff {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) :
    j ∈ itemFairnessMinimizerSet W ρ ↔
      normalizedItemUtility W ρ j = itemFairness W ρ := by
  classical
  simp [itemFairnessMinimizerSet]

/-- The finite minimum is attained by at least one item. -/
theorem itemFairnessMinimizerSet_nonempty {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) :
    (itemFairnessMinimizerSet W ρ).Nonempty := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Item n,
      itemFairness W ρ = normalizedItemUtility W ρ j := by
    unfold itemFairness AppliedModelingLib.finiteMin
    obtain ⟨j, _hjmem, hj⟩ :=
      Finset.exists_mem_eq_inf'
        (s := (Finset.univ : Finset (Item n)))
        (H := Finset.univ_nonempty)
        (f := normalizedItemUtility W ρ)
    exact ⟨j, hj⟩
  exact ⟨j, (mem_itemFairnessMinimizerSet_iff W ρ j).mpr hj.symm⟩

theorem not_mem_itemFairnessMinimizerSet_of_itemFairness_lt
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) {j : Item n}
    (h : itemFairness W ρ < normalizedItemUtility W ρ j) :
    j ∉ itemFairnessMinimizerSet W ρ := by
  classical
  intro hj
  have heq :=
    (mem_itemFairnessMinimizerSet_iff W ρ j).mp hj
  linarith

/-- Build a finite item PMF from a nonnegative real vector with total mass one. -/
noncomputable def pmfOfRealItemVector {n : ℕ}
    (x : Item n → ℝ)
    (hnonneg : ∀ j : Item n, 0 ≤ x j)
    (hsum : (∑ j : Item n, x j) = 1) : PMF (Item n) :=
  PMF.ofFintype (fun j : Item n => ENNReal.ofReal (x j)) (by
    calc
      (∑ j : Item n, ENNReal.ofReal (x j))
          = ENNReal.ofReal (∑ j : Item n, x j) := by
            rw [← ENNReal.ofReal_sum_of_nonneg
              (s := Finset.univ) (f := x)]
            simp [hnonneg]
      _ = 1 := by
            simp [hsum])

@[simp] theorem pmfOfRealItemVector_apply_toReal {n : ℕ}
    (x : Item n → ℝ)
    (hnonneg : ∀ j : Item n, 0 ≤ x j)
    (hsum : (∑ j : Item n, x j) = 1)
    (j : Item n) :
    ((pmfOfRealItemVector x hnonneg hsum) j).toReal = x j := by
  unfold pmfOfRealItemVector
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (hnonneg j)

/--
A real-vector presentation of policies as one standard simplex row per user.
This is only used to prove finite-dimensional optimum attainment for Lemma 2.
-/
abbrev PolicySimplexVector (m n : ℕ) :=
  User m → stdSimplex ℝ (Item n)

/-- Convert a real simplex vector back to the paper's `PMF`-valued policy type. -/
noncomputable def policyOfSimplexVector {m n : ℕ}
    (x : PolicySimplexVector m n) : Policy m n :=
  fun u =>
    pmfOfRealItemVector
      ((x u : stdSimplex ℝ (Item n)) : Item n → ℝ)
      (x u).2.1
      (x u).2.2

@[simp] theorem policyOfSimplexVector_apply_toReal {m n : ℕ}
    (x : PolicySimplexVector m n) (u : User m) (j : Item n) :
    ((policyOfSimplexVector x u) j).toReal =
      ((x u : stdSimplex ℝ (Item n)) : Item n → ℝ) j := by
  simp [policyOfSimplexVector]

/-- Convert a `PMF`-valued policy into its real simplex-vector presentation. -/
noncomputable def simplexVectorOfPolicy {m n : ℕ}
    (ρ : Policy m n) : PolicySimplexVector m n :=
  fun u =>
    ⟨fun j => (ρ u j).toReal,
      ⟨fun j => ENNReal.toReal_nonneg,
        AppliedModelingLib.pmfToRealSum (ρ u)⟩⟩

/-- Raw item utility evaluated on the real simplex-vector presentation. -/
noncomputable def rawItemUtilityVector {m n : ℕ}
    (W : RecommendationModel m n) (x : PolicySimplexVector m n)
    (j : Item n) : ℝ :=
  ∑ u : User m,
    W.utility u j * ((x u : stdSimplex ℝ (Item n)) : Item n → ℝ) j

/-- Normalized item utility evaluated on the real simplex-vector presentation. -/
noncomputable def normalizedItemUtilityVector {m n : ℕ}
    (W : RecommendationModel m n) (x : PolicySimplexVector m n)
    (j : Item n) : ℝ :=
  let denom := itemNormalizer W j
  if h : denom = 0 then 0 else rawItemUtilityVector W x j / denom

/-- Minimum item fairness evaluated on the real simplex-vector presentation. -/
noncomputable def itemFairnessVector {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (x : PolicySimplexVector m n) : ℝ :=
  AppliedModelingLib.finiteMin (normalizedItemUtilityVector W x)

theorem rawItemUtility_policyOfSimplexVector_eq {m n : ℕ}
    (W : RecommendationModel m n) (x : PolicySimplexVector m n)
    (j : Item n) :
    rawItemUtility W (policyOfSimplexVector x) j =
      rawItemUtilityVector W x j := by
  simp [rawItemUtility, rawItemUtilityVector]

theorem normalizedItemUtility_policyOfSimplexVector_eq {m n : ℕ}
    (W : RecommendationModel m n) (x : PolicySimplexVector m n)
    (j : Item n) :
    normalizedItemUtility W (policyOfSimplexVector x) j =
      normalizedItemUtilityVector W x j := by
  unfold normalizedItemUtility normalizedItemUtilityVector
  rw [rawItemUtility_policyOfSimplexVector_eq]

theorem itemFairness_policyOfSimplexVector_eq {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (x : PolicySimplexVector m n) :
    itemFairness W (policyOfSimplexVector x) =
      itemFairnessVector W x := by
  unfold itemFairness itemFairnessVector
  apply congrArg
  funext j
  exact normalizedItemUtility_policyOfSimplexVector_eq W x j

theorem rawItemUtilityVector_simplexVectorOfPolicy_eq {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) :
    rawItemUtilityVector W (simplexVectorOfPolicy ρ) j =
      rawItemUtility W ρ j := by
  unfold rawItemUtilityVector rawItemUtility simplexVectorOfPolicy
  rfl

theorem normalizedItemUtilityVector_simplexVectorOfPolicy_eq {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) :
    normalizedItemUtilityVector W (simplexVectorOfPolicy ρ) j =
      normalizedItemUtility W ρ j := by
  unfold normalizedItemUtilityVector normalizedItemUtility
  rw [rawItemUtilityVector_simplexVectorOfPolicy_eq]

theorem itemFairnessVector_simplexVectorOfPolicy_eq {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) :
    itemFairnessVector W (simplexVectorOfPolicy ρ) =
      itemFairness W ρ := by
  unfold itemFairnessVector itemFairness
  apply congrArg
  funext j
  exact normalizedItemUtilityVector_simplexVectorOfPolicy_eq W ρ j

theorem rawItemUtilityVector_continuous {m n : ℕ}
    (W : RecommendationModel m n) (j : Item n) :
    Continuous (fun x : PolicySimplexVector m n =>
      rawItemUtilityVector W x j) := by
  unfold rawItemUtilityVector
  apply continuous_finset_sum
  intro u _hu
  exact continuous_const.mul
    ((continuous_apply j).comp
      (continuous_subtype_val.comp (continuous_apply u)))

theorem normalizedItemUtilityVector_continuous {m n : ℕ}
    (W : RecommendationModel m n) (j : Item n) :
    Continuous (fun x : PolicySimplexVector m n =>
      normalizedItemUtilityVector W x j) := by
  unfold normalizedItemUtilityVector
  by_cases hden : itemNormalizer W j = 0
  · simpa [hden] using (continuous_const : Continuous
      (fun _ : PolicySimplexVector m n => (0 : ℝ)))
  · simpa [hden] using
      (rawItemUtilityVector_continuous W j).div_const (itemNormalizer W j)

theorem itemFairnessVector_continuous {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) :
    Continuous (fun x : PolicySimplexVector m n =>
      itemFairnessVector W x) := by
  have hcont : ∀ j : Item n,
      Continuous (fun x : PolicySimplexVector m n =>
        normalizedItemUtilityVector W x j) :=
    fun j => normalizedItemUtilityVector_continuous W j
  unfold itemFairnessVector AppliedModelingLib.finiteMin
  fun_prop

/-- Raw user utility evaluated on the real simplex-vector presentation. -/
noncomputable def rawUserUtilityVector {m n : ℕ}
    (W : RecommendationModel m n) (x : PolicySimplexVector m n)
    (u : User m) : ℝ :=
  ∑ j : Item n,
    ((x u : stdSimplex ℝ (Item n)) : Item n → ℝ) j * W.utility u j

/-- Normalized user utility evaluated on the real simplex-vector presentation. -/
noncomputable def normalizedUserUtilityVector {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (x : PolicySimplexVector m n)
    (u : User m) : ℝ :=
  rawUserUtilityVector W x u / bestItemUtility W u

/-- Minimum user fairness evaluated on the real simplex-vector presentation. -/
noncomputable def userFairnessVector {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (x : PolicySimplexVector m n) : ℝ :=
  AppliedModelingLib.finiteMin (normalizedUserUtilityVector W x)

theorem rawUserUtility_policyOfSimplexVector_eq {m n : ℕ}
    (W : RecommendationModel m n) (x : PolicySimplexVector m n)
    (u : User m) :
    rawUserUtility W (policyOfSimplexVector x) u =
      rawUserUtilityVector W x u := by
  unfold rawUserUtility rawUserUtilityVector AppliedModelingLib.Policy.agentScore
    AppliedModelingLib.pmfExp
  simp [mul_comm]

theorem normalizedUserUtility_policyOfSimplexVector_eq {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (x : PolicySimplexVector m n)
    (u : User m) :
    normalizedUserUtility W (policyOfSimplexVector x) u =
      normalizedUserUtilityVector W x u := by
  unfold normalizedUserUtility normalizedUserUtilityVector
  rw [rawUserUtility_policyOfSimplexVector_eq]

theorem userFairness_policyOfSimplexVector_eq {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (x : PolicySimplexVector m n) :
    userFairness W (policyOfSimplexVector x) =
      userFairnessVector W x := by
  unfold userFairness userFairnessVector
  apply congrArg
  funext u
  exact normalizedUserUtility_policyOfSimplexVector_eq W x u

theorem rawUserUtilityVector_simplexVectorOfPolicy_eq {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) :
    rawUserUtilityVector W (simplexVectorOfPolicy ρ) u =
      rawUserUtility W ρ u := by
  unfold rawUserUtilityVector rawUserUtility simplexVectorOfPolicy
    AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp
  change (∑ x : Item n, ((ρ u) x).toReal * W.utility u x) =
    ∑ x : Item n, ((ρ u) x).toReal * W.utility u x
  rfl

theorem normalizedUserUtilityVector_simplexVectorOfPolicy_eq
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) :
    normalizedUserUtilityVector W (simplexVectorOfPolicy ρ) u =
      normalizedUserUtility W ρ u := by
  unfold normalizedUserUtilityVector normalizedUserUtility
  rw [rawUserUtilityVector_simplexVectorOfPolicy_eq]

theorem userFairnessVector_simplexVectorOfPolicy_eq
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) :
    userFairnessVector W (simplexVectorOfPolicy ρ) =
      userFairness W ρ := by
  unfold userFairnessVector userFairness
  apply congrArg
  funext u
  exact normalizedUserUtilityVector_simplexVectorOfPolicy_eq W ρ u

theorem rawUserUtilityVector_continuous {m n : ℕ}
    (W : RecommendationModel m n) (u : User m) :
    Continuous (fun x : PolicySimplexVector m n =>
      rawUserUtilityVector W x u) := by
  unfold rawUserUtilityVector
  apply continuous_finset_sum
  intro j _hj
  have hrow : Continuous (fun x : PolicySimplexVector m n => x u) :=
    continuous_apply u
  have hcoord : Continuous (fun x : PolicySimplexVector m n =>
      ((x u : stdSimplex ℝ (Item n)) : Item n → ℝ) j) :=
    (continuous_apply j).comp (continuous_subtype_val.comp hrow)
  exact hcoord.mul continuous_const

theorem normalizedUserUtilityVector_continuous {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (u : User m) :
    Continuous (fun x : PolicySimplexVector m n =>
      normalizedUserUtilityVector W x u) := by
  unfold normalizedUserUtilityVector
  exact (rawUserUtilityVector_continuous W u).div_const _

theorem userFairnessVector_continuous {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) :
    Continuous (fun x : PolicySimplexVector m n =>
      userFairnessVector W x) := by
  have hcont : ∀ u : User m,
      Continuous (fun x : PolicySimplexVector m n =>
        normalizedUserUtilityVector W x u) :=
    fun u => normalizedUserUtilityVector_continuous W u
  unfold userFairnessVector AppliedModelingLib.finiteMin
  fun_prop

/--
The finite policy simplex is compact, so the original item-fairness objective
attains its supremum. This supplies the optimum-existence step used implicitly
in Appendix C, Lemma 2.
-/
theorem optimalItemFairness_attained_of_nonnegative
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    ∃ ρ : Policy m n, itemFairness W ρ = optimalItemFairness W := by
  classical
  let X := PolicySimplexVector m n
  have hcompact : IsCompact (Set.univ : Set X) := isCompact_univ
  have hnonempty : (Set.univ : Set X).Nonempty := Set.univ_nonempty
  have hcont : ContinuousOn (fun x : X => itemFairnessVector W x) Set.univ :=
    (itemFairnessVector_continuous W).continuousOn
  rcases hcompact.exists_isMaxOn hnonempty hcont with
    ⟨xopt, _hxmem, hxmax⟩
  let ρopt : Policy m n := policyOfSimplexVector xopt
  refine ⟨ρopt, ?_⟩
  have hρopt_eq :
      itemFairness W ρopt = itemFairnessVector W xopt := by
    dsimp [ρopt]
    exact itemFairness_policyOfSimplexVector_eq W xopt
  have hset_nonempty : (attainableItemFairnessSet W).Nonempty := by
    exact ⟨itemFairness W ρopt, ⟨ρopt, rfl⟩⟩
  have hopt_le : optimalItemFairness W ≤ itemFairness W ρopt := by
    unfold optimalItemFairness
    refine csSup_le hset_nonempty ?_
    intro r hr
    obtain ⟨ρ, rfl⟩ := hr
    have hxle :
        itemFairnessVector W (simplexVectorOfPolicy ρ) ≤
          itemFairnessVector W xopt :=
      (isMaxOn_iff.mp hxmax) (simplexVectorOfPolicy ρ) (Set.mem_univ _)
    rw [itemFairnessVector_simplexVectorOfPolicy_eq] at hxle
    rw [← hρopt_eq] at hxle
    exact hxle
  have hle_opt : itemFairness W ρopt ≤ optimalItemFairness W := by
    exact le_csSup
      (attainableItemFairnessSet_bddAbove_of_nonnegative W hNonneg)
      ⟨ρopt, rfl⟩
  exact le_antisymm hle_opt hopt_le

/--
The single-row vector used in Appendix C, Lemma 2's perturbation: subtract
`eps * targets.card` from the slack source item and add `eps` to each target.
-/
noncomputable def shiftedRowVector {m n : ℕ}
    (ρ : Policy m n) (u : User m) (source : Item n)
    (targets : Finset (Item n)) (eps : ℝ) : Item n → ℝ :=
  fun j =>
    (ρ u j).toReal -
      (if j = source then eps * (targets.card : ℝ) else 0) +
      (if j ∈ targets then eps else 0)

/-- The row perturbation preserves total probability mass. -/
theorem shiftedRowVector_sum_eq_one {m n : ℕ}
    (ρ : Policy m n) (u : User m) (source : Item n)
    (targets : Finset (Item n)) (eps : ℝ) :
    (∑ j : Item n, shiftedRowVector ρ u source targets eps j) = 1 := by
  classical
  unfold shiftedRowVector
  have hpmf : (∑ j : Item n, (ρ u j).toReal) = 1 :=
    AppliedModelingLib.pmfToRealSum (ρ u)
  have hsource :
      (∑ j : Item n, (if j = source then eps * (targets.card : ℝ) else 0)) =
        eps * (targets.card : ℝ) := by
    simpa using
      (Finset.sum_ite_eq' source
        (fun _ : Item n => eps * (targets.card : ℝ)))
  have htargets :
      (∑ j : Item n, (if j ∈ targets then eps else 0)) =
        (targets.card : ℝ) * eps := by
    calc
      (∑ j : Item n, (if j ∈ targets then eps else 0))
          = ∑ j ∈ targets, eps := by
              simp [Finset.sum_ite_mem]
      _ = (targets.card : ℝ) * eps := by
              simp [Finset.sum_const, nsmul_eq_mul]
  calc
    (∑ j : Item n,
        ((ρ u j).toReal -
          (if j = source then eps * (targets.card : ℝ) else 0) +
          (if j ∈ targets then eps else 0)))
        =
          (∑ j : Item n, (ρ u j).toReal) -
            (∑ j : Item n,
              (if j = source then eps * (targets.card : ℝ) else 0)) +
            (∑ j : Item n, (if j ∈ targets then eps else 0)) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = 1 := by
          rw [hpmf, hsource, htargets]
          ring

/-- The row perturbation is coordinatewise nonnegative when epsilon is small enough. -/
theorem shiftedRowVector_nonneg {m n : ℕ}
    (ρ : Policy m n) (u : User m) (source : Item n)
    (targets : Finset (Item n)) {eps : ℝ}
    (hsource_not_targets : source ∉ targets)
    (heps_nonneg : 0 ≤ eps)
    (hsource_mass : eps * (targets.card : ℝ) ≤ (ρ u source).toReal) :
    ∀ j : Item n, 0 ≤ shiftedRowVector ρ u source targets eps j := by
  classical
  intro j
  by_cases hjs : j = source
  · subst j
    simp [shiftedRowVector, hsource_not_targets]
    linarith
  · by_cases hjt : j ∈ targets
    · have hbase : 0 ≤ (ρ u j).toReal := ENNReal.toReal_nonneg
      simp [shiftedRowVector, hjs, hjt]
      linarith
    · simp [shiftedRowVector, hjs, hjt, ENNReal.toReal_nonneg]

/-- Apply the Appendix C Lemma 2 row perturbation to a single user row. -/
noncomputable def policyShiftRowToTargets {m n : ℕ}
    (ρ : Policy m n) (u : User m) (source : Item n)
    (targets : Finset (Item n)) (eps : ℝ)
    (hnonneg : ∀ j : Item n, 0 ≤ shiftedRowVector ρ u source targets eps j)
    (hsum : (∑ j : Item n, shiftedRowVector ρ u source targets eps j) = 1) :
    Policy m n :=
  fun u' =>
    if u' = u then
      pmfOfRealItemVector (shiftedRowVector ρ u source targets eps) hnonneg hsum
    else
      ρ u'

@[simp] theorem policyShiftRowToTargets_self_toReal {m n : ℕ}
    (ρ : Policy m n) (u : User m) (source : Item n)
    (targets : Finset (Item n)) (eps : ℝ)
    (hnonneg : ∀ j : Item n, 0 ≤ shiftedRowVector ρ u source targets eps j)
    (hsum : (∑ j : Item n, shiftedRowVector ρ u source targets eps j) = 1)
    (j : Item n) :
    ((policyShiftRowToTargets ρ u source targets eps hnonneg hsum u) j).toReal =
      shiftedRowVector ρ u source targets eps j := by
  simp [policyShiftRowToTargets]

@[simp] theorem policyShiftRowToTargets_other_toReal {m n : ℕ}
    (ρ : Policy m n) {u u' : User m} (source : Item n)
    (targets : Finset (Item n)) (eps : ℝ)
    (hnonneg : ∀ j : Item n, 0 ≤ shiftedRowVector ρ u source targets eps j)
    (hsum : (∑ j : Item n, shiftedRowVector ρ u source targets eps j) = 1)
    (hne : u' ≠ u) (j : Item n) :
    ((policyShiftRowToTargets ρ u source targets eps hnonneg hsum u') j).toReal =
      (ρ u' j).toReal := by
  simp [policyShiftRowToTargets, hne]

/-- Raw item utility after a single-row perturbation changes only by that row's delta. -/
theorem rawItemUtility_policyShiftRowToTargets_eq {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n)
    (u : User m) (source j : Item n)
    (targets : Finset (Item n)) (eps : ℝ)
    (hnonneg : ∀ l : Item n, 0 ≤ shiftedRowVector ρ u source targets eps l)
    (hsum : (∑ l : Item n, shiftedRowVector ρ u source targets eps l) = 1) :
    rawItemUtility W
        (policyShiftRowToTargets ρ u source targets eps hnonneg hsum) j =
      rawItemUtility W ρ j +
        W.utility u j *
          (shiftedRowVector ρ u source targets eps j - (ρ u j).toReal) := by
  classical
  unfold rawItemUtility
  calc
    (∑ u' : User m,
        W.utility u' j *
          ((policyShiftRowToTargets ρ u source targets eps hnonneg hsum u') j).toReal)
        =
      ∑ u' : User m,
        (W.utility u' j * (ρ u' j).toReal +
          if u' = u then
            W.utility u j *
              (shiftedRowVector ρ u source targets eps j - (ρ u j).toReal)
          else 0) := by
          refine Finset.sum_congr rfl ?_
          intro u' _hu'
          by_cases hu' : u' = u
          · subst u'
            simp
            ring
          · simp [policyShiftRowToTargets, hu']
    _ =
      (∑ u' : User m, W.utility u' j * (ρ u' j).toReal) +
        ∑ u' : User m,
          (if u' = u then
            W.utility u j *
              (shiftedRowVector ρ u source targets eps j - (ρ u j).toReal)
          else 0) := by
          rw [Finset.sum_add_distrib]
    _ =
      (∑ u' : User m, W.utility u' j * (ρ u' j).toReal) +
        W.utility u j *
          (shiftedRowVector ρ u source targets eps j - (ρ u j).toReal) := by
          rw [Finset.sum_ite_eq']
          simp

/--
The normalized value of the source item after the Appendix C Lemma 2 row
perturbation. The source item can go down, but by an explicitly controlled
amount.
-/
theorem normalizedItemUtility_policyShiftRowToTargets_source_eq {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n)
    (u : User m) (source : Item n)
    (targets : Finset (Item n)) (eps : ℝ)
    (hnonneg : ∀ l : Item n, 0 ≤ shiftedRowVector ρ u source targets eps l)
    (hsum : (∑ l : Item n, shiftedRowVector ρ u source targets eps l) = 1)
    (hsource_not_targets : source ∉ targets)
    (hden : 0 < itemNormalizer W source) :
    normalizedItemUtility W
        (policyShiftRowToTargets ρ u source targets eps hnonneg hsum) source =
      normalizedItemUtility W ρ source -
        W.utility u source * eps * (targets.card : ℝ) /
          itemNormalizer W source := by
  classical
  have hraw :=
    rawItemUtility_policyShiftRowToTargets_eq
      W ρ u source source targets eps hnonneg hsum
  unfold normalizedItemUtility
  simp [hden.ne', hraw, shiftedRowVector, hsource_not_targets]
  ring

/--
Each target minimizer's normalized value increases by the transferred row mass
weighted by that user's value for the target item.
-/
theorem normalizedItemUtility_policyShiftRowToTargets_target_eq {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n)
    (u : User m) (source j : Item n)
    (targets : Finset (Item n)) (eps : ℝ)
    (hnonneg : ∀ l : Item n, 0 ≤ shiftedRowVector ρ u source targets eps l)
    (hsum : (∑ l : Item n, shiftedRowVector ρ u source targets eps l) = 1)
    (hsource_not_targets : source ∉ targets)
    (hj : j ∈ targets)
    (hden : 0 < itemNormalizer W j) :
    normalizedItemUtility W
        (policyShiftRowToTargets ρ u source targets eps hnonneg hsum) j =
      normalizedItemUtility W ρ j +
        W.utility u j * eps / itemNormalizer W j := by
  classical
  have hjs : j ≠ source := by
    intro h
    subst j
    exact hsource_not_targets hj
  have hraw :=
    rawItemUtility_policyShiftRowToTargets_eq
      W ρ u source j targets eps hnonneg hsum
  unfold normalizedItemUtility
  simp [hden.ne', hraw, shiftedRowVector, hjs, hj]
  ring

/--
Items that are neither the source nor a target minimizer keep the same
normalized value under the one-row perturbation.
-/
theorem normalizedItemUtility_policyShiftRowToTargets_unchanged {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n)
    (u : User m) (source j : Item n)
    (targets : Finset (Item n)) (eps : ℝ)
    (hnonneg : ∀ l : Item n, 0 ≤ shiftedRowVector ρ u source targets eps l)
    (hsum : (∑ l : Item n, shiftedRowVector ρ u source targets eps l) = 1)
    (hjs : j ≠ source)
    (hj : j ∉ targets)
    (hden : 0 < itemNormalizer W j) :
    normalizedItemUtility W
        (policyShiftRowToTargets ρ u source targets eps hnonneg hsum) j =
      normalizedItemUtility W ρ j := by
  classical
  have hraw :=
    rawItemUtility_policyShiftRowToTargets_eq
      W ρ u source j targets eps hnonneg hsum
  unfold normalizedItemUtility
  simp [hden.ne', hraw, shiftedRowVector, hjs, hj]

/--
If `eps` is small enough that the source item remains above the old minimum,
then transferring `eps` from a slack source item to every current minimizer
strictly improves the item-fairness objective.
-/
theorem itemFairness_lt_policyShiftRowToTargets_of_eps
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPos : W.Positive)
    (ρ : Policy m n) (u : User m) (source : Item n)
    {eps : ℝ}
    (heps_pos : 0 < eps)
    (hsource_mass :
      eps * ((itemFairnessMinimizerSet W ρ).card : ℝ) ≤
        (ρ u source).toReal)
    (hsource_slack :
      itemFairness W ρ < normalizedItemUtility W ρ source)
    (hsource_after :
      itemFairness W ρ <
        normalizedItemUtility W ρ source -
          W.utility u source * eps *
            ((itemFairnessMinimizerSet W ρ).card : ℝ) /
            itemNormalizer W source) :
    ∃ ρ' : Policy m n, itemFairness W ρ < itemFairness W ρ' := by
  classical
  let targets := itemFairnessMinimizerSet W ρ
  have hsource_not_targets : source ∉ targets := by
    dsimp [targets]
    exact not_mem_itemFairnessMinimizerSet_of_itemFairness_lt
      W ρ hsource_slack
  have hnonneg : ∀ l : Item n,
      0 ≤ shiftedRowVector ρ u source targets eps l := by
    exact shiftedRowVector_nonneg ρ u source targets hsource_not_targets
      heps_pos.le hsource_mass
  have hsum :
      (∑ l : Item n, shiftedRowVector ρ u source targets eps l) = 1 :=
    shiftedRowVector_sum_eq_one ρ u source targets eps
  let ρ' : Policy m n :=
    policyShiftRowToTargets ρ u source targets eps hnonneg hsum
  refine ⟨ρ', ?_⟩
  change itemFairness W ρ <
    AppliedModelingLib.finiteMin (normalizedItemUtility W ρ')
  unfold AppliedModelingLib.finiteMin
  rw [Finset.lt_inf'_iff]
  intro j _hj
  have hden : 0 < itemNormalizer W j :=
    W.columnHasPositiveDemand_of_positive hPos j
  by_cases hjs : j = source
  · subst j
    dsimp [ρ', targets] at hsource_after ⊢
    rw [normalizedItemUtility_policyShiftRowToTargets_source_eq
      W ρ u source (itemFairnessMinimizerSet W ρ) eps
      hnonneg hsum hsource_not_targets
      (W.columnHasPositiveDemand_of_positive hPos source)]
    exact hsource_after
  · by_cases hjt : j ∈ targets
    · have hj_min :
        normalizedItemUtility W ρ j = itemFairness W ρ := by
          dsimp [targets] at hjt
          exact (mem_itemFairnessMinimizerSet_iff W ρ j).mp hjt
      have hinc_pos :
          0 < W.utility u j * eps / itemNormalizer W j := by
        exact div_pos (mul_pos (hPos u j) heps_pos) hden
      dsimp [ρ', targets]
      rw [normalizedItemUtility_policyShiftRowToTargets_target_eq
        W ρ u source j (itemFairnessMinimizerSet W ρ) eps
        hnonneg hsum hsource_not_targets hjt hden]
      rw [hj_min]
      linarith
    · have hj_not_min :
        normalizedItemUtility W ρ j ≠ itemFairness W ρ := by
          intro hmin
          exact hjt ((mem_itemFairnessMinimizerSet_iff W ρ j).mpr hmin)
      have hj_strict :
          itemFairness W ρ < normalizedItemUtility W ρ j := by
        have hle :
            itemFairness W ρ ≤ normalizedItemUtility W ρ j :=
          AppliedModelingLib.finiteMin_le (normalizedItemUtility W ρ) j
        exact lt_of_le_of_ne hle (Ne.symm hj_not_min)
      dsimp [ρ', targets]
      rw [normalizedItemUtility_policyShiftRowToTargets_unchanged
        W ρ u source j (itemFairnessMinimizerSet W ρ) eps
        hnonneg hsum hjs hjt hden]
      exact hj_strict

/--
The constructive perturbation step in Appendix C, Lemma 2: under strictly
positive utilities, any attained optimal policy with a slack item can transfer
a sufficiently small amount of probability mass from that slack item to all
currently worst-off items and strictly raise `I_min`.
-/
theorem itemFairnessSlackImprovementProperty_of_positive_of_optimal
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPos : W.Positive)
    {ρ : Policy m n}
    (hopt : itemFairness W ρ = optimalItemFairness W) :
    ItemFairnessSlackImprovementProperty W ρ := by
  classical
  intro source hsource_slack
  let targets := itemFairnessMinimizerSet W ρ
  have htargets_nonempty : targets.Nonempty := by
    dsimp [targets]
    exact itemFairnessMinimizerSet_nonempty W ρ
  have hcard_pos_nat : 0 < targets.card :=
    Finset.card_pos.mpr htargets_nonempty
  let C : ℝ := (targets.card : ℝ)
  have hC_pos : 0 < C := by
    dsimp [C]
    exact_mod_cast hcard_pos_nat
  have hC_nonneg : 0 ≤ C := hC_pos.le
  have hopt_pos : 0 < optimalItemFairness W := by
    have hbdd :=
      attainableItemFairnessSet_bddAbove_of_nonnegative W
        (W.nonnegative_of_positive hPos)
    have hmem :
        itemFairness W (uniformPolicy (m := m) (n := n)) ∈
          attainableItemFairnessSet W := by
      exact ⟨uniformPolicy (m := m) (n := n), rfl⟩
    exact lt_of_lt_of_le
      (itemFairness_uniformPolicy_pos_of_columnHasPositiveDemand W
        (W.columnHasPositiveDemand_of_positive hPos))
      (le_csSup hbdd hmem)
  have hρ_pos : 0 < itemFairness W ρ := by
    rw [hopt]
    exact hopt_pos
  obtain ⟨u, hu_ne⟩ :=
    item_coverage_of_itemFairness_pos W ρ hρ_pos source
  have hmass_pos : 0 < (ρ u source).toReal :=
    policy_toReal_pos_of_ne_zero ρ hu_ne
  let gap : ℝ := normalizedItemUtility W ρ source - itemFairness W ρ
  have hgap_pos : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr hsource_slack
  let denom : ℝ := itemNormalizer W source
  have hden_pos : 0 < denom := by
    dsimp [denom]
    exact W.columnHasPositiveDemand_of_positive hPos source
  let coeff : ℝ := W.utility u source * C / denom
  have hcoeff_nonneg : 0 ≤ coeff := by
    dsimp [coeff]
    exact div_nonneg (mul_nonneg (hPos u source).le hC_nonneg) hden_pos.le
  let eps : ℝ :=
    min ((ρ u source).toReal / (2 * C))
      (gap / (2 * (coeff + 1)))
  have htwoC_pos : 0 < 2 * C := by nlinarith
  have hcoeffD_pos : 0 < 2 * (coeff + 1) := by nlinarith
  have heps_pos : 0 < eps := by
    dsimp [eps]
    exact lt_min (div_pos hmass_pos htwoC_pos)
      (div_pos hgap_pos hcoeffD_pos)
  have heps_le_mass_div :
      eps ≤ (ρ u source).toReal / (2 * C) := by
    dsimp [eps]
    exact min_le_left _ _
  have heps_twoC_le_mass :
      eps * (2 * C) ≤ (ρ u source).toReal := by
    exact (le_div_iff₀ htwoC_pos).mp heps_le_mass_div
  have hsource_mass :
      eps * ((itemFairnessMinimizerSet W ρ).card : ℝ) ≤
        (ρ u source).toReal := by
    have hC_le_twoC : C ≤ 2 * C := by nlinarith
    have hepsC_le_epsTwoC : eps * C ≤ eps * (2 * C) :=
      mul_le_mul_of_nonneg_left hC_le_twoC heps_pos.le
    have hepsC_le_mass : eps * C ≤ (ρ u source).toReal :=
      hepsC_le_epsTwoC.trans heps_twoC_le_mass
    simpa [C, targets] using hepsC_le_mass
  have heps_le_gap_div :
      eps ≤ gap / (2 * (coeff + 1)) := by
    dsimp [eps]
    exact min_le_right _ _
  have heps_D_le_gap :
      eps * (2 * (coeff + 1)) ≤ gap := by
    exact (le_div_iff₀ hcoeffD_pos).mp heps_le_gap_div
  have hcoeff_lt_D : coeff < 2 * (coeff + 1) := by
    nlinarith
  have hloss_lt_gap : coeff * eps < gap := by
    have hlt_big : coeff * eps < (2 * (coeff + 1)) * eps :=
      mul_lt_mul_of_pos_right hcoeff_lt_D heps_pos
    have hbig_le_gap : (2 * (coeff + 1)) * eps ≤ gap := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using heps_D_le_gap
    exact hlt_big.trans_le hbig_le_gap
  have hloss_expr :
      W.utility u source * eps * C / denom = coeff * eps := by
    dsimp [coeff]
    ring
  have hsource_after :
      itemFairness W ρ <
        normalizedItemUtility W ρ source -
          W.utility u source * eps *
            ((itemFairnessMinimizerSet W ρ).card : ℝ) /
            itemNormalizer W source := by
    have hloss_lt_gap' :
        W.utility u source * eps * C / denom < gap := by
      rw [hloss_expr]
      exact hloss_lt_gap
    dsimp [gap, denom] at hloss_lt_gap'
    simpa [C, targets] using (by linarith : itemFairness W ρ <
      normalizedItemUtility W ρ source -
        W.utility u source * eps *
          ((itemFairnessMinimizerSet W ρ).card : ℝ) /
          itemNormalizer W source)
  exact itemFairness_lt_policyShiftRowToTargets_of_eps
    W hPos ρ u source heps_pos hsource_mass hsource_slack hsource_after

/--
An attained item-fairness optimum admits no policy that strictly improves every
item value. This is the generic optimality half of Appendix C, Lemma 2's
contradiction argument.
-/
theorem itemFairness_noStrictPointwiseImprovement_of_optimal
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative)
    {ρ : Policy m n}
    (hopt : itemFairness W ρ = optimalItemFairness W) :
    ItemFairnessNoStrictPointwiseImprovement W ρ := by
  classical
  intro hbad
  obtain ⟨ρ', hstrict⟩ := hbad
  let delta : ℝ :=
    AppliedModelingLib.finiteMin (fun j : Item n =>
      normalizedItemUtility W ρ' j - normalizedItemUtility W ρ j)
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    apply AppliedModelingLib.finiteMin_pos
    intro j
    exact sub_pos.mpr (hstrict j)
  have hle_all :
      itemFairness W ρ + delta ≤ itemFairness W ρ' := by
    unfold itemFairness
    apply AppliedModelingLib.le_finiteMin
    intro j
    have hdelta_le :
        delta ≤ normalizedItemUtility W ρ' j -
          normalizedItemUtility W ρ j := by
      dsimp [delta]
      exact AppliedModelingLib.finiteMin_le
        (fun l : Item n =>
          normalizedItemUtility W ρ' l - normalizedItemUtility W ρ l) j
    have hmin_le :
        AppliedModelingLib.finiteMin (normalizedItemUtility W ρ) ≤
          normalizedItemUtility W ρ j :=
      AppliedModelingLib.finiteMin_le (normalizedItemUtility W ρ) j
    linarith
  have hbdd := attainableItemFairnessSet_bddAbove_of_nonnegative W hNonneg
  have hρ'_mem :
      itemFairness W ρ' ∈ attainableItemFairnessSet W := by
    exact ⟨ρ', rfl⟩
  have hρ'_le_opt : itemFairness W ρ' ≤ optimalItemFairness W := by
    exact le_csSup hbdd hρ'_mem
  rw [hopt] at hle_all
  linarith

/--
If every slack item admits the paper's objective-improving perturbation, then an
attained optimum equalizes all normalized item utilities.
-/
theorem itemFairnessEqualityLPFeasible_of_optimal_of_slackImprovement
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative)
    {ρ : Policy m n}
    (hopt : itemFairness W ρ = optimalItemFairness W)
    (hslack : ItemFairnessSlackImprovementProperty W ρ) :
    itemFairnessEqualityLPFeasible W ρ (itemFairness W ρ) := by
  classical
  intro j
  apply le_antisymm
  · by_contra hnot
    have hmin_le :
        itemFairness W ρ ≤ normalizedItemUtility W ρ j :=
      AppliedModelingLib.finiteMin_le (normalizedItemUtility W ρ) j
    have hlt : itemFairness W ρ < normalizedItemUtility W ρ j :=
      lt_of_le_not_ge hmin_le hnot
    obtain ⟨ρ', himprove⟩ := hslack j hlt
    have hbdd := attainableItemFairnessSet_bddAbove_of_nonnegative W hNonneg
    have hρ'_le_opt : itemFairness W ρ' ≤ optimalItemFairness W := by
      exact le_csSup hbdd ⟨ρ', rfl⟩
    rw [hopt] at himprove
    exact not_lt_of_ge hρ'_le_opt himprove
  · exact AppliedModelingLib.finiteMin_le (normalizedItemUtility W ρ) j

/--
Appendix C, Lemma 2 in the paper's equality-form LP interface, conditional
only on the source proof's perturbation step for attained optima.
-/
theorem optimalItemFairnessEqualityLPValue_eq_optimalItemFairness_of_nonnegative_of_attained_of_slackImprovement
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative)
    (hatt : ∃ ρ : Policy m n, itemFairness W ρ = optimalItemFairness W)
    (hslack :
      ∀ ρ : Policy m n,
        itemFairness W ρ = optimalItemFairness W →
          ItemFairnessSlackImprovementProperty W ρ) :
    optimalItemFairnessEqualityLPValue W = optimalItemFairness W := by
  obtain ⟨ρopt, hρopt⟩ := hatt
  have heq :
      itemFairnessEqualityLPFeasible W ρopt
        (itemFairness W ρopt) :=
    itemFairnessEqualityLPFeasible_of_optimal_of_slackImprovement
      W hNonneg hρopt (hslack ρopt hρopt)
  have hEqNonempty :
      (itemFairnessEqualityLPValueSet W).Nonempty := by
    exact ⟨itemFairness W ρopt, ⟨ρopt, heq⟩⟩
  have hEqBdd :=
    itemFairnessEqualityLPValueSet_bddAbove_of_nonnegative W hNonneg
  have hItemBdd := attainableItemFairnessSet_bddAbove_of_nonnegative W hNonneg
  apply le_antisymm
  · unfold optimalItemFairnessEqualityLPValue
    refine csSup_le hEqNonempty ?_
    intro ell hell
    obtain ⟨ρ, hρ⟩ := hell
    have hitem_eq :
        itemFairness W ρ = ell :=
      itemFairness_eq_of_itemFairnessEqualityLPFeasible W ρ ell hρ
    rw [← hitem_eq]
    exact le_csSup hItemBdd ⟨ρ, rfl⟩
  · rw [← hρopt]
    unfold optimalItemFairnessEqualityLPValue
    exact le_csSup hEqBdd ⟨ρopt, heq⟩

/--
Appendix C, Lemma 2 in the paper's equality-form LP interface, with the
paper's slack-transfer perturbation discharged under strictly positive
utilities. The only remaining analytic side condition is attainment of the
finite-dimensional item-fairness optimum.
-/
theorem optimalItemFairnessEqualityLPValue_eq_optimalItemFairness_of_positive_of_attained
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPos : W.Positive)
    (hatt : ∃ ρ : Policy m n, itemFairness W ρ = optimalItemFairness W) :
    optimalItemFairnessEqualityLPValue W = optimalItemFairness W := by
  exact
    optimalItemFairnessEqualityLPValue_eq_optimalItemFairness_of_nonnegative_of_attained_of_slackImprovement
      W (W.nonnegative_of_positive hPos) hatt
      (fun ρ hρ =>
        itemFairnessSlackImprovementProperty_of_positive_of_optimal W hPos hρ)

/--
Appendix C, Lemma 2 in the paper's equality-form LP interface under strictly
positive utilities, with both finite optimum attainment and the source
slack-transfer perturbation discharged.
-/
theorem optimalItemFairnessEqualityLPValue_eq_optimalItemFairness_of_positive
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPos : W.Positive) :
    optimalItemFairnessEqualityLPValue W = optimalItemFairness W := by
  exact
    optimalItemFairnessEqualityLPValue_eq_optimalItemFairness_of_positive_of_attained
      W hPos
      (optimalItemFairness_attained_of_nonnegative W
        (W.nonnegative_of_positive hPos))

/--
Positive item demand and nonnegative utilities make the original optimal
item-fairness value strictly positive.
-/
theorem optimalItemFairness_pos_of_columnHasPositiveDemand
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hCol : W.ColumnHasPositiveDemand) :
    0 < optimalItemFairness W := by
  have hbdd := attainableItemFairnessSet_bddAbove_of_nonnegative W hNonneg
  have hmem :
      itemFairness W (uniformPolicy (m := m) (n := n)) ∈
        attainableItemFairnessSet W := by
    exact ⟨uniformPolicy (m := m) (n := n), rfl⟩
  exact lt_of_lt_of_le
    (itemFairness_uniformPolicy_pos_of_columnHasPositiveDemand W hCol)
    (le_csSup hbdd hmem)

/-- Feasibility for the paper's `γ`-constrained problem. -/
def feasibleAtLevel {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) (ρ : Policy m n) : Prop :=
  γ * optimalItemFairness W ≤ itemFairness W ρ

/-- Attainable minimum user-fairness values subject to the item constraint. -/
def attainableUserFairnessAtLevel {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : Set ℝ :=
  {r | ∃ ρ : Policy m n, feasibleAtLevel W γ ρ ∧ r = userFairness W ρ}

/-- Feasible user-fairness values are bounded above by one under positive row normalizers. -/
theorem attainableUserFairnessAtLevel_bddAbove_of_rowHasPositiveItem
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hRow : W.RowHasPositiveItem) (γ : ℝ) :
    BddAbove (attainableUserFairnessAtLevel W γ) := by
  refine ⟨1, ?_⟩
  intro r hr
  obtain ⟨ρ, _hfeas, hr⟩ := hr
  rw [hr]
  exact userFairness_le_one_of_rowHasPositiveItem W hRow ρ

/-- A canonical policy used only to witness nonempty finite feasible sets. -/
noncomputable def defaultPolicy {m n : ℕ} [NeZero n] : Policy m n :=
  AppliedModelingLib.Policy.pure
    (fun _ : User m => Classical.choice (inferInstance : Nonempty (Item n)))

/-- The deterministic policy that recommends each user an item attaining their finite row maximum. -/
noncomputable def bestItemPolicy {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) : Policy m n :=
  AppliedModelingLib.Policy.pure
    (fun u : User m =>
      Classical.choose (AppliedModelingLib.exists_finiteMax_eq (W.utility u)))

theorem bestItemPolicy_utility_eq_bestItemUtility
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (u : User m) :
    W.utility u
        (Classical.choose (AppliedModelingLib.exists_finiteMax_eq (W.utility u))) =
      bestItemUtility W u := by
  exact (Classical.choose_spec
    (AppliedModelingLib.exists_finiteMax_eq (W.utility u))).symm

/-- The best-item policy gives each user their row maximum in raw utility. -/
theorem rawUserUtility_bestItemPolicy_eq_bestItemUtility
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (u : User m) :
    rawUserUtility W (bestItemPolicy W) u = bestItemUtility W u := by
  unfold rawUserUtility bestItemPolicy
  rw [AppliedModelingLib.Policy.agentScore_pure]
  exact bestItemPolicy_utility_eq_bestItemUtility W u

/-- Under positive row normalizers, the best-item policy gives every user normalized utility `1`. -/
theorem normalizedUserUtility_bestItemPolicy_eq_one
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hRow : W.RowHasPositiveItem) (u : User m) :
    normalizedUserUtility W (bestItemPolicy W) u = 1 := by
  unfold normalizedUserUtility
  rw [rawUserUtility_bestItemPolicy_eq_bestItemUtility]
  exact div_self (ne_of_gt (bestItemUtility_pos_of_rowHasPositiveItem W hRow u))

/--
Without item-fairness constraints, the deterministic best-item policy gives
minimum normalized user utility `1`.
-/
theorem userFairness_bestItemPolicy_eq_one
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hRow : W.RowHasPositiveItem) :
    userFairness W (bestItemPolicy W) = 1 := by
  unfold userFairness
  exact AppliedModelingLib.finiteMin_eq_of_forall
    (normalizedUserUtility W (bestItemPolicy W)) 1
    (normalizedUserUtility_bestItemPolicy_eq_one W hRow)

/-- At baseline `γ = 0`, every policy is feasible under nonnegative utilities. -/
theorem feasibleAtLevel_zero_of_nonnegative {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative)
    (ρ : Policy m n) :
    feasibleAtLevel W 0 ρ := by
  unfold feasibleAtLevel
  simpa using itemFairness_nonneg_of_nonnegative W hNonneg ρ

/--
The baseline feasible value set is nonempty under nonnegative utilities. This
avoids a compactness argument for the paper's unconstrained item-fairness
baseline.
-/
theorem attainableUserFairnessAtLevel_zero_nonempty_of_nonnegative
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    (attainableUserFairnessAtLevel W 0).Nonempty := by
  refine ⟨userFairness W (defaultPolicy (m := m) (n := n)), ?_⟩
  exact ⟨defaultPolicy (m := m) (n := n),
    feasibleAtLevel_zero_of_nonnegative W hNonneg _, rfl⟩

/--
For any strict fraction `γ < 1`, positive item demand makes the original
`γ`-constrained feasible-value set nonempty. This uses the defining
approximation property of `sSup`; exact attainment is only needed at `γ = 1`.
-/
theorem attainableUserFairnessAtLevel_nonempty_of_gamma_lt_one
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hCol : W.ColumnHasPositiveDemand)
    {γ : ℝ} (hγ : γ < 1) :
    (attainableUserFairnessAtLevel W γ).Nonempty := by
  have hopt_pos := optimalItemFairness_pos_of_columnHasPositiveDemand W hNonneg hCol
  have hlt :
      γ * optimalItemFairness W < optimalItemFairness W := by
    simpa using (mul_lt_mul_of_pos_right hγ hopt_pos)
  have hitem_nonempty : (attainableItemFairnessSet W).Nonempty := by
    exact ⟨itemFairness W (uniformPolicy (m := m) (n := n)),
      ⟨uniformPolicy (m := m) (n := n), rfl⟩⟩
  obtain ⟨r, hrmem, hrgt⟩ :=
    exists_lt_of_lt_csSup hitem_nonempty hlt
  obtain ⟨ρ, hr⟩ := hrmem
  refine ⟨userFairness W ρ, ?_⟩
  refine ⟨ρ, ?_, rfl⟩
  unfold feasibleAtLevel
  rw [← hr]
  exact le_of_lt hrgt

/--
At the maximal boundary `γ = 1`, compactness of the item-fairness simplex
supplies a policy attaining `I^*_{\min}(w)`, hence a feasible user-fairness
value.
-/
theorem attainableUserFairnessAtLevel_one_nonempty_of_nonnegative
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    (attainableUserFairnessAtLevel W 1).Nonempty := by
  obtain ⟨ρ, hρ⟩ := optimalItemFairness_attained_of_nonnegative W hNonneg
  refine ⟨userFairness W ρ, ?_⟩
  refine ⟨ρ, ?_, rfl⟩
  unfold feasibleAtLevel
  rw [one_mul, hρ]

/-- `U^*_min(γ, w)` in the paper. -/
noncomputable def optimalUserFairnessAtLevel {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : ℝ :=
  sSup (attainableUserFairnessAtLevel W γ)

/--
The paper's unconstrained user-fairness optimum:
`U^*_min(w) = 1` when utilities are nonnegative and every user has a positive
row normalizer.
-/
theorem optimalUserFairnessAtLevel_zero_eq_one
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem) :
    optimalUserFairnessAtLevel W 0 = 1 := by
  have hset_nonempty :
      (attainableUserFairnessAtLevel W 0).Nonempty :=
    attainableUserFairnessAtLevel_zero_nonempty_of_nonnegative W hNonneg
  have hbdd :
      BddAbove (attainableUserFairnessAtLevel W 0) :=
    attainableUserFairnessAtLevel_bddAbove_of_rowHasPositiveItem W hRow 0
  have hbest_mem :
      userFairness W (bestItemPolicy W) ∈
        attainableUserFairnessAtLevel W 0 := by
    exact ⟨bestItemPolicy W, feasibleAtLevel_zero_of_nonnegative W hNonneg _, rfl⟩
  apply le_antisymm
  · unfold optimalUserFairnessAtLevel
    refine csSup_le hset_nonempty ?_
    intro r hr
    obtain ⟨ρ, _hfeas, hr⟩ := hr
    rw [hr]
    exact userFairness_le_one_of_rowHasPositiveItem W hRow ρ
  · rw [← userFairness_bestItemPolicy_eq_one W hRow]
    unfold optimalUserFairnessAtLevel
    exact le_csSup hbdd hbest_mem

/-- A policy solves the paper's optimization problem at fairness level `γ`. -/
def IsOptimalAtLevel {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) (ρ : Policy m n) : Prop :=
  feasibleAtLevel W γ ρ ∧ userFairness W ρ = optimalUserFairnessAtLevel W γ

/-- The vector-domain feasible set for the paper's `γ`-constrained problem. -/
def feasibleSimplexVectorAtLevel {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) :
    Set (PolicySimplexVector m n) :=
  {x | γ * optimalItemFairness W ≤ itemFairnessVector W x}

/--
Whenever the `γ`-constrained feasible-value set is nonempty, compactness of the
finite policy simplex gives an actual policy attaining
`U^*_{\min}(γ,w)`.
-/
theorem exists_isOptimalAtLevel_of_attainableUserFairnessAtLevel_nonempty
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ)
    (hFeasNonempty : (attainableUserFairnessAtLevel W γ).Nonempty) :
    ∃ ρ : Policy m n, IsOptimalAtLevel W γ ρ := by
  classical
  let S : Set (PolicySimplexVector m n) :=
    feasibleSimplexVectorAtLevel W γ
  have hS_closed : IsClosed S := by
    dsimp [S, feasibleSimplexVectorAtLevel]
    exact isClosed_le continuous_const (itemFairnessVector_continuous W)
  have hS_compact : IsCompact S :=
    isCompact_univ.of_isClosed_subset hS_closed (Set.subset_univ _)
  have hS_nonempty : S.Nonempty := by
    obtain ⟨_r, ρ, hfeas, _hr⟩ := hFeasNonempty
    refine ⟨simplexVectorOfPolicy ρ, ?_⟩
    dsimp [S, feasibleSimplexVectorAtLevel]
    rw [itemFairnessVector_simplexVectorOfPolicy_eq]
    exact hfeas
  rcases hS_compact.exists_isMaxOn hS_nonempty
      ((userFairnessVector_continuous W).continuousOn) with
    ⟨xopt, hxoptS, hxmax⟩
  let ρopt : Policy m n := policyOfSimplexVector xopt
  have hρopt_item :
      itemFairness W ρopt = itemFairnessVector W xopt := by
    dsimp [ρopt]
    exact itemFairness_policyOfSimplexVector_eq W xopt
  have hρopt_user :
      userFairness W ρopt = userFairnessVector W xopt := by
    dsimp [ρopt]
    exact userFairness_policyOfSimplexVector_eq W xopt
  have hρopt_feas : feasibleAtLevel W γ ρopt := by
    unfold feasibleAtLevel
    dsimp [S, feasibleSimplexVectorAtLevel] at hxoptS
    rw [hρopt_item]
    exact hxoptS
  have hρopt_mem :
      userFairness W ρopt ∈ attainableUserFairnessAtLevel W γ := by
    exact ⟨ρopt, hρopt_feas, rfl⟩
  have hupper :
      ∀ r ∈ attainableUserFairnessAtLevel W γ,
        r ≤ userFairness W ρopt := by
    intro r hr
    obtain ⟨ρ, hfeas, hr⟩ := hr
    have hxρS : simplexVectorOfPolicy ρ ∈ S := by
      dsimp [S, feasibleSimplexVectorAtLevel]
      rw [itemFairnessVector_simplexVectorOfPolicy_eq]
      exact hfeas
    have hxle :
        userFairnessVector W (simplexVectorOfPolicy ρ) ≤
          userFairnessVector W xopt :=
      (isMaxOn_iff.mp hxmax) (simplexVectorOfPolicy ρ) hxρS
    rw [userFairnessVector_simplexVectorOfPolicy_eq] at hxle
    rw [← hρopt_user] at hxle
    rw [hr]
    exact hxle
  have hbdd : BddAbove (attainableUserFairnessAtLevel W γ) :=
    ⟨userFairness W ρopt, hupper⟩
  have hopt_le :
      optimalUserFairnessAtLevel W γ ≤ userFairness W ρopt := by
    unfold optimalUserFairnessAtLevel
    exact csSup_le hFeasNonempty hupper
  have hle_opt :
      userFairness W ρopt ≤ optimalUserFairnessAtLevel W γ := by
    unfold optimalUserFairnessAtLevel
    exact le_csSup hbdd hρopt_mem
  exact ⟨ρopt, hρopt_feas, le_antisymm hle_opt hopt_le⟩

/-- The maximal-boundary user-fairness problem has an optimal policy. -/
theorem exists_isOptimalAtLevel_one_of_nonnegative
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    ∃ ρ : Policy m n, IsOptimalAtLevel W 1 ρ :=
  exists_isOptimalAtLevel_of_attainableUserFairnessAtLevel_nonempty
    W 1 (attainableUserFairnessAtLevel_one_nonempty_of_nonnegative W hNonneg)

/-- The paper's price of fairness, generalized to an arbitrary `γ`. -/
noncomputable def priceOfFairnessAt {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : ℝ :=
  let base := optimalUserFairnessAtLevel W 0
  if h : base = 0 then 0 else (base - optimalUserFairnessAtLevel W γ) / base

/--
When the unconstrained optimum is `1`, the price of fairness is just
`1 - U^*_min(γ,w)`.
-/
theorem priceOfFairnessAt_eq_one_sub_optimalUserFairnessAtLevel
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem) (γ : ℝ) :
    priceOfFairnessAt W γ = 1 - optimalUserFairnessAtLevel W γ := by
  unfold priceOfFairnessAt
  rw [optimalUserFairnessAtLevel_zero_eq_one W hNonneg hRow]
  simp

/-- The price of maximal item fairness on user fairness. -/
noncomputable def priceOfFairness {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) : ℝ :=
  priceOfFairnessAt W 1

/--
Paper-facing specialization of the price-of-fairness simplification at maximal
item fairness.
-/
theorem priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem) :
    priceOfFairness W = 1 - optimalUserFairnessAtLevel W 1 := by
  exact priceOfFairnessAt_eq_one_sub_optimalUserFairnessAtLevel W hNonneg hRow 1

/--
If the maximal-item-fairness constrained optimum weakly increases between two
models, then the price of fairness weakly decreases.
-/
theorem priceOfFairness_le_of_optimalUserFairnessAtLevel_one_le
    {m n : ℕ} [NeZero m] [NeZero n]
    (W W' : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem)
    (hNonneg' : W'.Nonnegative) (hRow' : W'.RowHasPositiveItem)
    (hopt :
      optimalUserFairnessAtLevel W 1 ≤ optimalUserFairnessAtLevel W' 1) :
    priceOfFairness W' ≤ priceOfFairness W := by
  rw [priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one W hNonneg hRow]
  rw [priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one W' hNonneg' hRow']
  linarith

/--
Strict version of the price-of-fairness monotonicity algebra.
-/
theorem priceOfFairness_lt_of_optimalUserFairnessAtLevel_one_lt
    {m n : ℕ} [NeZero m] [NeZero n]
    (W W' : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem)
    (hNonneg' : W'.Nonnegative) (hRow' : W'.RowHasPositiveItem)
    (hopt :
      optimalUserFairnessAtLevel W 1 < optimalUserFairnessAtLevel W' 1) :
    priceOfFairness W' < priceOfFairness W := by
  rw [priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one W hNonneg hRow]
  rw [priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one W' hNonneg' hRow']
  linarith

/-- Problem 1 from the paper, as a predicate on candidate solution policies. -/
def SolvesProblemOne {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) (ρ : Policy m n) : Prop :=
  IsOptimalAtLevel W γ ρ

/-! ### Proposition 1: the source equality-form linear program -/

/-- The two comparison forms needed for a finite linear description of `S`. -/
inductive PolicyLinearComparison where
  | eq
  | le
deriving DecidableEq

/-- A coefficient-level linear expression in the real policy coordinates. -/
noncomputable def policyLinearExpression {m n : ℕ}
    (a : User m → Item n → ℝ) (ρ : Policy m n) : ℝ :=
  ∑ u : User m, ∑ j : Item n, a u j * (ρ u j).toReal

/-- Satisfaction of one equality or weak-inequality policy constraint. -/
def policyLinearConstraintHolds {m n : ℕ}
    (a : User m → Item n → ℝ) (b : ℝ) (rel : PolicyLinearComparison)
    (ρ : Policy m n) : Prop :=
  match rel with
  | .eq => policyLinearExpression a ρ = b
  | .le => policyLinearExpression a ρ ≤ b

/-- A source condition-(i) witness: membership in `S` is exactly satisfaction
of a finite, explicitly coefficient-level family of linear constraints. -/
structure FiniteLinearPolicySetDescription {m n : ℕ}
    (S : Set (Policy m n)) where
  ConstraintIndex : Type
  constraintFintype : Fintype ConstraintIndex
  coefficient : ConstraintIndex → User m → Item n → ℝ
  rhs : ConstraintIndex → ℝ
  comparison : ConstraintIndex → PolicyLinearComparison
  mem_iff :
    ∀ ρ : Policy m n,
      ρ ∈ S ↔
        ∀ c : ConstraintIndex,
          policyLinearConstraintHolds (coefficient c) (rhs c) (comparison c) ρ

namespace FiniteLinearPolicySetDescription

/-- A policy satisfies the finite constraints describing `S`. -/
def Satisfies {m n : ℕ} {S : Set (Policy m n)}
    (D : FiniteLinearPolicySetDescription S) (ρ : Policy m n) : Prop :=
  ∀ c : D.ConstraintIndex,
    policyLinearConstraintHolds (D.coefficient c) (D.rhs c) (D.comparison c) ρ

theorem satisfies_iff_mem {m n : ℕ} {S : Set (Policy m n)}
    (D : FiniteLinearPolicySetDescription S) (ρ : Policy m n) :
    D.Satisfies ρ ↔ ρ ∈ S := by
  exact (D.mem_iff ρ).symm

end FiniteLinearPolicySetDescription

/-- The item-`j` equality of the source LP, written as a linear expression in
the policy coordinates and the objective variable `ell`. -/
noncomputable def propositionOneItemEqualityExpression {m n : ℕ}
    (W : RecommendationModel m n) (j : Item n)
    (ρ : Policy m n) (ell : ℝ) : ℝ :=
  (∑ u : User m,
      (W.utility u j / itemNormalizer W j) * (ρ u j).toReal) - ell

/-- Under the paper's positive-utility model, the coefficient-level item
equation is exactly `I_j(ρ) = ell`. -/
theorem propositionOneItemEqualityExpression_eq_normalized_sub
    {m n : ℕ} [NeZero m]
    (W : RecommendationModel m n) (hPos : W.Positive)
    (j : Item n) (ρ : Policy m n) (ell : ℝ) :
    propositionOneItemEqualityExpression W j ρ ell =
      normalizedItemUtility W ρ j - ell := by
  have hden : 0 < itemNormalizer W j :=
    W.columnHasPositiveDemand_of_positive hPos j
  unfold propositionOneItemEqualityExpression normalizedItemUtility
  rw [dif_neg hden.ne']
  unfold rawItemUtility
  apply congrArg (fun x : ℝ => x - ell)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro u _hu
  ring

theorem propositionOneItemEqualityExpression_eq_zero_iff
    {m n : ℕ} [NeZero m]
    (W : RecommendationModel m n) (hPos : W.Positive)
    (j : Item n) (ρ : Policy m n) (ell : ℝ) :
    propositionOneItemEqualityExpression W j ρ ell = 0 ↔
      normalizedItemUtility W ρ j = ell := by
  rw [propositionOneItemEqualityExpression_eq_normalized_sub W hPos]
  exact sub_eq_zero

/-- Feasibility for the concrete LP `L` in Proposition 1: the policy satisfies
the finite linear description of `S`, and every normalized item utility equals
the objective variable.  The policy type itself supplies the simplex rows. -/
abbrev PropositionOneLPFeasible {m n : ℕ} {S : Set (Policy m n)}
    (W : RecommendationModel m n)
    (D : FiniteLinearPolicySetDescription S)
    (ρ : Policy m n) (ell : ℝ) : Prop :=
  D.Satisfies ρ ∧
    ∀ j : Item n, propositionOneItemEqualityExpression W j ρ ell = 0

/-- A maximizer of Proposition 1's concrete LP `L`. -/
abbrev PropositionOneLPSolution {m n : ℕ} {S : Set (Policy m n)}
    (W : RecommendationModel m n)
    (D : FiniteLinearPolicySetDescription S)
    (ρ : Policy m n) (ell : ℝ) : Prop :=
  PropositionOneLPFeasible W D ρ ell ∧
    ∀ ρ' : Policy m n, ∀ ell' : ℝ,
      PropositionOneLPFeasible W D ρ' ell' → ell' ≤ ell

/-- The LP has the source policy as its unique policy optimizer (and hence
also pins the optimal objective value). -/
abbrev PropositionOneLPUniquePolicyOptimizer {m n : ℕ} [NeZero n]
    {S : Set (Policy m n)}
    (W : RecommendationModel m n)
    (D : FiniteLinearPolicySetDescription S)
    (ρstar : Policy m n) : Prop :=
  PropositionOneLPSolution W D ρstar (optimalItemFairness W) ∧
    ∀ ρ : Policy m n, ∀ ell : ℝ,
      PropositionOneLPSolution W D ρ ell →
        ρ = ρstar ∧ ell = optimalItemFairness W

/--
Proposition 1, with the source hypotheses and conclusion.

Condition (i) is the finite coefficient-level description `D`; condition (ii)
is `hProblemTwo`; condition (iii) is `hUniqueFeasible`.  The conclusion is not
a reduction witness: it proves that the source equality-form LP `L` recovers
`ρstar` as its unique policy optimizer.
-/
theorem propositionOne_unique_policy_optimizer_of_source_conditions
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPos : W.Positive)
    (S : Set (Policy m n)) (D : FiniteLinearPolicySetDescription S)
    (ρstar : Policy m n)
    (hProblemTwo : IsOptimalAtLevel W 1 ρstar)
    (hStarMem : ρstar ∈ S)
    (hUniqueFeasible :
      ∀ ρ : Policy m n,
        ρ ∈ S → itemFairness W ρ = optimalItemFairness W → ρ = ρstar) :
    PropositionOneLPUniquePolicyOptimizer W D ρstar := by
  have hNonneg : W.Nonnegative := W.nonnegative_of_positive hPos
  have hstar_item_le :
      itemFairness W ρstar ≤ optimalItemFairness W := by
    exact le_csSup (attainableItemFairnessSet_bddAbove_of_nonnegative W hNonneg)
      ⟨ρstar, rfl⟩
  have hstar_item_ge :
      optimalItemFairness W ≤ itemFairness W ρstar := by
    simpa [feasibleAtLevel] using hProblemTwo.1
  have hstar_item :
      itemFairness W ρstar = optimalItemFairness W :=
    le_antisymm hstar_item_le hstar_item_ge
  have hstar_equalized :
      itemFairnessEqualityLPFeasible W ρstar (optimalItemFairness W) := by
    rw [← hstar_item]
    exact itemFairnessEqualityLPFeasible_of_optimal_of_slackImprovement
      W hNonneg hstar_item
      (itemFairnessSlackImprovementProperty_of_positive_of_optimal
        W hPos hstar_item)
  have hstar_feasible :
      PropositionOneLPFeasible W D ρstar (optimalItemFairness W) := by
    refine ⟨(D.satisfies_iff_mem ρstar).mpr hStarMem, ?_⟩
    intro j
    exact (propositionOneItemEqualityExpression_eq_zero_iff
      W hPos j ρstar (optimalItemFairness W)).mpr (hstar_equalized j)
  have hupper :
      ∀ ρ : Policy m n, ∀ ell : ℝ,
        PropositionOneLPFeasible W D ρ ell → ell ≤ optimalItemFairness W := by
    intro ρ ell hfeas
    have heq : itemFairnessEqualityLPFeasible W ρ ell := by
      intro j
      exact (propositionOneItemEqualityExpression_eq_zero_iff
        W hPos j ρ ell).mp (hfeas.2 j)
    have hitem : itemFairness W ρ = ell :=
      itemFairness_eq_of_itemFairnessEqualityLPFeasible W ρ ell heq
    rw [← hitem]
    exact le_csSup (attainableItemFairnessSet_bddAbove_of_nonnegative W hNonneg)
      ⟨ρ, rfl⟩
  refine ⟨⟨hstar_feasible, hupper⟩, ?_⟩
  intro ρ ell hsol
  have hell_le : ell ≤ optimalItemFairness W := hupper ρ ell hsol.1
  have hopt_le : optimalItemFairness W ≤ ell :=
    hsol.2 ρstar (optimalItemFairness W) hstar_feasible
  have hell : ell = optimalItemFairness W := le_antisymm hell_le hopt_le
  have hρmem : ρ ∈ S := (D.satisfies_iff_mem ρ).mp hsol.1.1
  have heq : itemFairnessEqualityLPFeasible W ρ ell := by
    intro j
    exact (propositionOneItemEqualityExpression_eq_zero_iff
      W hPos j ρ ell).mp (hsol.1.2 j)
  have hitem : itemFairness W ρ = ell :=
    itemFairness_eq_of_itemFairnessEqualityLPFeasible W ρ ell heq
  exact ⟨hUniqueFeasible ρ hρmem (hitem.trans hell), hell⟩

end RecommendationModel

namespace EstimatedRecommendationModel

/-- A policy is optimal for the estimated utility matrix at level `γ`. -/
def SolvesEstimatedProblem {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρ : Policy m n) : Prop :=
  RecommendationModel.IsOptimalAtLevel E.estimatedModel γ ρ

/--
If the estimated utility matrix is exactly the true matrix, then the estimated
recommendation model is the true recommendation model.
-/
theorem estimatedModel_eq_true_of_estimatedUtility_eq_true
    {m n : ℕ} (E : EstimatedRecommendationModel m n)
    (h : E.estimatedUtility = E.trueModel.utility) :
    E.estimatedModel = E.trueModel := by
  cases E with
  | mk trueModel estimatedUtility =>
    cases trueModel
    simpa [estimatedModel] using h

/--
The paper's price of misestimation, evaluated on a chosen policy `ρ̂` that is intended
to solve the estimated problem.
-/
noncomputable def priceOfMisestimation {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n) : ℝ :=
  let base := RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ
  if h : base = 0 then 0 else
    (base - RecommendationModel.userFairness E.trueModel ρhat) / base

/--
Exact-estimation benchmark for the paper's price of misestimation: if the
estimated model is the true model and `ρ̂` solves the estimated problem, then
there is no loss from misestimation.
-/
theorem priceOfMisestimation_eq_zero_of_estimatedModel_eq_true
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n)
    (hmodel : E.estimatedModel = E.trueModel)
    (hopt : E.SolvesEstimatedProblem γ ρhat) :
    E.priceOfMisestimation γ ρhat = 0 := by
  unfold SolvesEstimatedProblem at hopt
  rw [hmodel] at hopt
  have huser :
      RecommendationModel.userFairness E.trueModel ρhat =
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ := hopt.2
  unfold priceOfMisestimation
  by_cases hbase :
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ = 0
  · simp [hbase]
  · simp [hbase, huser]

/--
Exact-estimation benchmark stated directly in terms of utility matrices.
-/
theorem priceOfMisestimation_eq_zero_of_estimatedUtility_eq_true
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n)
    (hutility : E.estimatedUtility = E.trueModel.utility)
    (hopt : E.SolvesEstimatedProblem γ ρhat) :
    E.priceOfMisestimation γ ρhat = 0 := by
  exact E.priceOfMisestimation_eq_zero_of_estimatedModel_eq_true γ ρhat
    (E.estimatedModel_eq_true_of_estimatedUtility_eq_true hutility) hopt

/--
When the true constrained optimum is positive, the price of misestimation is
`1 - U_min(ρhat,w) / U^*_min(γ,w)`.
-/
theorem priceOfMisestimation_eq_one_sub_userFairness_div
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n)
    (hbase : 0 <
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ) :
    E.priceOfMisestimation γ ρhat =
      1 - RecommendationModel.userFairness E.trueModel ρhat /
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ := by
  unfold priceOfMisestimation
  simp [hbase.ne']
  field_simp [hbase.ne']

/--
If a candidate policy gives true user fairness less than an `eps` fraction of
the true optimum, its price of misestimation is greater than `1 - eps`.
-/
theorem priceOfMisestimation_gt_one_sub_of_userFairness_lt_mul_optimum
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ eps : ℝ) (ρhat : Policy m n)
    (hbase : 0 <
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ)
    (huser :
      RecommendationModel.userFairness E.trueModel ρhat <
        eps * RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ) :
    1 - eps < E.priceOfMisestimation γ ρhat := by
  rw [E.priceOfMisestimation_eq_one_sub_userFairness_div γ ρhat hbase]
  have hratio :
      RecommendationModel.userFairness E.trueModel ρhat /
          RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ < eps := by
    rw [div_lt_iff₀ hbase]
    simpa [mul_comm] using huser
  linarith

/--
The final algebraic step in Appendix E's proof of Theorem 4: if the true
maximal-fairness optimum is above `1/n` while the estimated optimum's chosen
policy gives true user fairness below `eps/n`, then the price of
misestimation is above `1 - eps`.
-/
theorem priceOfMisestimation_gt_one_sub_of_userFairness_lt_div_card
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (eps : ℝ) (ρhat : Policy m n)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (huser :
      RecommendationModel.userFairness E.trueModel ρhat <
        eps / (n : ℝ)) :
    1 - eps < E.priceOfMisestimation 1 ρhat := by
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast (NeZero.pos n)
  have hinv_pos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hn_pos
  have hbase_pos :
      0 < RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1 :=
    lt_trans hinv_pos hbase
  have huser_mul :
      RecommendationModel.userFairness E.trueModel ρhat <
        eps * RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1 := by
    have hscale :
        eps * (n : ℝ)⁻¹ <
          eps * RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1 :=
      mul_lt_mul_of_pos_left hbase heps
    exact lt_trans (by simpa [div_eq_mul_inv] using huser) hscale
  exact E.priceOfMisestimation_gt_one_sub_of_userFairness_lt_mul_optimum
    1 eps ρhat hbase_pos huser_mul

/--
The first-bullet algebra in Theorem 4: if the unconstrained true optimum is
`1` and the policy chosen under estimated utilities gives true user fairness at
least `1/2`, then the price of misestimation without item-fairness constraints
is at most `1/2`.
-/
theorem priceOfMisestimation_at_zero_le_half_of_userFairness_ge_half
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (ρhat : Policy m n)
    (hbase :
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel 0 = 1)
    (huser :
      (1 / 2 : ℝ) ≤ RecommendationModel.userFairness E.trueModel ρhat) :
    E.priceOfMisestimation 0 ρhat ≤ (1 / 2 : ℝ) := by
  unfold priceOfMisestimation
  simp [hbase]
  linarith

end EstimatedRecommendationModel
end GCG24UserItemFairness
