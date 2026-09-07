import LMMS04FairDivision.ProofInterface

/-!
# Paper Assumptions: LMMS04 Fair Division

This file records theorem-domain conditions and documented partial-formalization
boundaries used by the compact LMMS04 review surface. The Section 3 PTAS/FPTAS
runtime layer remains conditional on reusable fixed-dimension integer-program
complexity infrastructure.
-/

namespace LMMS04FairDivision

open scoped BigOperators
open AppliedModelingLib.FairDivision

/-! ## Section 2 -/

/-- The alpha-bounded envy statements use a nonnegative marginal-value bound. -/
-- audit-premise: halpha_nonneg : 0 ≤ alpha
abbrev assumption_nonnegative_alpha_bound (alpha : ℝ) : Prop :=
  0 ≤ alpha

/-- The alpha-bounded form assumes every marginal item value is at most `alpha`. -/
-- audit-premise: hbound : MarginalBound v alpha
abbrev assumption_alpha_marginal_value_bound
    {Agent Item : Type*} [DecidableEq Item]
    (v : Valuation Agent Item) (alpha : ℝ) : Prop :=
  MarginalBound v alpha

/-- The constructive algorithm endpoint enumerates the input goods without duplicates. -/
-- audit-premise: hnodup : goodsList.Nodup
abbrev assumption_duplicate_free_goods_enumeration {Item : Type*}
    (goodsList : List Item) : Prop :=
  goodsList.Nodup

/-- The measure-valued envy theorem is stated for a positive atom bound. -/
-- audit-premise: halpha_pos : 0 < alpha
abbrev assumption_positive_atom_bound (alpha : ℝ) : Prop :=
  0 < alpha

/-! ## Section 3 -/

/-- PTAS/FPTAS ratio statements quantify over the usual positive error range. -/
-- audit-premise: hepsilon_pos : 0 < epsilon
-- audit-premise: hepsilon_le_one : epsilon ≤ 1
abbrev assumption_ptas_error_parameter_range (epsilon : ℝ) : Prop :=
  0 < epsilon ∧ epsilon ≤ 1

/-- Rounded-search statements expose the paper's positive load and rounding-scale domain. -/
-- audit-premise: hlambda : 1 < lambda
-- audit-premise: hlambda : 0 < lambda
-- audit-premise: hL : 0 < L
-- audit-premise: hLR : 0 < LR
abbrev assumption_positive_rounding_and_load_parameters
    (lambda L LR : ℝ) : Prop :=
  1 < lambda ∧ 0 < lambda ∧ 0 < L ∧ 0 < LR

/-- Capped rounded-supply endpoints compare the base load with the rounded average. -/
-- audit-premise: hbase_le_avg : L ≤ LR
abbrev assumption_base_load_at_most_rounded_average (L LR : ℝ) : Prop :=
  L ≤ LR

/-- Claim 3.4 finite small-good model uses positive goods whose value is below `L`. -/
-- audit-premise: hgoods_pos : ∀ g : SourceItem, g ∈ goods → 0 < v g
-- audit-premise: hgoods_lt : ∀ g : SourceItem, g ∈ goods → v g < L
-- audit-premise: hitem_nonneg : ∀ A : Alloc, ∀ i : SourceAgent, ∀ g : SourceItem, g ∈ M.bundleOf A i → 0 ≤ M.commonValue g
-- audit-premise: hitem_lt : ∀ A : Alloc, ∀ i : SourceAgent, ∀ g : SourceItem, g ∈ M.bundleOf A i → M.commonValue g < L
abbrev assumption_claim34_positive_small_goods_domain
    {SourceItem SourceAgent Alloc : Type*} [DecidableEq SourceItem]
    (goods : Finset SourceItem) (v commonValue : SourceItem → ℝ)
    (bundleOf : Alloc → SourceAgent → Finset SourceItem) (L : ℝ) : Prop :=
  (∀ g : SourceItem, g ∈ goods → 0 < v g) ∧
    (∀ g : SourceItem, g ∈ goods → v g < L) ∧
      (∀ A : Alloc, ∀ i : SourceAgent, ∀ g : SourceItem,
        g ∈ bundleOf A i → 0 ≤ commonValue g) ∧
        (∀ A : Alloc, ∀ i : SourceAgent, ∀ g : SourceItem,
          g ∈ bundleOf A i → commonValue g < L)

/--
Lemma 3.5's algebraic transfer row exposes positivity and half-load window
conditions for the source, rounded, and output loads.
-/
-- audit-premise: houtMin : 0 < outMin
-- audit-premise: hroundedMin : 0 < roundedMin
-- audit-premise: hoptMin : 0 < optMin
-- audit-premise: hoptMax : 0 ≤ optMax
-- audit-premise: hroundedMax_nonneg : 0 ≤ roundedMax
-- audit-premise: hroundedMin_half : L ≤ 2 * roundedMin
-- audit-premise: hroundedMax_half : L ≤ 2 * roundedMax
-- audit-premise: hoptMin_half : L ≤ 2 * optMin
-- audit-premise: hoptMax_half : L ≤ 2 * optMax
abbrev assumption_additive_transfer_load_window_conditions
    (L outMin roundedMin optMin optMax roundedMax : ℝ) : Prop :=
  0 < outMin ∧
    0 < roundedMin ∧
      0 < optMin ∧
        0 ≤ optMax ∧
          0 ≤ roundedMax ∧
            L ≤ 2 * roundedMin ∧
              L ≤ 2 * roundedMax ∧
                L ≤ 2 * optMin ∧
                  L ≤ 2 * optMax

/-! ## Section 4 -/

/-- The randomized allocation concentration bound uses normalized nonnegative item weights. -/
-- audit-premise: halpha : 0 ≤ alpha
-- audit-premise: ht : 0 < t
-- audit-premise: hnonneg : ∀ p : Agent, ∀ g : Item, 0 ≤ w p g
-- audit-premise: hsum : ∀ p : Agent, ∑ g : Item, w p g = 1
-- audit-premise: hbound : ∀ p : Agent, ∀ g : Item, w p g ≤ alpha
abbrev assumption_uniform_random_weight_normalization
    {Agent Item : Type*} [Fintype Item]
    (w : Agent → Item → ℝ) (alpha t : ℝ) : Prop :=
  0 ≤ alpha ∧
    0 < t ∧
      (∀ p : Agent, ∀ g : Item, 0 ≤ w p g) ∧
        (∀ p : Agent, ∑ g : Item, w p g = 1) ∧
          (∀ p : Agent, ∀ g : Item, w p g ≤ alpha)

end LMMS04FairDivision
