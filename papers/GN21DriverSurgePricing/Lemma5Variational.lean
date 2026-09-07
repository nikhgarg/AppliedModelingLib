import GN21DriverSurgePricing.CutoffAttainment
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.IntermediateValue

/-!
# Source-exact endpoint forms for GN21 Lemma 5

The printed Lemma 5 allows finite or infinite endpoints in its decreasing,
quasi-convex, and quasi-concave branches.  The older `lemma5PolicyForm`
predicate only has real-valued endpoints, so it is useful for finite endpoint
calculus but is not the source-facing conclusion type.

This file defines the endpoint-complete policy families used by the variational
proof.  They are predicates and ordinary policies, not records carrying a
theorem conclusion.
-/

open AppliedModelingLib
open MeasureTheory
open Filter
open scoped Topology ENNReal symmDiff

namespace GN21DriverSurgePricing

/-- The open middle interval with endpoints in `[0, infinity]`. -/
def gn21ExtendedMiddlePolicy (lower upper : ℝ≥0∞) : TripPolicy :=
  gn21RightExtendedCutoffPolicy lower ∩ gn21LeftExtendedCutoffPolicy upper

/-- The union of the two open tails with endpoints in `[0, infinity]`. -/
def gn21ExtendedTwoTailPolicy (lower upper : ℝ≥0∞) : TripPolicy :=
  gn21LeftExtendedCutoffPolicy lower ∪ gn21RightExtendedCutoffPolicy upper

@[simp] theorem gn21ExtendedMiddlePolicy_coe_coe (lower upper : NNReal) :
    gn21ExtendedMiddlePolicy (lower : ℝ≥0∞) (upper : ℝ≥0∞) =
      acceptMiddleTripsPolicy (lower : ℝ) (upper : ℝ) := by
  ext τ
  simp [gn21ExtendedMiddlePolicy, acceptMiddleTripsPolicy,
    rejectShortTripsPolicy, rejectLongTripsPolicy]
  intro hlower _hupper
  exact lt_of_le_of_lt lower.property hlower

@[simp] theorem gn21ExtendedTwoTailPolicy_coe_coe (lower upper : NNReal) :
    gn21ExtendedTwoTailPolicy (lower : ℝ≥0∞) (upper : ℝ≥0∞) =
      rejectMiddleTripsPolicy (lower : ℝ) (upper : ℝ) := by
  ext τ
  simp [gn21ExtendedTwoTailPolicy, rejectMiddleTripsPolicy,
    rejectShortTripsPolicy, rejectLongTripsPolicy]
  constructor
  · rintro (⟨hτ, hlower⟩ | hupper)
    · exact ⟨hτ, Or.inl hlower⟩
    · exact ⟨lt_of_le_of_lt upper.property hupper, Or.inr hupper⟩
  · rintro ⟨hτ, hlower | hupper⟩
    · exact Or.inl ⟨hτ, hlower⟩
    · exact Or.inr hupper

theorem gn21ExtendedMiddlePolicy_coe_coe_eq_Ioo
    (lower upper : NNReal) :
    gn21ExtendedMiddlePolicy (lower : ℝ≥0∞) (upper : ℝ≥0∞) =
      Set.Ioo (lower : ℝ) (upper : ℝ) := by
  rw [gn21ExtendedMiddlePolicy_coe_coe]
  ext τ
  constructor
  · intro hτ
    exact ⟨hτ.1.2, hτ.2⟩
  · intro hτ
    exact ⟨⟨lt_of_le_of_lt lower.property hτ.1, hτ.1⟩, hτ.2⟩

theorem gn21ExtendedMiddlePolicy_coe_top_eq_Ioi (lower : NNReal) :
    gn21ExtendedMiddlePolicy (lower : ℝ≥0∞) ∞ =
      Set.Ioi (lower : ℝ) := by
  rw [gn21ExtendedMiddlePolicy, gn21LeftExtendedCutoffPolicy_top,
    gn21RightExtendedCutoffPolicy_coe]
  rw [Set.inter_eq_left.2
    (rejectShortTripsPolicy_subset_acceptAll (lower : ℝ))]
  ext τ
  constructor
  · exact fun hτ => hτ.2
  · intro hτ
    exact ⟨lt_of_le_of_lt lower.property hτ, hτ⟩

@[simp] theorem gn21ExtendedMiddlePolicy_zero_top :
    gn21ExtendedMiddlePolicy 0 ∞ = acceptAllPolicy := by
  simp [gn21ExtendedMiddlePolicy]

@[simp] theorem gn21ExtendedMiddlePolicy_zero (upper : ℝ≥0∞) :
    gn21ExtendedMiddlePolicy 0 upper =
      gn21LeftExtendedCutoffPolicy upper := by
  rw [gn21ExtendedMiddlePolicy, gn21RightExtendedCutoffPolicy_zero]
  exact Set.inter_eq_right.2
    (gn21LeftExtendedCutoffPolicy_subset_acceptAll upper)

@[simp] theorem gn21ExtendedMiddlePolicy_top_right (lower : ℝ≥0∞) :
    gn21ExtendedMiddlePolicy lower ∞ =
      gn21RightExtendedCutoffPolicy lower := by
  rw [gn21ExtendedMiddlePolicy, gn21LeftExtendedCutoffPolicy_top]
  exact Set.inter_eq_left.2
    (gn21RightExtendedCutoffPolicy_subset_acceptAll lower)

@[simp] theorem gn21ExtendedMiddlePolicy_top (upper : ℝ≥0∞) :
    gn21ExtendedMiddlePolicy ∞ upper = ∅ := by
  simp [gn21ExtendedMiddlePolicy]

@[simp] theorem gn21ExtendedTwoTailPolicy_top_left (upper : ℝ≥0∞) :
    gn21ExtendedTwoTailPolicy ∞ upper = acceptAllPolicy := by
  rw [gn21ExtendedTwoTailPolicy, gn21LeftExtendedCutoffPolicy_top]
  exact Set.union_eq_left.2
    (gn21RightExtendedCutoffPolicy_subset_acceptAll upper)

@[simp] theorem gn21ExtendedTwoTailPolicy_zero_top :
    gn21ExtendedTwoTailPolicy 0 ∞ = ∅ := by
  simp [gn21ExtendedTwoTailPolicy]

theorem gn21ExtendedMiddlePolicy_eq_empty_of_le
    {lower upper : ℝ≥0∞} (hupper_lower : upper ≤ lower) :
    gn21ExtendedMiddlePolicy lower upper = ∅ := by
  cases lower using ENNReal.recTopCoe with
  | top => exact gn21ExtendedMiddlePolicy_top upper
  | coe lowerFinite =>
      cases upper using ENNReal.recTopCoe with
      | top => simp at hupper_lower
      | coe upperFinite =>
          rw [gn21ExtendedMiddlePolicy_coe_coe_eq_Ioo]
          ext τ
          simp only [Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hlower, hupper⟩
          have hupper_lower_real :
              (upperFinite : ℝ) ≤ (lowerFinite : ℝ) := by
            exact_mod_cast ENNReal.coe_le_coe.mp hupper_lower
          exact (not_lt_of_ge hupper_lower_real) (hlower.trans hupper)

theorem gn21ExtendedTwoTailPolicy_eq_acceptAll_of_lt
    {lower upper : ℝ≥0∞} (hupper_lower : upper < lower) :
    gn21ExtendedTwoTailPolicy lower upper = acceptAllPolicy := by
  cases lower using ENNReal.recTopCoe with
  | top => exact gn21ExtendedTwoTailPolicy_top_left upper
  | coe lowerFinite =>
      cases upper using ENNReal.recTopCoe with
      | top => simp at hupper_lower
      | coe upperFinite =>
          rw [gn21ExtendedTwoTailPolicy_coe_coe]
          ext τ
          simp only [rejectMiddleTripsPolicy, acceptAllPolicy,
            positiveTripLengths, Set.mem_inter_iff, Set.mem_Ioi,
            Set.mem_union, Set.mem_Iio]
          constructor
          · exact fun hτ => hτ.1
          · intro hτ
            refine ⟨hτ, ?_⟩
            by_cases hτ_lower : τ < (lowerFinite : ℝ)
            · exact Or.inl hτ_lower
            · right
              have hupper_lower_real :
                  (upperFinite : ℝ) < (lowerFinite : ℝ) := by
                exact_mod_cast hupper_lower
              exact hupper_lower_real.trans_le (le_of_not_gt hτ_lower)

theorem gn21ExtendedMiddlePolicy_subset_acceptAll
    (lower upper : ℝ≥0∞) :
    gn21ExtendedMiddlePolicy lower upper ⊆ acceptAllPolicy := by
  intro τ hτ
  exact gn21RightExtendedCutoffPolicy_subset_acceptAll lower hτ.1

theorem gn21ExtendedTwoTailPolicy_subset_acceptAll
    (lower upper : ℝ≥0∞) :
    gn21ExtendedTwoTailPolicy lower upper ⊆ acceptAllPolicy := by
  intro τ hτ
  rcases hτ with hτ | hτ
  · exact gn21LeftExtendedCutoffPolicy_subset_acceptAll lower hτ
  · exact gn21RightExtendedCutoffPolicy_subset_acceptAll upper hτ

theorem gn21ExtendedMiddlePolicy_open (lower upper : ℝ≥0∞) :
    IsOpen (gn21ExtendedMiddlePolicy lower upper) :=
  (gn21RightExtendedCutoffPolicy_open lower).inter
    (gn21LeftExtendedCutoffPolicy_open upper)

theorem gn21ExtendedTwoTailPolicy_open (lower upper : ℝ≥0∞) :
    IsOpen (gn21ExtendedTwoTailPolicy lower upper) :=
  (gn21LeftExtendedCutoffPolicy_open lower).union
    (gn21RightExtendedCutoffPolicy_open upper)

theorem gn21ExtendedMiddlePolicy_measurable (lower upper : ℝ≥0∞) :
    MeasurableSet (gn21ExtendedMiddlePolicy lower upper) :=
  (gn21ExtendedMiddlePolicy_open lower upper).measurableSet

theorem gn21ExtendedTwoTailPolicy_measurable (lower upper : ℝ≥0∞) :
    MeasurableSet (gn21ExtendedTwoTailPolicy lower upper) :=
  (gn21ExtendedTwoTailPolicy_open lower upper).measurableSet

@[simp] theorem gn21ExtendedMiddlePolicy_self (endpoint : ℝ≥0∞) :
    gn21ExtendedMiddlePolicy endpoint endpoint = ∅ := by
  cases endpoint using ENNReal.recTopCoe with
  | top => simp [gn21ExtendedMiddlePolicy]
  | coe endpointFinite =>
      rw [gn21ExtendedMiddlePolicy_coe_coe_eq_Ioo]
      exact Set.Ioo_self (endpointFinite : ℝ)

/--
The five endpoint-complete policy forms in the printed Lemma 5 table at
`source.txt:3370-3386`.  The strictly increasing branch has a finite
nonnegative lower endpoint, exactly as printed; the other branches retain the
paper's explicit infinity endpoints.
-/
def lemma5SourcePolicyForm
    (shape : Lemma5DerivativeShape) (policy : TripPolicy) : Prop :=
  match shape with
  | .positive => policy = acceptAllPolicy
  | .strictlyIncreasing =>
      ∃ cutoff : NNReal,
        policy = gn21RightExtendedCutoffPolicy (cutoff : ℝ≥0∞)
  | .strictlyDecreasing =>
      ∃ cutoff : ℝ≥0∞, policy = gn21LeftExtendedCutoffPolicy cutoff
  | .strictlyQuasiConvex =>
      ∃ lower upper : ℝ≥0∞,
        policy = gn21ExtendedTwoTailPolicy lower upper
  | .strictlyQuasiConcave =>
      ∃ lower upper : ℝ≥0∞,
        policy = gn21ExtendedMiddlePolicy lower upper

/-- Source Lemma 5 policy form under the paper's equality-up-to-null-sets convention. -/
def lemma5SourcePolicyFormAlmostEverywhere
    (mu : Measure TripLength) (shape : Lemma5DerivativeShape)
    (policy : TripPolicy) : Prop :=
  ∃ representative : TripPolicy,
    lemma5SourcePolicyForm shape representative ∧
      policyAlmostEverywhereEq mu policy representative

theorem lemma5SourcePolicyForm_subset_acceptAll
    {shape : Lemma5DerivativeShape} {policy : TripPolicy}
    (hform : lemma5SourcePolicyForm shape policy) :
    policy ⊆ acceptAllPolicy := by
  cases shape with
  | positive =>
      rw [show policy = acceptAllPolicy from hform]
  | strictlyIncreasing =>
      rcases hform with ⟨cutoff, rfl⟩
      exact gn21RightExtendedCutoffPolicy_subset_acceptAll _
  | strictlyDecreasing =>
      rcases hform with ⟨cutoff, rfl⟩
      exact gn21LeftExtendedCutoffPolicy_subset_acceptAll _
  | strictlyQuasiConvex =>
      rcases hform with ⟨lower, upper, rfl⟩
      exact gn21ExtendedTwoTailPolicy_subset_acceptAll lower upper
  | strictlyQuasiConcave =>
      rcases hform with ⟨lower, upper, rfl⟩
      exact gn21ExtendedMiddlePolicy_subset_acceptAll lower upper

theorem lemma5SourcePolicyForm_open
    {shape : Lemma5DerivativeShape} {policy : TripPolicy}
    (hform : lemma5SourcePolicyForm shape policy) :
    IsOpen policy := by
  cases shape with
  | positive =>
      rw [show policy = acceptAllPolicy from hform]
      simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using
        (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
  | strictlyIncreasing =>
      rcases hform with ⟨cutoff, rfl⟩
      exact gn21RightExtendedCutoffPolicy_open _
  | strictlyDecreasing =>
      rcases hform with ⟨cutoff, rfl⟩
      exact gn21LeftExtendedCutoffPolicy_open _
  | strictlyQuasiConvex =>
      rcases hform with ⟨lower, upper, rfl⟩
      exact gn21ExtendedTwoTailPolicy_open lower upper
  | strictlyQuasiConcave =>
      rcases hform with ⟨lower, upper, rfl⟩
      exact gn21ExtendedMiddlePolicy_open lower upper

theorem lemma5SourcePolicyForm_measurable
    {shape : Lemma5DerivativeShape} {policy : TripPolicy}
    (hform : lemma5SourcePolicyForm shape policy) :
    MeasurableSet policy :=
  (lemma5SourcePolicyForm_open hform).measurableSet

theorem lemma5SourcePolicyFormAlmostEverywhere_of_form
    (mu : Measure TripLength) {shape : Lemma5DerivativeShape}
    {policy : TripPolicy}
    (hform : lemma5SourcePolicyForm shape policy) :
    lemma5SourcePolicyFormAlmostEverywhere mu shape policy := by
  refine ⟨policy, hform, ?_⟩
  simp [policyAlmostEverywhereEq]

/-! ## Connected components of source-open policies -/

/-- An open connected subset of `ℝ` cannot contain its finite infimum. -/
theorem gn21_isOpen_not_mem_sInf
    {component : Set ℝ}
    (hopen : IsOpen component)
    (hnonempty : component.Nonempty)
    (hbddBelow : BddBelow component) :
    sInf component ∉ component := by
  intro hinf
  rcases mem_nhds_iff_exists_Ioo_subset.mp
      (hopen.mem_nhds hinf) with ⟨lower, upper, hinf_mem, hinterval⟩
  rcases exists_between hinf_mem.1 with ⟨point, hlower_point, hpoint_inf⟩
  have hpoint_mem : point ∈ component :=
    hinterval ⟨hlower_point, hpoint_inf.trans hinf_mem.2⟩
  exact (not_lt_of_ge (csInf_le hbddBelow hpoint_mem)) hpoint_inf

/-- An open connected subset of `ℝ` cannot contain its finite supremum. -/
theorem gn21_isOpen_not_mem_sSup
    {component : Set ℝ}
    (hopen : IsOpen component)
    (hnonempty : component.Nonempty)
    (hbddAbove : BddAbove component) :
    sSup component ∉ component := by
  intro hsup
  rcases mem_nhds_iff_exists_Ioo_subset.mp
      (hopen.mem_nhds hsup) with ⟨lower, upper, hsup_mem, hinterval⟩
  rcases exists_between hsup_mem.2 with ⟨point, hsup_point, hpoint_upper⟩
  have hpoint_mem : point ∈ component :=
    hinterval ⟨hsup_mem.1.trans hsup_point, hpoint_upper⟩
  exact (not_lt_of_ge (le_csSup hbddAbove hpoint_mem)) hsup_point

/--
Every connected component of an open feasible trip policy is either a bounded
open interval or a positive right ray.  This is the topology bridge omitted by
the printed countable-interval argument.
-/
theorem connectedComponentIn_open_positive_eq_interval_or_rightRay
    {sigma : TripPolicy} (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    {point : ℝ} (hpoint : point ∈ sigma) :
    ∃ lower : ℝ, 0 ≤ lower ∧
      ((∃ upper : ℝ, lower < upper ∧
          connectedComponentIn sigma point = Set.Ioo lower upper) ∨
        connectedComponentIn sigma point = Set.Ioi lower) := by
  let component : Set ℝ := connectedComponentIn sigma point
  have hcomponent_open : IsOpen component :=
    hsigma_open.connectedComponentIn
  have hcomponent_nonempty : component.Nonempty :=
    connectedComponentIn_nonempty_iff.mpr hpoint
  have hcomponent_connected : IsConnected component :=
    isConnected_connectedComponentIn_iff.mpr hpoint
  have hcomponent_subset_positive : component ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact hsigma_subset (connectedComponentIn_subset sigma point hx)
  have hcomponent_bddBelow : BddBelow component := by
    refine ⟨0, ?_⟩
    intro x hx
    exact le_of_lt (hcomponent_subset_positive hx)
  let lower : ℝ := sInf component
  have hlower_nonneg : 0 ≤ lower := by
    exact le_csInf hcomponent_nonempty fun x hx =>
      le_of_lt (hcomponent_subset_positive hx)
  refine ⟨lower, hlower_nonneg, ?_⟩
  by_cases hcomponent_bddAbove : BddAbove component
  · let upper : ℝ := sSup component
    have hlower_not_mem : lower ∉ component := by
      exact gn21_isOpen_not_mem_sInf hcomponent_open hcomponent_nonempty
        hcomponent_bddBelow
    have hupper_not_mem : upper ∉ component := by
      exact gn21_isOpen_not_mem_sSup hcomponent_open hcomponent_nonempty
        hcomponent_bddAbove
    have hcomponent_eq : component = Set.Ioo lower upper := by
      apply Set.Subset.antisymm
      · intro x hx
        have hbounds : x ∈ Set.Icc lower upper :=
          subset_Icc_csInf_csSup hcomponent_bddBelow hcomponent_bddAbove hx
        exact
          ⟨lt_of_le_of_ne hbounds.1
              (fun h => hlower_not_mem (h.symm ▸ hx)),
            lt_of_le_of_ne hbounds.2 (fun h => hupper_not_mem (h ▸ hx))⟩
      · exact hcomponent_connected.Ioo_csInf_csSup_subset
          hcomponent_bddBelow hcomponent_bddAbove
    have hlower_upper : lower < upper := by
      rcases hcomponent_nonempty with ⟨x, hx⟩
      rw [hcomponent_eq] at hx
      exact hx.1.trans hx.2
    exact Or.inl ⟨upper, hlower_upper, hcomponent_eq⟩
  · have hlower_not_mem : lower ∉ component := by
      exact gn21_isOpen_not_mem_sInf hcomponent_open hcomponent_nonempty
        hcomponent_bddBelow
    have hcomponent_eq : component = Set.Ioi lower := by
      apply Set.Subset.antisymm
      · intro x hx
        have hlower_le : lower ≤ x := csInf_le hcomponent_bddBelow hx
        exact lt_of_le_of_ne hlower_le
          (fun h => hlower_not_mem (h.symm ▸ hx))
      · exact hcomponent_connected.2.Ioi_csInf_subset
          hcomponent_bddBelow hcomponent_bddAbove
    exact Or.inr hcomponent_eq

/-- Removing one connected component from an open policy leaves an open set. -/
theorem isOpen_diff_connectedComponentIn
    {sigma : TripPolicy} (hsigma_open : IsOpen sigma) (point : ℝ) :
    IsOpen (sigma \ connectedComponentIn sigma point) := by
  let remainder : Set ℝ := sigma \ connectedComponentIn sigma point
  have hremainder_eq :
      remainder =
        ⋃ y : {y // y ∈ remainder}, connectedComponentIn sigma y.1 := by
    ext x
    constructor
    · intro hx
      apply Set.mem_iUnion.2
      exact ⟨⟨x, hx⟩, mem_connectedComponentIn hx.1⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨y, hxy⟩
      refine ⟨connectedComponentIn_subset sigma y.1 hxy, ?_⟩
      intro hxpoint
      have hpoint_x :
          connectedComponentIn sigma point =
            connectedComponentIn sigma x :=
        connectedComponentIn_eq hxpoint
      have hy_x :
          connectedComponentIn sigma y.1 =
            connectedComponentIn sigma x :=
        connectedComponentIn_eq hxy
      have hpoint_y :
          connectedComponentIn sigma point =
            connectedComponentIn sigma y.1 :=
        hpoint_x.trans hy_x.symm
      exact y.2.2 (hpoint_y.symm ▸ mem_connectedComponentIn y.2.1)
  change IsOpen remainder
  rw [hremainder_eq]
  exact isOpen_iUnion fun y => hsigma_open.connectedComponentIn

/--
A nonempty open feasible policy that is not a right cutoff has a bounded
connected component.  The other components remain available as an arbitrary
open context for a local endpoint move.
-/
theorem exists_bounded_connectedComponent_of_not_strictlyIncreasing_form
    {sigma : TripPolicy} (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hsigma_nonempty : sigma.Nonempty)
    (hnot_form : ¬ lemma5SourcePolicyForm .strictlyIncreasing sigma) :
    ∃ point lower upper : ℝ,
      point ∈ sigma ∧ 0 ≤ lower ∧ lower < upper ∧
        connectedComponentIn sigma point = Set.Ioo lower upper := by
  rcases hsigma_nonempty with ⟨point, hpoint⟩
  rcases connectedComponentIn_open_positive_eq_interval_or_rightRay
      hsigma_open hsigma_subset hpoint with
    ⟨lower, hlower_nonneg, hbounded | hrightRay⟩
  · rcases hbounded with ⟨upper, hlower_upper, hcomponent⟩
    exact ⟨point, lower, upper, hpoint, hlower_nonneg,
      hlower_upper, hcomponent⟩
  · by_cases hsigma_component :
        sigma = connectedComponentIn sigma point
    · exfalso
      apply hnot_form
      let cutoff : NNReal := ⟨lower, hlower_nonneg⟩
      refine ⟨cutoff, ?_⟩
      rw [hsigma_component, hrightRay,
        gn21RightExtendedCutoffPolicy_coe]
      ext x
      simp only [rejectShortTripsPolicy, Set.mem_inter_iff, Set.mem_Ioi]
      dsimp [cutoff]
      constructor
      · intro hx
        exact ⟨lt_of_le_of_lt hlower_nonneg hx, hx⟩
      · exact fun hx => hx.2
    · have hcomponent_subset :
          connectedComponentIn sigma point ⊆ sigma :=
        connectedComponentIn_subset sigma point
      have hsigma_not_subset :
          ¬ sigma ⊆ connectedComponentIn sigma point := by
        intro hsubset
        exact hsigma_component
          (Set.Subset.antisymm hsubset hcomponent_subset)
      rcases Set.not_subset.mp hsigma_not_subset with
        ⟨other, hother_sigma, hother_not_component⟩
      rcases connectedComponentIn_open_positive_eq_interval_or_rightRay
          hsigma_open hsigma_subset hother_sigma with
        ⟨otherLower, hotherLower_nonneg, hotherBounded | hotherRightRay⟩
      · rcases hotherBounded with
          ⟨otherUpper, hotherLower_upper, hotherComponent⟩
        exact ⟨other, otherLower, otherUpper, hother_sigma,
          hotherLower_nonneg, hotherLower_upper, hotherComponent⟩
      · exfalso
        let common : ℝ := max lower otherLower + 1
        have hcommon_left : common ∈ connectedComponentIn sigma point := by
          rw [hrightRay]
          change lower < max lower otherLower + 1
          calc
            lower ≤ max lower otherLower := le_max_left _ _
            _ < max lower otherLower + 1 := by linarith
        have hcommon_right : common ∈ connectedComponentIn sigma other := by
          rw [hotherRightRay]
          change otherLower < max lower otherLower + 1
          calc
            otherLower ≤ max lower otherLower := le_max_right _ _
            _ < max lower otherLower + 1 := by linarith
        have hleft_common :
            connectedComponentIn sigma point =
              connectedComponentIn sigma common :=
          connectedComponentIn_eq hcommon_left
        have hright_common :
            connectedComponentIn sigma other =
              connectedComponentIn sigma common :=
          connectedComponentIn_eq hcommon_right
        have hcomponents_eq :
            connectedComponentIn sigma point =
              connectedComponentIn sigma other :=
          hleft_common.trans hright_common.symm
        exact hother_not_component
          (hcomponents_eq.symm ▸ mem_connectedComponentIn hother_sigma)

/--
The legal upper-endpoint path of one selected bounded component.  The
background is the complement of that *actual* component of `policy`, rather
than an arbitrary set supplied independently of the policy being varied.
-/
def gn21Lemma5ComponentUpperPath
    (policy : TripPolicy) (lower upper x : TripLength) : TripPolicy :=
  (policy \ Set.Ioo lower upper) ∪ Set.Ioo lower x

/-- The legal lower-endpoint path of one selected bounded component. -/
def gn21Lemma5ComponentLowerPath
    (policy : TripPolicy) (lower upper x : TripLength) : TripPolicy :=
  (policy \ Set.Ioo lower upper) ∪ Set.Ioo x upper

/-- The legal lower-endpoint path of one selected right-tail component. -/
def gn21Lemma5ComponentTailLowerPath
    (policy : TripPolicy) (lower x : TripLength) : TripPolicy :=
  (policy \ Set.Ioi lower) ∪ Set.Ioi x

/--
The Appendix-D upper-endpoint clarification.  Its derivative is required only
for a bounded connected component of the current open feasible policy.  The
component equality and the endpoint inequalities make the mutation legal and
rule out the former arbitrary-background union premise.
-/
abbrev GN21Lemma5ComponentUpperDerivativeCondition
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ) : Prop :=
  ∀ {policy : TripPolicy} {point lower upper : TripLength},
    IsOpen policy → policy ⊆ acceptAllPolicy → point ∈ policy →
      connectedComponentIn policy point = Set.Ioo lower upper →
        0 ≤ lower → lower < upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x => Rhat (gn21Lemma5ComponentUpperPath policy lower upper x))
              derivativeValue upper ∧
              sameStrictSign derivativeValue (response policy upper)

/-- The component-local lower-endpoint clarification for bounded components. -/
abbrev GN21Lemma5ComponentLowerDerivativeCondition
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ) : Prop :=
  ∀ {policy : TripPolicy} {point lower upper : TripLength},
    IsOpen policy → policy ⊆ acceptAllPolicy → point ∈ policy →
      connectedComponentIn policy point = Set.Ioo lower upper →
        0 < lower → lower < upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x => Rhat (gn21Lemma5ComponentLowerPath policy lower upper x))
              derivativeValue lower ∧
              sameStrictSign derivativeValue (-response policy lower)

/-- The one-sided component-local lower-endpoint clarification at zero. -/
abbrev GN21Lemma5ComponentLowerRightDerivativeCondition
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ) : Prop :=
  ∀ {policy : TripPolicy} {point upper : TripLength},
    IsOpen policy → policy ⊆ acceptAllPolicy → point ∈ policy →
      connectedComponentIn policy point = Set.Ioo 0 upper →
        0 < upper →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
              (fun x => Rhat (gn21Lemma5ComponentLowerPath policy 0 upper x))
              derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue (-response policy 0)

/-- The component-local lower-endpoint clarification for a right tail. -/
abbrev GN21Lemma5ComponentTailLowerDerivativeCondition
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ) : Prop :=
  ∀ {policy : TripPolicy} {point lower : TripLength},
    IsOpen policy → policy ⊆ acceptAllPolicy → point ∈ policy →
      connectedComponentIn policy point = Set.Ioi lower →
        0 < lower →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x => Rhat (gn21Lemma5ComponentTailLowerPath policy lower x))
              derivativeValue lower ∧
              sameStrictSign derivativeValue (-response policy lower)

/--
The former arbitrary-context interface is strictly stronger than the approved
component-local interface.  This adapter is retained only for legacy callers:
it specializes an arbitrary union path to the complement of an actual bounded
component.  Source-facing Lemma 5 routes use the component-local field
directly and do not invoke this adapter.
-/
theorem gn21Lemma5ComponentUpperDerivativeCondition_of_arbitraryContext
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    (hderivative :
      ∀ (context : TripPolicy) (lower upper : ℝ),
        0 ≤ lower → lower < upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x => Rhat (context ∪ Set.Ioo lower x))
              derivativeValue upper ∧
            sameStrictSign derivativeValue
              (response (context ∪ Set.Ioo lower upper) upper)) :
    GN21Lemma5ComponentUpperDerivativeCondition Rhat response := by
  intro policy point lower upper _hopen _hsubset _hpoint hcomponent
    hlower_nonneg hlower_upper
  let context : TripPolicy := policy \ Set.Ioo lower upper
  have hcomponent_subset : Set.Ioo lower upper ⊆ policy := by
    rw [← hcomponent]
    exact connectedComponentIn_subset policy point
  have hpolicy_eq : policy = context ∪ Set.Ioo lower upper := by
    ext x
    constructor
    · intro hx
      by_cases hx_interval : x ∈ Set.Ioo lower upper
      · exact Or.inr hx_interval
      · exact Or.inl ⟨hx, hx_interval⟩
    · rintro (hx | hx)
      · exact hx.1
      · exact hcomponent_subset hx
  rcases hderivative context lower upper hlower_nonneg hlower_upper with
    ⟨derivativeValue, hderiv, hsign⟩
  refine ⟨derivativeValue, ?_, ?_⟩
  · simpa [gn21Lemma5ComponentUpperPath, context] using hderiv
  · rw [hpolicy_eq]
    exact hsign

/-- Legacy-to-local adapter for a bounded component's lower endpoint. -/
theorem gn21Lemma5ComponentLowerDerivativeCondition_of_arbitraryContext
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    (hderivative :
      ∀ (context : TripPolicy) (lower upper : ℝ),
        0 < lower → lower < upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x => Rhat (context ∪ Set.Ioo x upper))
              derivativeValue lower ∧
            sameStrictSign derivativeValue
              (-response (context ∪ Set.Ioo lower upper) lower)) :
    GN21Lemma5ComponentLowerDerivativeCondition Rhat response := by
  intro policy point lower upper _hopen _hsubset _hpoint hcomponent
    hlower_pos hlower_upper
  let context : TripPolicy := policy \ Set.Ioo lower upper
  have hcomponent_subset : Set.Ioo lower upper ⊆ policy := by
    rw [← hcomponent]
    exact connectedComponentIn_subset policy point
  have hpolicy_eq : policy = context ∪ Set.Ioo lower upper := by
    ext x
    constructor
    · intro hx
      by_cases hx_interval : x ∈ Set.Ioo lower upper
      · exact Or.inr hx_interval
      · exact Or.inl ⟨hx, hx_interval⟩
    · rintro (hx | hx)
      · exact hx.1
      · exact hcomponent_subset hx
  rcases hderivative context lower upper hlower_pos hlower_upper with
    ⟨derivativeValue, hderiv, hsign⟩
  refine ⟨derivativeValue, ?_, ?_⟩
  · simpa [gn21Lemma5ComponentLowerPath, context] using hderiv
  · rw [hpolicy_eq]
    exact hsign

/-- Legacy-to-local adapter for the bounded component whose lower endpoint is zero. -/
theorem gn21Lemma5ComponentLowerRightDerivativeCondition_of_arbitraryContext
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    (hderivative :
      ∀ (context : TripPolicy) (upper : ℝ),
        0 < upper →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
              (fun x => Rhat (context ∪ Set.Ioo x upper))
              derivativeValue (Set.Ici 0) 0 ∧
            sameStrictSign derivativeValue
              (-response (context ∪ Set.Ioo 0 upper) 0)) :
    GN21Lemma5ComponentLowerRightDerivativeCondition Rhat response := by
  intro policy point upper _hopen _hsubset _hpoint hcomponent hupper_pos
  let context : TripPolicy := policy \ Set.Ioo 0 upper
  have hcomponent_subset : Set.Ioo 0 upper ⊆ policy := by
    rw [← hcomponent]
    exact connectedComponentIn_subset policy point
  have hpolicy_eq : policy = context ∪ Set.Ioo 0 upper := by
    ext x
    constructor
    · intro hx
      by_cases hx_interval : x ∈ Set.Ioo 0 upper
      · exact Or.inr hx_interval
      · exact Or.inl ⟨hx, hx_interval⟩
    · rintro (hx | hx)
      · exact hx.1
      · exact hcomponent_subset hx
  rcases hderivative context upper hupper_pos with
    ⟨derivativeValue, hderiv, hsign⟩
  refine ⟨derivativeValue, ?_, ?_⟩
  · simpa [gn21Lemma5ComponentLowerPath, context] using hderiv
  · rw [hpolicy_eq]
    exact hsign

/-- Legacy-to-local adapter for a selected right-tail component. -/
theorem gn21Lemma5ComponentTailLowerDerivativeCondition_of_arbitraryContext
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    (hderivative :
      ∀ (context : TripPolicy) (lower : ℝ),
        0 < lower →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x => Rhat (context ∪ Set.Ioi x))
              derivativeValue lower ∧
            sameStrictSign derivativeValue
              (-response (context ∪ Set.Ioi lower) lower)) :
    GN21Lemma5ComponentTailLowerDerivativeCondition Rhat response := by
  intro policy point lower _hopen _hsubset _hpoint hcomponent hlower_pos
  let context : TripPolicy := policy \ Set.Ioi lower
  have hcomponent_subset : Set.Ioi lower ⊆ policy := by
    rw [← hcomponent]
    exact connectedComponentIn_subset policy point
  have hpolicy_eq : policy = context ∪ Set.Ioi lower := by
    ext x
    constructor
    · intro hx
      by_cases hx_tail : x ∈ Set.Ioi lower
      · exact Or.inr hx_tail
      · exact Or.inl ⟨hx, hx_tail⟩
    · rintro (hx | hx)
      · exact hx.1
      · exact hcomponent_subset hx
  rcases hderivative context lower hlower_pos with
    ⟨derivativeValue, hderiv, hsign⟩
  refine ⟨derivativeValue, ?_, ?_⟩
  · simpa [gn21Lemma5ComponentTailLowerPath, context] using hderiv
  · rw [hpolicy_eq]
    exact hsign

/--
A positive right derivative within the feasible half-line gives a bounded
strict right improvement.  This is the one-sided calculus needed when an open
interval starts at the source endpoint `0`.
-/
theorem exists_pos_right_improvement_of_hasDerivWithinAt_Ici_zero_pos_lt
    {f : ℝ → ℝ} {derivativeValue delta : ℝ}
    (hderiv : HasDerivWithinAt f derivativeValue (Set.Ici 0) 0)
    (hderivative_pos : 0 < derivativeValue)
    (hdelta_pos : 0 < delta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < delta ∧
      f 0 < f epsilon := by
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_diff, Set.mem_Ici, Set.mem_singleton_iff,
      Set.mem_Ioi]
    constructor
    · rintro ⟨hx_nonneg, hx_ne⟩
      exact lt_of_le_of_ne hx_nonneg (Ne.symm hx_ne)
    · intro hx_pos
      exact ⟨le_of_lt hx_pos, ne_of_gt hx_pos⟩
  have hslope_tendsto :
      Filter.Tendsto (slope f 0) (𝓝[>] 0) (𝓝 derivativeValue) := by
    rw [hasDerivWithinAt_iff_tendsto_slope, hset] at hderiv
    exact hderiv
  have hslope_pos :
      ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < slope f 0 epsilon :=
    hslope_tendsto.eventually (Ioi_mem_nhds hderivative_pos)
  have hepsilon_pos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < epsilon :=
    self_mem_nhdsWithin
  have hepsilon_lt : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), epsilon < delta :=
    nhdsWithin_le_nhds (Iio_mem_nhds hdelta_pos)
  rcases (hepsilon_pos.and (hepsilon_lt.and hslope_pos)).exists with
    ⟨epsilon, hepsilon_pos, hepsilon_lt, hslope_pos⟩
  have hdiff_pos : 0 < f epsilon - f 0 := by
    simp only [slope_def_field, sub_zero] at hslope_pos
    rcases (div_pos_iff.mp hslope_pos) with hpositive | hnegative
    · exact hpositive.1
    · linarith
  exact ⟨epsilon, hepsilon_pos, hepsilon_lt, by linarith⟩

/--
An open feasible policy that is not a right cutoff has a strict local
improvement when its endpoint response is strictly increasing.  The endpoint
calculus is restricted to actual connected components of that policy; no
arbitrary-background union path, improvement, or policy-form conclusion is
assumed as input.
-/
theorem exists_strictlyIncreasing_open_strict_improvement_of_not_form
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hsigma_nonempty : sigma.Nonempty)
    (hnot_form : ¬ lemma5SourcePolicyForm .strictlyIncreasing sigma)
    (hresponse_increasing : StrictMonoOn (response sigma) (Set.Ici 0))
    (hupper_derivative :
      GN21Lemma5ComponentUpperDerivativeCondition Rhat response)
    (hlower_derivative :
      GN21Lemma5ComponentLowerDerivativeCondition Rhat response)
    (hlower_right_derivative :
      GN21Lemma5ComponentLowerRightDerivativeCondition Rhat response) :
    ∃ improved : TripPolicy,
      IsOpen improved ∧ improved ⊆ acceptAllPolicy ∧
        Rhat sigma < Rhat improved := by
  rcases exists_bounded_connectedComponent_of_not_strictlyIncreasing_form
      hsigma_open hsigma_subset hsigma_nonempty hnot_form with
    ⟨point, lower, upper, hpoint, hlower_nonneg, hlower_upper,
      hcomponent_eq⟩
  let context : TripPolicy := sigma \ Set.Ioo lower upper
  have hinterval_subset : Set.Ioo lower upper ⊆ sigma := by
    rw [← hcomponent_eq]
    exact connectedComponentIn_subset sigma point
  have hcontext_open : IsOpen context := by
    dsimp [context]
    rw [← hcomponent_eq]
    exact isOpen_diff_connectedComponentIn hsigma_open point
  have hcontext_subset : context ⊆ acceptAllPolicy := by
    intro x hx
    exact hsigma_subset hx.1
  have hsigma_eq : sigma = context ∪ Set.Ioo lower upper := by
    ext x
    constructor
    · intro hx
      by_cases hx_interval : x ∈ Set.Ioo lower upper
      · exact Or.inr hx_interval
      · exact Or.inl ⟨hx, hx_interval⟩
    · rintro (hx | hx)
      · exact hx.1
      · exact hinterval_subset hx
  have hupper_nonneg : 0 ≤ upper :=
    hlower_nonneg.trans (le_of_lt hlower_upper)
  have hresponse_dichotomy :
      0 < response sigma upper ∨ 0 < -response sigma lower := by
    by_cases hupper_response_pos : 0 < response sigma upper
    · exact Or.inl hupper_response_pos
    · right
      have hresponse_lt : response sigma lower < response sigma upper :=
        hresponse_increasing hlower_nonneg hupper_nonneg hlower_upper
      linarith
  rcases hresponse_dichotomy with hupper_response_pos | hlower_response_pos
  · rcases hupper_derivative hsigma_open hsigma_subset hpoint hcomponent_eq
        hlower_nonneg hlower_upper with
      ⟨derivativeValue, hderiv, hsign⟩
    have hderivative_pos : 0 < derivativeValue :=
      sameStrictSign_pos_left hsign hupper_response_pos
    rcases exists_pos_right_improvement_of_hasDerivAt_pos
        hderiv hderivative_pos with
      ⟨epsilon, hepsilon_pos, himprovement⟩
    let improved : TripPolicy := context ∪ Set.Ioo lower (upper + epsilon)
    refine ⟨improved, ?_, ?_, ?_⟩
    · exact hcontext_open.union isOpen_Ioo
    · exact
        union_ioo_subset_acceptAllPolicy_of_subset_of_left_nonneg
          hcontext_subset hlower_nonneg
    · have hpath_at_upper :
          gn21Lemma5ComponentUpperPath sigma lower upper upper = sigma := by
        simpa [gn21Lemma5ComponentUpperPath, context] using hsigma_eq.symm
      change Rhat sigma < Rhat
        (gn21Lemma5ComponentUpperPath sigma lower upper (upper + epsilon))
      simpa [hpath_at_upper] using himprovement
  · by_cases hlower_zero : lower = 0
    · subst lower
      rcases hlower_right_derivative hsigma_open hsigma_subset hpoint
          hcomponent_eq hlower_upper with
        ⟨derivativeValue, hderiv, hsign⟩
      have hderivative_pos : 0 < derivativeValue :=
        sameStrictSign_pos_left hsign hlower_response_pos
      rcases
          exists_pos_right_improvement_of_hasDerivWithinAt_Ici_zero_pos_lt
            hderiv hderivative_pos hlower_upper with
        ⟨epsilon, hepsilon_pos, hepsilon_upper, himprovement⟩
      let improved : TripPolicy := context ∪ Set.Ioo epsilon upper
      refine ⟨improved, ?_, ?_, ?_⟩
      · exact hcontext_open.union isOpen_Ioo
      · exact
          union_ioo_subset_acceptAllPolicy_of_subset_of_left_nonneg
            hcontext_subset (le_of_lt hepsilon_pos)
      · have hpath_at_lower :
            gn21Lemma5ComponentLowerPath sigma 0 upper 0 = sigma := by
          simpa [gn21Lemma5ComponentLowerPath, context] using hsigma_eq.symm
        change Rhat sigma < Rhat
          (gn21Lemma5ComponentLowerPath sigma 0 upper epsilon)
        simpa [hpath_at_lower] using himprovement
    · have hlower_pos : 0 < lower :=
        lt_of_le_of_ne hlower_nonneg (Ne.symm hlower_zero)
      rcases hlower_derivative hsigma_open hsigma_subset hpoint hcomponent_eq
          hlower_pos hlower_upper with
        ⟨derivativeValue, hderiv, hsign⟩
      have hderivative_pos : 0 < derivativeValue :=
        sameStrictSign_pos_left hsign hlower_response_pos
      rcases exists_pos_right_improvement_of_hasDerivAt_pos_lt
          hderiv hderivative_pos (sub_pos.mpr hlower_upper) with
        ⟨epsilon, hepsilon_pos, hepsilon_lt, himprovement⟩
      let improved : TripPolicy := context ∪ Set.Ioo (lower + epsilon) upper
      refine ⟨improved, ?_, ?_, ?_⟩
      · exact hcontext_open.union isOpen_Ioo
      · exact
          union_ioo_subset_acceptAllPolicy_of_subset_of_left_nonneg
            hcontext_subset (by linarith)
      · have hpath_at_lower :
            gn21Lemma5ComponentLowerPath sigma lower upper lower = sigma := by
          simpa [gn21Lemma5ComponentLowerPath, context] using hsigma_eq.symm
        change Rhat sigma < Rhat
          (gn21Lemma5ComponentLowerPath sigma lower upper (lower + epsilon))
        simpa [hpath_at_lower] using himprovement

/--
Split an open policy at `pivot` and move the lower endpoint of its right-hand
part to `cutoff`.  At `cutoff = pivot` this differs from the original policy
only at the split point.
-/
def gn21InteriorSplitLowerPolicy
    (sigma : TripPolicy) (pivot cutoff : ℝ) : TripPolicy :=
  (sigma ∩ Set.Iio pivot) ∪ (sigma ∩ Set.Ioi cutoff)

theorem gn21InteriorSplitLowerPolicy_open
    {sigma : TripPolicy} (hsigma_open : IsOpen sigma)
    (pivot cutoff : ℝ) :
    IsOpen (gn21InteriorSplitLowerPolicy sigma pivot cutoff) :=
  (hsigma_open.inter isOpen_Iio).union (hsigma_open.inter isOpen_Ioi)

theorem gn21InteriorSplitLowerPolicy_subset
    (sigma : TripPolicy) (pivot cutoff : ℝ) :
    gn21InteriorSplitLowerPolicy sigma pivot cutoff ⊆ sigma := by
  rintro x (hx | hx)
  · exact hx.1
  · exact hx.1

/-- Splitting at the same point preserves a policy up to a singleton. -/
theorem policyAlmostEverywhereEq_interiorSplitLowerPolicy_self
    (mu : Measure TripLength) [NoAtoms mu]
    (sigma : TripPolicy) (pivot : ℝ) :
    policyAlmostEverywhereEq mu sigma
      (gn21InteriorSplitLowerPolicy sigma pivot pivot) := by
  rw [policyAlmostEverywhereEq]
  apply measure_mono_null (t := ({pivot} : Set ℝ))
  · intro x hx
    rw [Set.symmDiff_def] at hx
    rcases hx with hx | hx
    · by_contra hx_ne
      rcases lt_or_gt_of_ne hx_ne with hx_lt | hx_gt
      · exact hx.2 (Or.inl ⟨hx.1, hx_lt⟩)
      · exact hx.2 (Or.inr ⟨hx.1, hx_gt⟩)
    · exact False.elim (hx.2 (gn21InteriorSplitLowerPolicy_subset
        sigma pivot pivot hx.1))
  · exact measure_singleton pivot

/--
A positive derivative of the interior-split lower path gives an open feasible
strict improvement of the original policy.  The reward equality at the split
point is derived from nonatomic a.e. invariance.
-/
theorem exists_open_strict_improvement_of_interiorSplitLower_derivative_pos
    (mu : Measure TripLength) [NoAtoms mu]
    (Rhat : SingleStateReward)
    {sigma : TripPolicy} (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hRhat_ae :
      ∀ {left right : TripPolicy},
        policyAlmostEverywhereEq mu left right → Rhat left = Rhat right)
    (pivot derivativeValue : ℝ)
    (hderiv :
      HasDerivAt
        (fun cutoff => Rhat (gn21InteriorSplitLowerPolicy sigma pivot cutoff))
        derivativeValue pivot)
    (hderivative_pos : 0 < derivativeValue) :
    ∃ improved : TripPolicy,
      IsOpen improved ∧ improved ⊆ acceptAllPolicy ∧
        Rhat sigma < Rhat improved := by
  rcases exists_pos_right_improvement_of_hasDerivAt_pos
      hderiv hderivative_pos with
    ⟨epsilon, hepsilon_pos, himprovement⟩
  let improved : TripPolicy :=
    gn21InteriorSplitLowerPolicy sigma pivot (pivot + epsilon)
  have hsplit_reward :
      Rhat sigma = Rhat (gn21InteriorSplitLowerPolicy sigma pivot pivot) :=
    hRhat_ae
      (policyAlmostEverywhereEq_interiorSplitLowerPolicy_self
        mu sigma pivot)
  refine ⟨improved, ?_, ?_, ?_⟩
  · exact gn21InteriorSplitLowerPolicy_open hsigma_open _ _
  · exact (gn21InteriorSplitLowerPolicy_subset sigma _ _).trans
      hsigma_subset
  · exact hsplit_reward.trans_lt himprovement

/--
Strict local improvement for a non-left-cutoff open policy under a strictly
decreasing response.  Bounded components use their two endpoints; a right
tail whose boundary response is nonpositive is split at an interior point and
then shortened there.  This is the variation missing from a boundary-only
argument.
-/
theorem exists_strictlyDecreasing_open_strict_improvement_of_not_form
    (mu : Measure TripLength) [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hsigma_nonempty : sigma.Nonempty)
    (hnot_form : ¬ lemma5SourcePolicyForm .strictlyDecreasing sigma)
    (hRhat_ae :
      ∀ {left right : TripPolicy},
        policyAlmostEverywhereEq mu left right → Rhat left = Rhat right)
    (hresponse_decreasing : StrictAntiOn (response sigma) (Set.Ici 0))
    (hinterval_upper_derivative :
      GN21Lemma5ComponentUpperDerivativeCondition Rhat response)
    (hinterval_lower_derivative :
      GN21Lemma5ComponentLowerDerivativeCondition Rhat response)
    (htail_lower_derivative :
      GN21Lemma5ComponentTailLowerDerivativeCondition Rhat response)
    (hsplit_lower_derivative :
      ∀ (policy : TripPolicy) (pivot : ℝ),
        IsOpen policy → policy ⊆ acceptAllPolicy →
          pivot ∈ policy →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun cutoff =>
                Rhat (gn21InteriorSplitLowerPolicy policy pivot cutoff))
              derivativeValue pivot ∧
            sameStrictSign derivativeValue (-response policy pivot)) :
    ∃ improved : TripPolicy,
      IsOpen improved ∧ improved ⊆ acceptAllPolicy ∧
        Rhat sigma < Rhat improved := by
  rcases hsigma_nonempty with ⟨point, hpoint⟩
  rcases connectedComponentIn_open_positive_eq_interval_or_rightRay
      hsigma_open hsigma_subset hpoint with
    ⟨lower, hlower_nonneg, hbounded | hrightRay⟩
  · rcases hbounded with ⟨upper, hlower_upper, hcomponent_eq⟩
    let context : TripPolicy := sigma \ Set.Ioo lower upper
    have hinterval_subset : Set.Ioo lower upper ⊆ sigma := by
      rw [← hcomponent_eq]
      exact connectedComponentIn_subset sigma point
    have hcontext_open : IsOpen context := by
      dsimp [context]
      rw [← hcomponent_eq]
      exact isOpen_diff_connectedComponentIn hsigma_open point
    have hcontext_subset : context ⊆ acceptAllPolicy := by
      intro x hx
      exact hsigma_subset hx.1
    have hsigma_eq : sigma = context ∪ Set.Ioo lower upper := by
      ext x
      constructor
      · intro hx
        by_cases hx_interval : x ∈ Set.Ioo lower upper
        · exact Or.inr hx_interval
        · exact Or.inl ⟨hx, hx_interval⟩
      · rintro (hx | hx)
        · exact hx.1
        · exact hinterval_subset hx
    have hupper_nonneg : 0 ≤ upper :=
      hlower_nonneg.trans (le_of_lt hlower_upper)
    by_cases hlower_zero : lower = 0
    · subst lower
      by_cases hsigma_component :
          sigma = connectedComponentIn sigma point
      · exfalso
        apply hnot_form
        let cutoff : NNReal := ⟨upper, le_of_lt hlower_upper⟩
        refine ⟨(cutoff : ℝ≥0∞), ?_⟩
        rw [hsigma_component, hcomponent_eq,
          gn21LeftExtendedCutoffPolicy_coe]
        change Set.Ioo 0 upper = rejectLongTripsPolicy upper
        ext x
        simp [rejectLongTripsPolicy]
      · have hcomponent_subset :
            connectedComponentIn sigma point ⊆ sigma :=
          connectedComponentIn_subset sigma point
        have hsigma_not_subset :
            ¬ sigma ⊆ connectedComponentIn sigma point := by
          intro hsubset
          exact hsigma_component
            (Set.Subset.antisymm hsubset hcomponent_subset)
        rcases Set.not_subset.mp hsigma_not_subset with
          ⟨other, hother_sigma, hother_not_component⟩
        have hother_pos : 0 < other := hsigma_subset hother_sigma
        have hother_not_interval : other ∉ Set.Ioo (0 : ℝ) upper := by
          intro hother_interval
          exact hother_not_component (hcomponent_eq.symm ▸ hother_interval)
        have hupper_le_other : upper ≤ other := by
          exact le_of_not_gt fun hother_upper =>
            hother_not_interval ⟨hother_pos, hother_upper⟩
        obtain ⟨pivot, hpivot_sigma, hupper_pivot⟩ :
            ∃ pivot : ℝ, pivot ∈ sigma ∧ upper < pivot := by
          by_cases hupper_other : upper < other
          · exact ⟨other, hother_sigma, hupper_other⟩
          · have hother_eq : other = upper :=
              le_antisymm (le_of_not_gt hupper_other) hupper_le_other
            rcases mem_nhds_iff_exists_Ioo_subset.mp
                (hsigma_open.mem_nhds hother_sigma) with
              ⟨left, right, hother_mem, hinterval_sigma⟩
            have hupper_right : upper < right := by
              simpa [hother_eq] using hother_mem.2
            rcases exists_between hupper_right with
              ⟨pivot, hupper_pivot, hpivot_right⟩
            have hleft_pivot : left < pivot := by
              exact hother_mem.1.trans_eq hother_eq |>.trans hupper_pivot
            exact ⟨pivot,
              hinterval_sigma ⟨hleft_pivot, hpivot_right⟩,
              hupper_pivot⟩
        have hpivot_nonneg : 0 ≤ pivot :=
          le_of_lt (hsigma_subset hpivot_sigma)
        have hresponse_lt :
            response sigma pivot < response sigma upper :=
          hresponse_decreasing (le_of_lt hlower_upper) hpivot_nonneg
            hupper_pivot
        by_cases hupper_response_pos : 0 < response sigma upper
        · rcases hinterval_upper_derivative hsigma_open hsigma_subset hpoint
              hcomponent_eq (by simp) hlower_upper with
            ⟨derivativeValue, hderiv_local, hsign_local⟩
          have hderiv :
              HasDerivAt (fun x => Rhat (context ∪ Set.Ioo 0 x))
                derivativeValue upper := by
            simpa [gn21Lemma5ComponentUpperPath, context] using hderiv_local
          have hsign :
              sameStrictSign derivativeValue
                (response (context ∪ Set.Ioo 0 upper) upper) := by
            rw [← hsigma_eq]
            exact hsign_local
          have hsign_sigma :
              sameStrictSign derivativeValue (response sigma upper) := by
            rw [hsigma_eq]
            exact hsign
          have hderivative_pos : 0 < derivativeValue :=
            sameStrictSign_pos_left hsign_sigma hupper_response_pos
          rcases exists_pos_right_improvement_of_hasDerivAt_pos
              hderiv hderivative_pos with
            ⟨epsilon, hepsilon_pos, himprovement⟩
          refine ⟨context ∪ Set.Ioo 0 (upper + epsilon), ?_, ?_, ?_⟩
          · exact hcontext_open.union isOpen_Ioo
          · exact
              union_ioo_subset_acceptAllPolicy_of_subset_of_left_nonneg
                hcontext_subset (by simp)
          · rw [hsigma_eq]
            exact himprovement
        · have hpivot_response_neg : response sigma pivot < 0 := by
            linarith
          rcases hsplit_lower_derivative sigma pivot hsigma_open
              hsigma_subset hpivot_sigma with
            ⟨derivativeValue, hderiv, hsign⟩
          have hderivative_pos : 0 < derivativeValue :=
            sameStrictSign_pos_left hsign (by linarith)
          exact
            exists_open_strict_improvement_of_interiorSplitLower_derivative_pos
              mu Rhat hsigma_open hsigma_subset hRhat_ae pivot
              derivativeValue hderiv hderivative_pos
    · have hlower_pos : 0 < lower :=
        lt_of_le_of_ne hlower_nonneg (Ne.symm hlower_zero)
      have hresponse_lt :
          response sigma upper < response sigma lower :=
        hresponse_decreasing (le_of_lt hlower_pos) hupper_nonneg
          hlower_upper
      by_cases hlower_response_pos : 0 < response sigma lower
      · rcases hinterval_lower_derivative hsigma_open hsigma_subset hpoint
            hcomponent_eq hlower_pos hlower_upper with
          ⟨derivativeValue, hderiv_local, hsign_local⟩
        have hderiv :
            HasDerivAt (fun x => Rhat (context ∪ Set.Ioo x upper))
              derivativeValue lower := by
          simpa [gn21Lemma5ComponentLowerPath, context] using hderiv_local
        have hsign :
            sameStrictSign derivativeValue
              (-response (context ∪ Set.Ioo lower upper) lower) := by
          rw [← hsigma_eq]
          exact hsign_local
        have hsign_sigma :
            sameStrictSign derivativeValue (-response sigma lower) := by
          rw [hsigma_eq]
          exact hsign
        have hderivative_neg : derivativeValue < 0 :=
          sameStrictSign_neg_left hsign_sigma (by linarith)
        rcases exists_pos_left_improvement_of_hasDerivAt_neg_lt
            hderiv hderivative_neg hlower_pos with
          ⟨epsilon, hepsilon_pos, hepsilon_lower, himprovement⟩
        refine ⟨context ∪ Set.Ioo (lower - epsilon) upper, ?_, ?_, ?_⟩
        · exact hcontext_open.union isOpen_Ioo
        · exact
            union_ioo_subset_acceptAllPolicy_of_subset_of_left_nonneg
              hcontext_subset (by linarith)
        · rw [hsigma_eq]
          exact himprovement
      · have hupper_response_neg : response sigma upper < 0 := by
          linarith
        rcases hinterval_upper_derivative hsigma_open hsigma_subset hpoint
            hcomponent_eq hlower_nonneg hlower_upper with
          ⟨derivativeValue, hderiv_local, hsign_local⟩
        have hderiv :
            HasDerivAt (fun x => Rhat (context ∪ Set.Ioo lower x))
              derivativeValue upper := by
          simpa [gn21Lemma5ComponentUpperPath, context] using hderiv_local
        have hsign :
            sameStrictSign derivativeValue
              (response (context ∪ Set.Ioo lower upper) upper) := by
          rw [← hsigma_eq]
          exact hsign_local
        have hsign_sigma :
            sameStrictSign derivativeValue (response sigma upper) := by
          rw [hsigma_eq]
          exact hsign
        have hderivative_neg : derivativeValue < 0 :=
          sameStrictSign_neg_left hsign_sigma hupper_response_neg
        rcases exists_pos_left_improvement_of_hasDerivAt_neg_lt
            hderiv hderivative_neg (sub_pos.mpr hlower_upper) with
          ⟨epsilon, hepsilon_pos, hepsilon_width, himprovement⟩
        refine ⟨context ∪ Set.Ioo lower (upper - epsilon), ?_, ?_, ?_⟩
        · exact hcontext_open.union isOpen_Ioo
        · exact
            union_ioo_subset_acceptAllPolicy_of_subset_of_left_nonneg
              hcontext_subset hlower_nonneg
        · rw [hsigma_eq]
          exact himprovement
  · have hcomponent_subset : Set.Ioi lower ⊆ sigma := by
      rw [← hrightRay]
      exact connectedComponentIn_subset sigma point
    by_cases hlower_zero : lower = 0
    · subst lower
      exfalso
      apply hnot_form
      have hsigma_eq_acceptAll : sigma = acceptAllPolicy := by
        apply Set.Subset.antisymm hsigma_subset
        intro x hx
        exact hcomponent_subset hx
      refine ⟨∞, ?_⟩
      simpa [hsigma_eq_acceptAll]
    · have hlower_pos : 0 < lower :=
        lt_of_le_of_ne hlower_nonneg (Ne.symm hlower_zero)
      let context : TripPolicy := sigma \ Set.Ioi lower
      have hcontext_open : IsOpen context := by
        dsimp [context]
        rw [← hrightRay]
        exact isOpen_diff_connectedComponentIn hsigma_open point
      have hcontext_subset : context ⊆ acceptAllPolicy := by
        intro x hx
        exact hsigma_subset hx.1
      have hsigma_eq : sigma = context ∪ Set.Ioi lower := by
        ext x
        constructor
        · intro hx
          by_cases hx_tail : x ∈ Set.Ioi lower
          · exact Or.inr hx_tail
          · exact Or.inl ⟨hx, hx_tail⟩
        · rintro (hx | hx)
          · exact hx.1
          · exact hcomponent_subset hx
      by_cases hlower_response_pos : 0 < response sigma lower
      · rcases htail_lower_derivative hsigma_open hsigma_subset hpoint hrightRay
            hlower_pos with
          ⟨derivativeValue, hderiv_local, hsign_local⟩
        have hderiv :
            HasDerivAt (fun x => Rhat (context ∪ Set.Ioi x))
              derivativeValue lower := by
          simpa [gn21Lemma5ComponentTailLowerPath, context] using hderiv_local
        have hsign :
            sameStrictSign derivativeValue
              (-response (context ∪ Set.Ioi lower) lower) := by
          rw [← hsigma_eq]
          exact hsign_local
        have hsign_sigma :
            sameStrictSign derivativeValue (-response sigma lower) := by
          rw [hsigma_eq]
          exact hsign
        have hderivative_neg : derivativeValue < 0 :=
          sameStrictSign_neg_left hsign_sigma (by linarith)
        rcases exists_pos_left_improvement_of_hasDerivAt_neg_lt
            hderiv hderivative_neg hlower_pos with
          ⟨epsilon, hepsilon_pos, hepsilon_lower, himprovement⟩
        refine ⟨context ∪ Set.Ioi (lower - epsilon), ?_, ?_, ?_⟩
        · exact hcontext_open.union isOpen_Ioi
        · intro x hx
          rcases hx with hx | hx
          · exact hcontext_subset hx
          · have hcutoff_pos : 0 < lower - epsilon := by linarith
            simpa [acceptAllPolicy, positiveTripLengths,
              positiveRealAcceptAll] using hcutoff_pos.trans hx
        · rw [hsigma_eq]
          exact himprovement
      · let pivot : ℝ := lower + 1
        have hlower_pivot : lower < pivot := by
          dsimp [pivot]
          linarith
        have hpivot_sigma : pivot ∈ sigma :=
          hcomponent_subset hlower_pivot
        have hpivot_nonneg : 0 ≤ pivot :=
          le_of_lt (hlower_pos.trans hlower_pivot)
        have hpivot_response_neg : response sigma pivot < 0 := by
          have hresponse_lt :
              response sigma pivot < response sigma lower :=
            hresponse_decreasing (le_of_lt hlower_pos) hpivot_nonneg
              hlower_pivot
          linarith
        rcases hsplit_lower_derivative sigma pivot hsigma_open
            hsigma_subset hpivot_sigma with
          ⟨derivativeValue, hderiv, hsign⟩
        have hderivative_pos : 0 < derivativeValue :=
          sameStrictSign_pos_left hsign (by linarith)
        exact
          exists_open_strict_improvement_of_interiorSplitLower_derivative_pos
            mu Rhat hsigma_open hsigma_subset hRhat_ae pivot
            derivativeValue hderiv hderivative_pos

/-- Strict local improvement for every non-accept-all open policy when the
endpoint response is positive on positive trip lengths. -/
theorem exists_positive_open_strict_improvement_of_not_form
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hsigma_nonempty : sigma.Nonempty)
    (hnot_form : ¬ lemma5SourcePolicyForm .positive sigma)
    (hresponse_positive :
      ∀ u : TripLength, 0 < u → 0 < response sigma u)
    (hinterval_upper_derivative :
      GN21Lemma5ComponentUpperDerivativeCondition Rhat response)
    (htail_lower_derivative :
      GN21Lemma5ComponentTailLowerDerivativeCondition Rhat response) :
    ∃ improved : TripPolicy,
      IsOpen improved ∧ improved ⊆ acceptAllPolicy ∧
        Rhat sigma < Rhat improved := by
  rcases hsigma_nonempty with ⟨point, hpoint⟩
  rcases connectedComponentIn_open_positive_eq_interval_or_rightRay
      hsigma_open hsigma_subset hpoint with
    ⟨lower, hlower_nonneg, hbounded | hrightRay⟩
  · rcases hbounded with ⟨upper, hlower_upper, hcomponent_eq⟩
    let context : TripPolicy := sigma \ Set.Ioo lower upper
    have hinterval_subset : Set.Ioo lower upper ⊆ sigma := by
      rw [← hcomponent_eq]
      exact connectedComponentIn_subset sigma point
    have hcontext_open : IsOpen context := by
      dsimp [context]
      rw [← hcomponent_eq]
      exact isOpen_diff_connectedComponentIn hsigma_open point
    have hcontext_subset : context ⊆ acceptAllPolicy := by
      intro x hx
      exact hsigma_subset hx.1
    have hsigma_eq : sigma = context ∪ Set.Ioo lower upper := by
      ext x
      constructor
      · intro hx
        by_cases hx_interval : x ∈ Set.Ioo lower upper
        · exact Or.inr hx_interval
        · exact Or.inl ⟨hx, hx_interval⟩
      · rintro (hx | hx)
        · exact hx.1
        · exact hinterval_subset hx
    have hupper_pos : 0 < upper :=
      lt_of_le_of_lt hlower_nonneg hlower_upper
    rcases hinterval_upper_derivative hsigma_open hsigma_subset hpoint
        hcomponent_eq hlower_nonneg hlower_upper with
      ⟨derivativeValue, hderiv, hsign⟩
    have hderivative_pos : 0 < derivativeValue :=
      sameStrictSign_pos_left hsign
        (hresponse_positive upper hupper_pos)
    rcases exists_pos_right_improvement_of_hasDerivAt_pos
        hderiv hderivative_pos with
      ⟨epsilon, hepsilon_pos, himprovement⟩
    refine ⟨context ∪ Set.Ioo lower (upper + epsilon), ?_, ?_, ?_⟩
    · exact hcontext_open.union isOpen_Ioo
    · exact
        union_ioo_subset_acceptAllPolicy_of_subset_of_left_nonneg
          hcontext_subset hlower_nonneg
    · have hpath_at_upper :
          gn21Lemma5ComponentUpperPath sigma lower upper upper = sigma := by
        simpa [gn21Lemma5ComponentUpperPath, context] using hsigma_eq.symm
      change Rhat sigma < Rhat
        (gn21Lemma5ComponentUpperPath sigma lower upper (upper + epsilon))
      simpa [hpath_at_upper] using himprovement
  · have hcomponent_subset : Set.Ioi lower ⊆ sigma := by
      rw [← hrightRay]
      exact connectedComponentIn_subset sigma point
    by_cases hlower_zero : lower = 0
    · subst lower
      exfalso
      apply hnot_form
      have hsigma_eq_acceptAll : sigma = acceptAllPolicy := by
        apply Set.Subset.antisymm hsigma_subset
        exact hcomponent_subset
      exact hsigma_eq_acceptAll
    · have hlower_pos : 0 < lower :=
        lt_of_le_of_ne hlower_nonneg (Ne.symm hlower_zero)
      let context : TripPolicy := sigma \ Set.Ioi lower
      have hcontext_open : IsOpen context := by
        dsimp [context]
        rw [← hrightRay]
        exact isOpen_diff_connectedComponentIn hsigma_open point
      have hcontext_subset : context ⊆ acceptAllPolicy := by
        intro x hx
        exact hsigma_subset hx.1
      have hsigma_eq : sigma = context ∪ Set.Ioi lower := by
        ext x
        constructor
        · intro hx
          by_cases hx_tail : x ∈ Set.Ioi lower
          · exact Or.inr hx_tail
          · exact Or.inl ⟨hx, hx_tail⟩
        · rintro (hx | hx)
          · exact hx.1
          · exact hcomponent_subset hx
      rcases htail_lower_derivative hsigma_open hsigma_subset hpoint hrightRay
          hlower_pos with
        ⟨derivativeValue, hderiv, hsign⟩
      have hderivative_neg : derivativeValue < 0 :=
        sameStrictSign_neg_left hsign
          (by linarith [hresponse_positive lower hlower_pos])
      rcases exists_pos_left_improvement_of_hasDerivAt_neg_lt
          hderiv hderivative_neg hlower_pos with
        ⟨epsilon, hepsilon_pos, hepsilon_lower, himprovement⟩
      refine ⟨context ∪ Set.Ioi (lower - epsilon), ?_, ?_, ?_⟩
      · exact hcontext_open.union isOpen_Ioi
      · apply union_subset_acceptAllPolicy hcontext_subset
        intro x hx
        have hcutoff_pos : 0 < lower - epsilon := by linarith
        simpa [acceptAllPolicy, positiveTripLengths,
          positiveRealAcceptAll] using hcutoff_pos.trans hx
      · have hpath_at_lower :
            gn21Lemma5ComponentTailLowerPath sigma lower lower = sigma := by
          simpa [gn21Lemma5ComponentTailLowerPath, context] using hsigma_eq.symm
        change Rhat sigma < Rhat
          (gn21Lemma5ComponentTailLowerPath sigma lower (lower - epsilon))
        simpa [hpath_at_lower] using himprovement

/-- Strict local improvement for a non-single-interval open policy under a
strictly quasi-concave response. -/
theorem exists_strictlyQuasiConcave_open_strict_improvement_of_not_form
    (mu : Measure TripLength) [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hsigma_nonempty : sigma.Nonempty)
    (hnot_form : ¬ lemma5SourcePolicyForm .strictlyQuasiConcave sigma)
    (hRhat_ae :
      ∀ {left right : TripPolicy},
        policyAlmostEverywhereEq mu left right → Rhat left = Rhat right)
    (hresponse_quasiConcave :
      strictQuasiConcaveOnPositive (response sigma))
    (hinterval_upper_derivative :
      GN21Lemma5ComponentUpperDerivativeCondition Rhat response)
    (hsplit_lower_derivative :
      ∀ (policy : TripPolicy) (pivot : ℝ),
        IsOpen policy → policy ⊆ acceptAllPolicy →
          pivot ∈ policy →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun cutoff =>
                Rhat (gn21InteriorSplitLowerPolicy policy pivot cutoff))
              derivativeValue pivot ∧
            sameStrictSign derivativeValue (-response policy pivot)) :
    ∃ improved : TripPolicy,
      IsOpen improved ∧ improved ⊆ acceptAllPolicy ∧
        Rhat sigma < Rhat improved := by
  rcases hsigma_nonempty with ⟨point, hpoint⟩
  rcases connectedComponentIn_open_positive_eq_interval_or_rightRay
      hsigma_open hsigma_subset hpoint with
    ⟨pointLower, hpointLower_nonneg, hpointClass⟩
  have hsigma_ne_pointComponent :
      sigma ≠ connectedComponentIn sigma point := by
    intro hsigma_component
    apply hnot_form
    rcases hpointClass with hpointBounded | hpointRightRay
    · let lowerNN : NNReal := ⟨pointLower, hpointLower_nonneg⟩
      rcases hpointBounded with
        ⟨pointUpper, hpointLower_upper, hpointComponent⟩
      let upperNN : NNReal :=
        ⟨pointUpper,
          hpointLower_nonneg.trans (le_of_lt hpointLower_upper)⟩
      refine ⟨(lowerNN : ℝ≥0∞), (upperNN : ℝ≥0∞), ?_⟩
      rw [hsigma_component, hpointComponent]
      exact (gn21ExtendedMiddlePolicy_coe_coe_eq_Ioo lowerNN upperNN).symm
    · let lowerNN : NNReal := ⟨pointLower, hpointLower_nonneg⟩
      refine ⟨(lowerNN : ℝ≥0∞), ∞, ?_⟩
      rw [hsigma_component, hpointRightRay]
      exact (gn21ExtendedMiddlePolicy_coe_top_eq_Ioi lowerNN).symm
  have hpointComponent_subset :
      connectedComponentIn sigma point ⊆ sigma :=
    connectedComponentIn_subset sigma point
  have hsigma_not_subset_pointComponent :
      ¬ sigma ⊆ connectedComponentIn sigma point := by
    intro hsubset
    exact hsigma_ne_pointComponent
      (Set.Subset.antisymm hsubset hpointComponent_subset)
  rcases Set.not_subset.mp hsigma_not_subset_pointComponent with
    ⟨other, hother_sigma, hother_not_pointComponent⟩
  have hpoint_ne_other : point ≠ other := by
    intro hpoint_other
    apply hother_not_pointComponent
    rw [← hpoint_other]
    exact mem_connectedComponentIn hpoint
  have hpoint_not_otherComponent :
      point ∉ connectedComponentIn sigma other := by
    intro hpoint_otherComponent
    have hcomponents_eq :
        connectedComponentIn sigma other =
          connectedComponentIn sigma point :=
      connectedComponentIn_eq hpoint_otherComponent
    exact hother_not_pointComponent
      (hcomponents_eq ▸ mem_connectedComponentIn hother_sigma)
  obtain ⟨leftPoint, rightPoint, hleft_sigma, hright_sigma,
      hleft_right, hright_not_leftComponent⟩ :
      ∃ leftPoint rightPoint : ℝ,
        leftPoint ∈ sigma ∧ rightPoint ∈ sigma ∧
          leftPoint < rightPoint ∧
          rightPoint ∉ connectedComponentIn sigma leftPoint := by
    rcases lt_or_gt_of_ne hpoint_ne_other with hpoint_other | hother_point
    · exact ⟨point, other, hpoint, hother_sigma, hpoint_other,
        hother_not_pointComponent⟩
    · exact ⟨other, point, hother_sigma, hpoint, hother_point,
        hpoint_not_otherComponent⟩
  rcases connectedComponentIn_open_positive_eq_interval_or_rightRay
      hsigma_open hsigma_subset hleft_sigma with
    ⟨lower, hlower_nonneg, hbounded | hrightRay⟩
  · rcases hbounded with ⟨upper, hlower_upper, hcomponent_eq⟩
    have hleft_component : leftPoint ∈ Set.Ioo lower upper := by
      rw [← hcomponent_eq]
      exact mem_connectedComponentIn hleft_sigma
    have hright_not_interval : rightPoint ∉ Set.Ioo lower upper := by
      intro hright_interval
      exact hright_not_leftComponent (hcomponent_eq.symm ▸ hright_interval)
    have hlower_right : lower < rightPoint :=
      hleft_component.1.trans hleft_right
    have hupper_le_right : upper ≤ rightPoint := by
      exact le_of_not_gt fun hright_upper =>
        hright_not_interval ⟨hlower_right, hright_upper⟩
    obtain ⟨pivot, hpivot_sigma, hupper_pivot⟩ :
        ∃ pivot : ℝ, pivot ∈ sigma ∧ upper < pivot := by
      by_cases hupper_right : upper < rightPoint
      · exact ⟨rightPoint, hright_sigma, hupper_right⟩
      · have hright_eq : rightPoint = upper :=
          le_antisymm (le_of_not_gt hupper_right) hupper_le_right
        rcases mem_nhds_iff_exists_Ioo_subset.mp
            (hsigma_open.mem_nhds hright_sigma) with
          ⟨left, right, hright_mem, hinterval_sigma⟩
        have hupper_right' : upper < right := by
          simpa [hright_eq] using hright_mem.2
        rcases exists_between hupper_right' with
          ⟨pivot, hupper_pivot, hpivot_right⟩
        have hleft_pivot : left < pivot := by
          have hleft_upper : left < upper := by
            simpa [hright_eq] using hright_mem.1
          exact hleft_upper.trans hupper_pivot
        exact ⟨pivot,
          hinterval_sigma ⟨hleft_pivot, hpivot_right⟩,
          hupper_pivot⟩
    have hleftPoint_pos : 0 < leftPoint := hsigma_subset hleft_sigma
    have hpivot_nonneg : 0 ≤ pivot :=
      le_of_lt (hsigma_subset hpivot_sigma)
    have hleftPoint_upper : leftPoint < upper := hleft_component.2
    have hsign_trichotomy :
        0 < response sigma upper ∨
          response sigma leftPoint < 0 ∨
            response sigma pivot < 0 :=
      lemma5_strictQuasiConcave_two_interval_endpoint_sign_trichotomy
        (response sigma) hresponse_quasiConcave hleftPoint_pos
        hleftPoint_upper hupper_pivot
    let context : TripPolicy := sigma \ Set.Ioo lower upper
    have hinterval_subset : Set.Ioo lower upper ⊆ sigma := by
      rw [← hcomponent_eq]
      exact connectedComponentIn_subset sigma leftPoint
    have hcontext_open : IsOpen context := by
      dsimp [context]
      rw [← hcomponent_eq]
      exact isOpen_diff_connectedComponentIn hsigma_open leftPoint
    have hcontext_subset : context ⊆ acceptAllPolicy := by
      intro x hx
      exact hsigma_subset hx.1
    have hsigma_eq : sigma = context ∪ Set.Ioo lower upper := by
      ext x
      constructor
      · intro hx
        by_cases hx_interval : x ∈ Set.Ioo lower upper
        · exact Or.inr hx_interval
        · exact Or.inl ⟨hx, hx_interval⟩
      · rintro (hx | hx)
        · exact hx.1
        · exact hinterval_subset hx
    rcases hsign_trichotomy with hupper_pos | hleft_neg | hpivot_neg
    · rcases hinterval_upper_derivative hsigma_open hsigma_subset hleft_sigma
          hcomponent_eq hlower_nonneg hlower_upper with
        ⟨derivativeValue, hderiv_local, hsign_local⟩
      have hderiv :
          HasDerivAt (fun x => Rhat (context ∪ Set.Ioo lower x))
            derivativeValue upper := by
        simpa [gn21Lemma5ComponentUpperPath, context] using hderiv_local
      have hsign :
          sameStrictSign derivativeValue
            (response (context ∪ Set.Ioo lower upper) upper) := by
        rw [← hsigma_eq]
        exact hsign_local
      have hsign_sigma :
          sameStrictSign derivativeValue (response sigma upper) := by
        rw [hsigma_eq]
        exact hsign
      have hderivative_pos : 0 < derivativeValue :=
        sameStrictSign_pos_left hsign_sigma hupper_pos
      rcases exists_pos_right_improvement_of_hasDerivAt_pos
          hderiv hderivative_pos with
        ⟨epsilon, hepsilon_pos, himprovement⟩
      refine ⟨context ∪ Set.Ioo lower (upper + epsilon), ?_, ?_, ?_⟩
      · exact hcontext_open.union isOpen_Ioo
      · exact
          union_ioo_subset_acceptAllPolicy_of_subset_of_left_nonneg
            hcontext_subset hlower_nonneg
      · rw [hsigma_eq]
        exact himprovement
    · rcases hsplit_lower_derivative sigma leftPoint hsigma_open
          hsigma_subset hleft_sigma with
        ⟨derivativeValue, hderiv, hsign⟩
      have hderivative_pos : 0 < derivativeValue :=
        sameStrictSign_pos_left hsign (by linarith)
      exact
        exists_open_strict_improvement_of_interiorSplitLower_derivative_pos
          mu Rhat hsigma_open hsigma_subset hRhat_ae leftPoint
          derivativeValue hderiv hderivative_pos
    · rcases hsplit_lower_derivative sigma pivot hsigma_open
          hsigma_subset hpivot_sigma with
        ⟨derivativeValue, hderiv, hsign⟩
      have hderivative_pos : 0 < derivativeValue :=
        sameStrictSign_pos_left hsign (by linarith)
      exact
        exists_open_strict_improvement_of_interiorSplitLower_derivative_pos
          mu Rhat hsigma_open hsigma_subset hRhat_ae pivot
          derivativeValue hderiv hderivative_pos
  · exfalso
    have hleft_tail : leftPoint ∈ Set.Ioi lower := by
      rw [← hrightRay]
      exact mem_connectedComponentIn hleft_sigma
    apply hright_not_leftComponent
    rw [hrightRay]
    exact hleft_tail.trans hleft_right

theorem gn21ExtendedTwoTailPolicy_coe_top_eq_Ioo (upper : NNReal) :
    gn21ExtendedTwoTailPolicy (upper : ℝ≥0∞) ∞ =
      Set.Ioo 0 (upper : ℝ) := by
  rw [gn21ExtendedTwoTailPolicy, gn21RightExtendedCutoffPolicy_top,
    Set.union_empty, gn21LeftExtendedCutoffPolicy_coe]
  ext x
  simp [rejectLongTripsPolicy]

theorem gn21ExtendedTwoTailPolicy_zero_coe_eq_Ioi (lower : NNReal) :
    gn21ExtendedTwoTailPolicy 0 (lower : ℝ≥0∞) =
      Set.Ioi (lower : ℝ) := by
  rw [gn21ExtendedTwoTailPolicy, gn21RightExtendedCutoffPolicy_coe]
  change rejectLongTripsPolicy 0 ∪
      rejectShortTripsPolicy (lower : ℝ) = Set.Ioi (lower : ℝ)
  ext x
  constructor
  · rintro (hx | hx)
    · rcases hx with ⟨hx_pos, hx_neg⟩
      change 0 < x at hx_pos
      change x < 0 at hx_neg
      exact False.elim ((not_lt_of_ge (le_of_lt hx_pos)) hx_neg)
    · change 0 < x ∧ lower < x at hx
      exact hx.2
  · intro hx
    exact Or.inr ⟨lt_of_le_of_lt lower.property hx, hx⟩

theorem gn21ExtendedTwoTailPolicy_coe_coe_eq_Ioo_union_Ioi
    (upper lower : NNReal) :
    gn21ExtendedTwoTailPolicy (upper : ℝ≥0∞) (lower : ℝ≥0∞) =
      Set.Ioo 0 (upper : ℝ) ∪ Set.Ioi (lower : ℝ) := by
  rw [gn21ExtendedTwoTailPolicy, gn21LeftExtendedCutoffPolicy_coe,
    gn21RightExtendedCutoffPolicy_coe]
  ext x
  constructor
  · rintro (hx | hx)
    · exact Or.inl hx
    · exact Or.inr hx.2
  · rintro (hx | hx)
    · exact Or.inl hx
    · exact Or.inr ⟨lt_of_le_of_lt lower.property hx, hx⟩

/-- Two bounded open components with lower endpoint zero must coincide. -/
theorem connectedComponentIn_eq_of_eq_Ioo_zero
    {sigma : TripPolicy} {leftPoint rightPoint leftUpper rightUpper : ℝ}
    (hleftUpper_pos : 0 < leftUpper)
    (hrightUpper_pos : 0 < rightUpper)
    (hleft :
      connectedComponentIn sigma leftPoint = Set.Ioo 0 leftUpper)
    (hright :
      connectedComponentIn sigma rightPoint = Set.Ioo 0 rightUpper) :
    connectedComponentIn sigma leftPoint =
      connectedComponentIn sigma rightPoint := by
  let common : ℝ := min leftUpper rightUpper / 2
  have hmin_pos : 0 < min leftUpper rightUpper :=
    lt_min hleftUpper_pos hrightUpper_pos
  have hcommon_pos : 0 < common := by
    dsimp [common]
    linarith
  have hcommon_left : common < leftUpper := by
    dsimp [common]
    have hmin_le := min_le_left leftUpper rightUpper
    linarith
  have hcommon_right : common < rightUpper := by
    dsimp [common]
    have hmin_le := min_le_right leftUpper rightUpper
    linarith
  have hcommon_leftComponent :
      common ∈ connectedComponentIn sigma leftPoint := by
    rw [hleft]
    exact ⟨hcommon_pos, hcommon_left⟩
  have hcommon_rightComponent :
      common ∈ connectedComponentIn sigma rightPoint := by
    rw [hright]
    exact ⟨hcommon_pos, hcommon_right⟩
  exact
    (connectedComponentIn_eq hcommon_leftComponent).trans
      (connectedComponentIn_eq hcommon_rightComponent).symm

/-- Two right-ray connected components must coincide. -/
theorem connectedComponentIn_eq_of_eq_Ioi
    {sigma : TripPolicy} {leftPoint rightPoint leftLower rightLower : ℝ}
    (hleft : connectedComponentIn sigma leftPoint = Set.Ioi leftLower)
    (hright : connectedComponentIn sigma rightPoint = Set.Ioi rightLower) :
    connectedComponentIn sigma leftPoint =
      connectedComponentIn sigma rightPoint := by
  let common : ℝ := max leftLower rightLower + 1
  have hcommon_left : leftLower < common := by
    dsimp [common]
    calc
      leftLower ≤ max leftLower rightLower := le_max_left _ _
      _ < max leftLower rightLower + 1 := by linarith
  have hcommon_right : rightLower < common := by
    dsimp [common]
    calc
      rightLower ≤ max leftLower rightLower := le_max_right _ _
      _ < max leftLower rightLower + 1 := by linarith
  have hcommon_leftComponent :
      common ∈ connectedComponentIn sigma leftPoint := by
    rw [hleft]
    exact hcommon_left
  have hcommon_rightComponent :
      common ∈ connectedComponentIn sigma rightPoint := by
    rw [hright]
    exact hcommon_right
  exact
    (connectedComponentIn_eq hcommon_leftComponent).trans
      (connectedComponentIn_eq hcommon_rightComponent).symm

/--
If an open feasible policy is not a two-tail source form, one of its connected
components is a bounded interval whose lower endpoint is strictly positive.
-/
theorem exists_positiveLower_bounded_component_of_not_quasiConvex_form
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hsigma_nonempty : sigma.Nonempty)
    (hnot_form : ¬ lemma5SourcePolicyForm .strictlyQuasiConvex sigma) :
    ∃ point lower upper : ℝ,
      point ∈ sigma ∧ 0 < lower ∧ lower < upper ∧
        connectedComponentIn sigma point = Set.Ioo lower upper := by
  by_contra hnone
  have hclass : ∀ point : ℝ, point ∈ sigma →
      (∃ upper : ℝ, 0 < upper ∧
        connectedComponentIn sigma point = Set.Ioo 0 upper) ∨
      (∃ lower : ℝ, 0 ≤ lower ∧
        connectedComponentIn sigma point = Set.Ioi lower) := by
    intro point hpoint
    rcases connectedComponentIn_open_positive_eq_interval_or_rightRay
        hsigma_open hsigma_subset hpoint with
      ⟨lower, hlower_nonneg, hbounded | hrightRay⟩
    · rcases hbounded with ⟨upper, hlower_upper, hcomponent⟩
      have hlower_zero : lower = 0 := by
        by_contra hlower_ne
        have hlower_pos : 0 < lower :=
          lt_of_le_of_ne hlower_nonneg (Ne.symm hlower_ne)
        exact hnone ⟨point, lower, upper, hpoint, hlower_pos,
          hlower_upper, hcomponent⟩
      subst lower
      exact Or.inl ⟨upper, hlower_upper, hcomponent⟩
    · exact Or.inr ⟨lower, hlower_nonneg, hrightRay⟩
  rcases hsigma_nonempty with ⟨base, hbase_sigma⟩
  rcases hclass base hbase_sigma with hbaseBounded | hbaseRay
  · rcases hbaseBounded with ⟨baseUpper, hbaseUpper_pos, hbaseComponent⟩
    by_cases hexistsRay : ∃ point : ℝ, point ∈ sigma ∧
        ∃ lower : ℝ, 0 ≤ lower ∧
          connectedComponentIn sigma point = Set.Ioi lower
    · rcases hexistsRay with
        ⟨rayPoint, hrayPoint_sigma, rayLower, hrayLower_nonneg,
          hrayComponent⟩
      have hsigma_eq :
          sigma = Set.Ioo 0 baseUpper ∪ Set.Ioi rayLower := by
        apply Set.Subset.antisymm
        · intro x hx
          rcases hclass x hx with hbounded | hray
          · rcases hbounded with ⟨upper, hupper_pos, hcomponent⟩
            have hcomponents_eq :=
              connectedComponentIn_eq_of_eq_Ioo_zero
                hupper_pos hbaseUpper_pos hcomponent hbaseComponent
            left
            rw [← hbaseComponent, ← hcomponents_eq]
            exact mem_connectedComponentIn hx
          · rcases hray with ⟨lower, hlower_nonneg, hcomponent⟩
            have hcomponents_eq :=
              connectedComponentIn_eq_of_eq_Ioi hcomponent hrayComponent
            right
            rw [← hrayComponent, ← hcomponents_eq]
            exact mem_connectedComponentIn hx
        · intro x hx
          change x ∈ Set.Ioo 0 baseUpper ∨ x ∈ Set.Ioi rayLower at hx
          rcases hx with hx | hx
          · apply connectedComponentIn_subset sigma base
            rw [hbaseComponent]
            exact hx
          · apply connectedComponentIn_subset sigma rayPoint
            rw [hrayComponent]
            exact hx
      apply hnot_form
      let upperNN : NNReal := ⟨baseUpper, le_of_lt hbaseUpper_pos⟩
      let lowerNN : NNReal := ⟨rayLower, hrayLower_nonneg⟩
      refine ⟨(upperNN : ℝ≥0∞), (lowerNN : ℝ≥0∞), ?_⟩
      rw [hsigma_eq]
      exact
        (gn21ExtendedTwoTailPolicy_coe_coe_eq_Ioo_union_Ioi
          upperNN lowerNN).symm
    · have hsigma_eq : sigma = Set.Ioo 0 baseUpper := by
        apply Set.Subset.antisymm
        · intro x hx
          rcases hclass x hx with hbounded | hray
          · rcases hbounded with ⟨upper, hupper_pos, hcomponent⟩
            have hcomponents_eq :=
              connectedComponentIn_eq_of_eq_Ioo_zero
                hupper_pos hbaseUpper_pos hcomponent hbaseComponent
            rw [← hbaseComponent, ← hcomponents_eq]
            exact mem_connectedComponentIn hx
          · rcases hray with ⟨lower, hlower_nonneg, hcomponent⟩
            exact False.elim (hexistsRay ⟨x, hx, lower,
              hlower_nonneg, hcomponent⟩)
        · intro x hx
          apply connectedComponentIn_subset sigma base
          rw [hbaseComponent]
          exact hx
      apply hnot_form
      let upperNN : NNReal := ⟨baseUpper, le_of_lt hbaseUpper_pos⟩
      refine ⟨(upperNN : ℝ≥0∞), ∞, ?_⟩
      rw [hsigma_eq]
      exact (gn21ExtendedTwoTailPolicy_coe_top_eq_Ioo upperNN).symm
  · rcases hbaseRay with
      ⟨baseLower, hbaseLower_nonneg, hbaseComponent⟩
    by_cases hexistsBounded : ∃ point : ℝ, point ∈ sigma ∧
        ∃ upper : ℝ, 0 < upper ∧
          connectedComponentIn sigma point = Set.Ioo 0 upper
    · rcases hexistsBounded with
        ⟨boundedPoint, hboundedPoint_sigma, boundedUpper,
          hboundedUpper_pos, hboundedComponent⟩
      have hsigma_eq :
          sigma = Set.Ioo 0 boundedUpper ∪ Set.Ioi baseLower := by
        apply Set.Subset.antisymm
        · intro x hx
          rcases hclass x hx with hbounded | hray
          · rcases hbounded with ⟨upper, hupper_pos, hcomponent⟩
            have hcomponents_eq :=
              connectedComponentIn_eq_of_eq_Ioo_zero
                hupper_pos hboundedUpper_pos hcomponent hboundedComponent
            left
            rw [← hboundedComponent, ← hcomponents_eq]
            exact mem_connectedComponentIn hx
          · rcases hray with ⟨lower, hlower_nonneg, hcomponent⟩
            have hcomponents_eq :=
              connectedComponentIn_eq_of_eq_Ioi hcomponent hbaseComponent
            right
            rw [← hbaseComponent, ← hcomponents_eq]
            exact mem_connectedComponentIn hx
        · intro x hx
          change x ∈ Set.Ioo 0 boundedUpper ∨ x ∈ Set.Ioi baseLower at hx
          rcases hx with hx | hx
          · apply connectedComponentIn_subset sigma boundedPoint
            rw [hboundedComponent]
            exact hx
          · apply connectedComponentIn_subset sigma base
            rw [hbaseComponent]
            exact hx
      apply hnot_form
      let upperNN : NNReal :=
        ⟨boundedUpper, le_of_lt hboundedUpper_pos⟩
      let lowerNN : NNReal := ⟨baseLower, hbaseLower_nonneg⟩
      refine ⟨(upperNN : ℝ≥0∞), (lowerNN : ℝ≥0∞), ?_⟩
      rw [hsigma_eq]
      exact
        (gn21ExtendedTwoTailPolicy_coe_coe_eq_Ioo_union_Ioi
          upperNN lowerNN).symm
    · have hsigma_eq : sigma = Set.Ioi baseLower := by
        apply Set.Subset.antisymm
        · intro x hx
          rcases hclass x hx with hbounded | hray
          · rcases hbounded with ⟨upper, hupper_pos, hcomponent⟩
            exact False.elim (hexistsBounded ⟨x, hx, upper,
              hupper_pos, hcomponent⟩)
          · rcases hray with ⟨lower, hlower_nonneg, hcomponent⟩
            have hcomponents_eq :=
              connectedComponentIn_eq_of_eq_Ioi hcomponent hbaseComponent
            rw [← hbaseComponent, ← hcomponents_eq]
            exact mem_connectedComponentIn hx
        · intro x hx
          apply connectedComponentIn_subset sigma base
          rw [hbaseComponent]
          exact hx
      apply hnot_form
      let lowerNN : NNReal := ⟨baseLower, hbaseLower_nonneg⟩
      refine ⟨0, (lowerNN : ℝ≥0∞), ?_⟩
      rw [hsigma_eq]
      exact (gn21ExtendedTwoTailPolicy_zero_coe_eq_Ioi lowerNN).symm

/-- Strict local improvement for a non-two-tail open policy under a strictly
quasi-convex response. -/
theorem exists_strictlyQuasiConvex_open_strict_improvement_of_not_form
    (mu : Measure TripLength) [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hsigma_nonempty : sigma.Nonempty)
    (hnot_form : ¬ lemma5SourcePolicyForm .strictlyQuasiConvex sigma)
    (hRhat_ae :
      ∀ {left right : TripPolicy},
        policyAlmostEverywhereEq mu left right → Rhat left = Rhat right)
    (hresponse_quasiConvex :
      strictQuasiConvexOnPositive (response sigma))
    (hinterval_upper_derivative :
      GN21Lemma5ComponentUpperDerivativeCondition Rhat response)
    (hinterval_lower_derivative :
      GN21Lemma5ComponentLowerDerivativeCondition Rhat response)
    (hsplit_lower_derivative :
      ∀ (policy : TripPolicy) (pivot : ℝ),
        IsOpen policy → policy ⊆ acceptAllPolicy →
          pivot ∈ policy →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun cutoff =>
                Rhat (gn21InteriorSplitLowerPolicy policy pivot cutoff))
              derivativeValue pivot ∧
            sameStrictSign derivativeValue (-response policy pivot)) :
    ∃ improved : TripPolicy,
      IsOpen improved ∧ improved ⊆ acceptAllPolicy ∧
        Rhat sigma < Rhat improved := by
  rcases exists_positiveLower_bounded_component_of_not_quasiConvex_form
      hsigma_open hsigma_subset hsigma_nonempty hnot_form with
    ⟨point, lower, upper, hpoint, hlower_pos, hlower_upper,
      hcomponent_eq⟩
  let context : TripPolicy := sigma \ Set.Ioo lower upper
  have hinterval_subset : Set.Ioo lower upper ⊆ sigma := by
    rw [← hcomponent_eq]
    exact connectedComponentIn_subset sigma point
  have hcontext_open : IsOpen context := by
    dsimp [context]
    rw [← hcomponent_eq]
    exact isOpen_diff_connectedComponentIn hsigma_open point
  have hcontext_subset : context ⊆ acceptAllPolicy := by
    intro x hx
    exact hsigma_subset hx.1
  have hsigma_eq : sigma = context ∪ Set.Ioo lower upper := by
    ext x
    constructor
    · intro hx
      by_cases hx_interval : x ∈ Set.Ioo lower upper
      · exact Or.inr hx_interval
      · exact Or.inl ⟨hx, hx_interval⟩
    · rintro (hx | hx)
      · exact hx.1
      · exact hinterval_subset hx
  have hlower_nonneg : 0 ≤ lower := le_of_lt hlower_pos
  by_cases hlower_response_pos : 0 < response sigma lower
  · rcases hinterval_lower_derivative hsigma_open hsigma_subset hpoint
        hcomponent_eq hlower_pos hlower_upper with
      ⟨derivativeValue, hderiv_local, hsign_local⟩
    have hderiv :
        HasDerivAt (fun x => Rhat (context ∪ Set.Ioo x upper))
          derivativeValue lower := by
      simpa [gn21Lemma5ComponentLowerPath, context] using hderiv_local
    have hsign :
        sameStrictSign derivativeValue
          (-response (context ∪ Set.Ioo lower upper) lower) := by
      rw [← hsigma_eq]
      exact hsign_local
    have hsign_sigma :
        sameStrictSign derivativeValue (-response sigma lower) := by
      rw [hsigma_eq]
      exact hsign
    have hderivative_neg : derivativeValue < 0 :=
      sameStrictSign_neg_left hsign_sigma (by linarith)
    rcases exists_pos_left_improvement_of_hasDerivAt_neg_lt
        hderiv hderivative_neg hlower_pos with
      ⟨epsilon, hepsilon_pos, hepsilon_lower, himprovement⟩
    refine ⟨context ∪ Set.Ioo (lower - epsilon) upper, ?_, ?_, ?_⟩
    · exact hcontext_open.union isOpen_Ioo
    · exact
        union_ioo_subset_acceptAllPolicy_of_subset_of_left_nonneg
          hcontext_subset (by linarith)
    · rw [hsigma_eq]
      exact himprovement
  · by_cases hupper_response_pos : 0 < response sigma upper
    · rcases hinterval_upper_derivative hsigma_open hsigma_subset hpoint
          hcomponent_eq hlower_nonneg hlower_upper with
        ⟨derivativeValue, hderiv_local, hsign_local⟩
      have hderiv :
          HasDerivAt (fun x => Rhat (context ∪ Set.Ioo lower x))
            derivativeValue upper := by
        simpa [gn21Lemma5ComponentUpperPath, context] using hderiv_local
      have hsign :
          sameStrictSign derivativeValue
            (response (context ∪ Set.Ioo lower upper) upper) := by
        rw [← hsigma_eq]
        exact hsign_local
      have hsign_sigma :
          sameStrictSign derivativeValue (response sigma upper) := by
        rw [hsigma_eq]
        exact hsign
      have hderivative_pos : 0 < derivativeValue :=
        sameStrictSign_pos_left hsign_sigma hupper_response_pos
      rcases exists_pos_right_improvement_of_hasDerivAt_pos
          hderiv hderivative_pos with
        ⟨epsilon, hepsilon_pos, himprovement⟩
      refine ⟨context ∪ Set.Ioo lower (upper + epsilon), ?_, ?_, ?_⟩
      · exact hcontext_open.union isOpen_Ioo
      · exact
          union_ioo_subset_acceptAllPolicy_of_subset_of_left_nonneg
            hcontext_subset hlower_nonneg
      · rw [hsigma_eq]
        exact himprovement
    · by_cases hlower_response_neg : response sigma lower < 0
      · rcases hinterval_lower_derivative hsigma_open hsigma_subset hpoint
            hcomponent_eq hlower_pos hlower_upper with
          ⟨derivativeValue, hderiv_local, hsign_local⟩
        have hderiv :
            HasDerivAt (fun x => Rhat (context ∪ Set.Ioo x upper))
              derivativeValue lower := by
          simpa [gn21Lemma5ComponentLowerPath, context] using hderiv_local
        have hsign :
            sameStrictSign derivativeValue
              (-response (context ∪ Set.Ioo lower upper) lower) := by
          rw [← hsigma_eq]
          exact hsign_local
        have hsign_sigma :
            sameStrictSign derivativeValue (-response sigma lower) := by
          rw [hsigma_eq]
          exact hsign
        have hderivative_pos : 0 < derivativeValue :=
          sameStrictSign_pos_left hsign_sigma (by linarith)
        rcases exists_pos_right_improvement_of_hasDerivAt_pos_lt
            hderiv hderivative_pos (sub_pos.mpr hlower_upper) with
          ⟨epsilon, hepsilon_pos, hepsilon_width, himprovement⟩
        refine ⟨context ∪ Set.Ioo (lower + epsilon) upper, ?_, ?_, ?_⟩
        · exact hcontext_open.union isOpen_Ioo
        · exact
            union_ioo_subset_acceptAllPolicy_of_subset_of_left_nonneg
              hcontext_subset (by linarith)
        · rw [hsigma_eq]
          exact himprovement
      · by_cases hupper_response_neg : response sigma upper < 0
        · rcases hinterval_upper_derivative hsigma_open hsigma_subset hpoint
              hcomponent_eq hlower_nonneg hlower_upper with
            ⟨derivativeValue, hderiv_local, hsign_local⟩
          have hderiv :
              HasDerivAt (fun x => Rhat (context ∪ Set.Ioo lower x))
                derivativeValue upper := by
            simpa [gn21Lemma5ComponentUpperPath, context] using hderiv_local
          have hsign :
              sameStrictSign derivativeValue
                (response (context ∪ Set.Ioo lower upper) upper) := by
            rw [← hsigma_eq]
            exact hsign_local
          have hsign_sigma :
              sameStrictSign derivativeValue (response sigma upper) := by
            rw [hsigma_eq]
            exact hsign
          have hderivative_neg : derivativeValue < 0 :=
            sameStrictSign_neg_left hsign_sigma hupper_response_neg
          rcases exists_pos_left_improvement_of_hasDerivAt_neg_lt
              hderiv hderivative_neg (sub_pos.mpr hlower_upper) with
            ⟨epsilon, hepsilon_pos, hepsilon_width, himprovement⟩
          refine ⟨context ∪ Set.Ioo lower (upper - epsilon), ?_, ?_, ?_⟩
          · exact hcontext_open.union isOpen_Ioo
          · exact
              union_ioo_subset_acceptAllPolicy_of_subset_of_left_nonneg
                hcontext_subset hlower_nonneg
          · rw [hsigma_eq]
            exact himprovement
        · have hlower_response_zero : response sigma lower = 0 := by
            linarith
          have hupper_response_zero : response sigma upper = 0 := by
            linarith
          let pivot : ℝ := (lower + upper) / 2
          have hlower_pivot : lower < pivot := by
            dsimp [pivot]
            linarith
          have hpivot_upper : pivot < upper := by
            dsimp [pivot]
            linarith
          have hpivot_sigma : pivot ∈ sigma :=
            hinterval_subset ⟨hlower_pivot, hpivot_upper⟩
          have hpivot_response_neg : response sigma pivot < 0 := by
            have hpivot_lt :
                response sigma pivot <
                  max (response sigma lower) (response sigma upper) :=
              paper_lemma5_strictQuasiConvex_response_lt_of_between
                (response sigma) hresponse_quasiConvex hlower_pos
                hlower_pivot hpivot_upper
            simpa [hlower_response_zero, hupper_response_zero] using hpivot_lt
          rcases hsplit_lower_derivative sigma pivot hsigma_open
              hsigma_subset hpivot_sigma with
            ⟨derivativeValue, hderiv, hsign⟩
          have hderivative_pos : 0 < derivativeValue :=
            sameStrictSign_pos_left hsign (by linarith)
          exact
            exists_open_strict_improvement_of_interiorSplitLower_derivative_pos
              mu Rhat hsigma_open hsigma_subset hRhat_ae pivot
              derivativeValue hderiv hderivative_pos

/-- Symmetric-difference continuity makes reward invariant under null policy changes. -/
theorem reward_eq_of_symmDiffContinuousAt_of_policyAlmostEverywhereEq
    (mu : Measure TripLength) (Rhat : SingleStateReward)
    {sigma tau : TripPolicy}
    (hcontinuous : GN21SymmDiffContinuousAt mu Rhat sigma)
    (hae : policyAlmostEverywhereEq mu sigma tau) :
    Rhat sigma = Rhat tau := by
  by_contra hne
  have hdiff_ne : Rhat tau - Rhat sigma ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hdiff_pos : 0 < |Rhat tau - Rhat sigma| := abs_pos.mpr hdiff_ne
  rcases hcontinuous |Rhat tau - Rhat sigma| hdiff_pos with
    ⟨delta, hdelta_ne, hdelta⟩
  have hmeasure_lt : mu (sigma ∆ tau) < delta := by
    rw [show mu (sigma ∆ tau) = 0 from hae]
    exact bot_lt_iff_ne_bot.mpr hdelta_ne
  exact (lt_irrefl |Rhat tau - Rhat sigma|)
    (hdelta tau hmeasure_lt)

/-- Null symmetric-difference equality is transitive. -/
theorem policyAlmostEverywhereEq.trans'
    (mu : Measure TripLength) {sigma tau upsilon : TripPolicy}
    (hsigma_tau : policyAlmostEverywhereEq mu sigma tau)
    (htau_upsilon : policyAlmostEverywhereEq mu tau upsilon) :
    policyAlmostEverywhereEq mu sigma upsilon := by
  rw [policyAlmostEverywhereEq]
  exact measure_symmDiff_eq_zero_iff.mpr
    ((ae_eq_set_of_policyAlmostEverywhereEq mu hsigma_tau).trans
      (ae_eq_set_of_policyAlmostEverywhereEq mu htau_upsilon))

/-- Touching extended middle intervals merge modulo their shared endpoint. -/
theorem policyAlmostEverywhereEq_extendedMiddle_union_touching
    (mu : Measure TripLength) [NoAtoms mu]
    {lower middle upper : ℝ≥0∞}
    (hlower_middle : lower ≤ middle)
    (hmiddle_upper : middle ≤ upper) :
    policyAlmostEverywhereEq mu
      (gn21ExtendedMiddlePolicy lower middle ∪
        gn21ExtendedMiddlePolicy middle upper)
      (gn21ExtendedMiddlePolicy lower upper) := by
  cases middle using ENNReal.recTopCoe with
  | top =>
      have hupper_top : upper = ∞ := top_unique hmiddle_upper
      subst upper
      simp [policyAlmostEverywhereEq]
  | coe middleFinite =>
      cases lower using ENNReal.recTopCoe with
      | top =>
          have hfalse : ¬ (∞ : ℝ≥0∞) ≤ (middleFinite : ℝ≥0∞) :=
            not_le_of_gt ENNReal.coe_lt_top
          exact False.elim (hfalse hlower_middle)
      | coe lowerFinite =>
          have hlower_middle_real :
              (lowerFinite : ℝ) ≤ (middleFinite : ℝ) := by
            exact_mod_cast ENNReal.coe_le_coe.mp hlower_middle
          cases upper using ENNReal.recTopCoe with
          | top =>
              rw [gn21ExtendedMiddlePolicy_coe_coe_eq_Ioo,
                gn21ExtendedMiddlePolicy_coe_top_eq_Ioi,
                gn21ExtendedMiddlePolicy_coe_top_eq_Ioi]
              exact policyAlmostEverywhereEq_ioo_union_Ioi_touching
                mu hlower_middle_real
          | coe upperFinite =>
              have hmiddle_upper_real :
                  (middleFinite : ℝ) ≤ (upperFinite : ℝ) := by
                exact_mod_cast ENNReal.coe_le_coe.mp hmiddle_upper
              rw [gn21ExtendedMiddlePolicy_coe_coe_eq_Ioo,
                gn21ExtendedMiddlePolicy_coe_coe_eq_Ioo,
                gn21ExtendedMiddlePolicy_coe_coe_eq_Ioo]
              exact policyAlmostEverywhereEq_ioo_union_touching
                mu hlower_middle_real hmiddle_upper_real

/--
An indexed union preserves almost-everywhere equality when only two indexed
components change and their two-component unions are almost everywhere equal.
-/
theorem policyAlmostEverywhereEq_iUnion_of_two
    {index : Type*} (mu : Measure TripLength)
    (left right : index → TripPolicy) (first second : index)
    (hsame : ∀ i, i ≠ first → i ≠ second → left i = right i)
    (hpair : policyAlmostEverywhereEq mu
      (left first ∪ left second) (right first ∪ right second)) :
    policyAlmostEverywhereEq mu (⋃ i, left i) (⋃ i, right i) := by
  rw [policyAlmostEverywhereEq]
  apply measure_symmDiff_eq_zero_iff.mpr
  have hpair_ae := ae_eq_set_of_policyAlmostEverywhereEq mu hpair
  filter_upwards [hpair_ae] with τ hτ
  have hτ_iff := Iff.of_eq hτ
  apply propext
  constructor
  · intro hleft
    rcases Set.mem_iUnion.1 hleft with ⟨i, hi⟩
    by_cases hfirst : i = first
    · subst i
      rcases hτ_iff.mp (Or.inl hi) with hright | hright
      · exact Set.mem_iUnion.2 ⟨first, hright⟩
      · exact Set.mem_iUnion.2 ⟨second, hright⟩
    · by_cases hsecond : i = second
      · subst i
        rcases hτ_iff.mp (Or.inr hi) with hright | hright
        · exact Set.mem_iUnion.2 ⟨first, hright⟩
        · exact Set.mem_iUnion.2 ⟨second, hright⟩
      · rw [hsame i hfirst hsecond] at hi
        exact Set.mem_iUnion.2 ⟨i, hi⟩
  · intro hright
    rcases Set.mem_iUnion.1 hright with ⟨i, hi⟩
    by_cases hfirst : i = first
    · subst i
      rcases hτ_iff.mpr (Or.inl hi) with hleft | hleft
      · exact Set.mem_iUnion.2 ⟨first, hleft⟩
      · exact Set.mem_iUnion.2 ⟨second, hleft⟩
    · by_cases hsecond : i = second
      · subst i
        rcases hτ_iff.mpr (Or.inr hi) with hleft | hleft
        · exact Set.mem_iUnion.2 ⟨first, hleft⟩
        · exact Set.mem_iUnion.2 ⟨second, hleft⟩
      · rw [← hsame i hfirst hsecond] at hi
        exact Set.mem_iUnion.2 ⟨i, hi⟩

/-! ## Compact finite endpoint domain -/

/-- The lower endpoint coordinate of interval `i` in a `2 * n` endpoint vector. -/
def gn21LowerEndpointIndex {n : Nat} (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.1, by omega⟩

/-- The upper endpoint coordinate of interval `i` in a `2 * n` endpoint vector. -/
def gn21UpperEndpointIndex {n : Nat} (i : Fin n) : Fin (2 * n) :=
  ⟨2 * i.1 + 1, by omega⟩

/-- A finite endpoint vector uses the compact extended nonnegative line. -/
abbrev GN21EndpointVector (n : Nat) := Fin (2 * n) → ℝ≥0∞

/-- Ordered endpoint vectors, including collision and infinity boundary points. -/
def gn21OrderedEndpointVectors (n : Nat) : Set (GN21EndpointVector n) :=
  {endpoints | ∀ ⦃i j⦄, i ≤ j → endpoints i ≤ endpoints j}

/-- Every two distinct ordered coordinates are strictly separated. -/
def gn21StrictEndpointVector {n : Nat}
    (endpoints : GN21EndpointVector n) : Prop :=
  ∀ ⦃i j : Fin (2 * n)⦄, i < j → endpoints i < endpoints j

/-- The open policy represented by an ordered finite endpoint vector. -/
def gn21EndpointVectorPolicy {n : Nat}
    (endpoints : GN21EndpointVector n) : TripPolicy :=
  ⋃ i : Fin n,
    gn21ExtendedMiddlePolicy
      (endpoints (gn21LowerEndpointIndex i))
      (endpoints (gn21UpperEndpointIndex i))

/-- Interleaved slot/parity coordinates for the endpoint-vector convention. -/
def gn21SlotParityEquiv (n : Nat) : Fin n × Fin 2 ≃ Fin (2 * n) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm n 2))

/-- Build an interleaved endpoint vector from lower and upper coordinates by slot. -/
def gn21EndpointVectorOfSlots {n : Nat}
    (lower upper : Fin n → ℝ≥0∞) : GN21EndpointVector n := fun coordinate =>
  let slotParity := (gn21SlotParityEquiv n).symm coordinate
  if slotParity.2 = 0 then lower slotParity.1 else upper slotParity.1

@[simp] theorem gn21EndpointVectorOfSlots_lower {n : Nat}
    (lower upper : Fin n → ℝ≥0∞) (slot : Fin n) :
    gn21EndpointVectorOfSlots lower upper (gn21LowerEndpointIndex slot) =
      lower slot := by
  have hcoordinate :
      gn21LowerEndpointIndex slot =
        gn21SlotParityEquiv n (slot, (0 : Fin 2)) := by
    apply Fin.ext
    simp [gn21LowerEndpointIndex, gn21SlotParityEquiv, finProdFinEquiv]
  rw [hcoordinate]
  simp [gn21EndpointVectorOfSlots]

@[simp] theorem gn21EndpointVectorOfSlots_upper {n : Nat}
    (lower upper : Fin n → ℝ≥0∞) (slot : Fin n) :
    gn21EndpointVectorOfSlots lower upper (gn21UpperEndpointIndex slot) =
      upper slot := by
  have hcoordinate :
      gn21UpperEndpointIndex slot =
        gn21SlotParityEquiv n (slot, (1 : Fin 2)) := by
    apply Fin.ext
    simp [gn21UpperEndpointIndex, gn21SlotParityEquiv, finProdFinEquiv]
    omega
  rw [hcoordinate]
  simp [gn21EndpointVectorOfSlots]

/-- Ordered slots produce an ordered interleaved endpoint vector. -/
theorem gn21EndpointVectorOfSlots_ordered {n : Nat}
    {lower upper : Fin n → ℝ≥0∞}
    (hwithin : ∀ slot, lower slot ≤ upper slot)
    (hbetween : ∀ left right, left < right → upper left ≤ lower right) :
    gn21EndpointVectorOfSlots lower upper ∈ gn21OrderedEndpointVectors n := by
  intro first second hfirst_second
  let firstPair := (gn21SlotParityEquiv n).symm first
  let secondPair := (gn21SlotParityEquiv n).symm second
  have hfirst_value :
      first.1 = firstPair.2.1 + 2 * firstPair.1.1 := by
    have happly := congrArg Fin.val
      ((gn21SlotParityEquiv n).apply_symm_apply first)
    simpa [firstPair, gn21SlotParityEquiv, finProdFinEquiv] using happly.symm
  have hsecond_value :
      second.1 = secondPair.2.1 + 2 * secondPair.1.1 := by
    have happly := congrArg Fin.val
      ((gn21SlotParityEquiv n).apply_symm_apply second)
    simpa [secondPair, gn21SlotParityEquiv, finProdFinEquiv] using happly.symm
  have hslot_le : firstPair.1.1 ≤ secondPair.1.1 := by
    omega
  by_cases hslot : firstPair.1 = secondPair.1
  · by_cases hfirst_zero : firstPair.2 = 0
    · rw [show gn21EndpointVectorOfSlots lower upper first =
          lower firstPair.1 by
        simp [gn21EndpointVectorOfSlots, firstPair, hfirst_zero]]
      by_cases hsecond_zero : secondPair.2 = 0
      · rw [show gn21EndpointVectorOfSlots lower upper second =
            lower secondPair.1 by
          simp [gn21EndpointVectorOfSlots, secondPair, hsecond_zero]]
        simpa [hslot]
      · rw [show gn21EndpointVectorOfSlots lower upper second =
            upper secondPair.1 by
          simp [gn21EndpointVectorOfSlots, secondPair, hsecond_zero]]
        simpa [hslot] using hwithin firstPair.1
    · have hfirst_one : firstPair.2.1 = 1 := by omega
      have hsecond_nonzero : secondPair.2 ≠ 0 := by
        intro hsecond_zero
        have hsecond_value_zero : secondPair.2.1 = 0 := by
          simpa using congrArg Fin.val hsecond_zero
        have hslot_value : firstPair.1.1 = secondPair.1.1 := by
          simpa using congrArg Fin.val hslot
        omega
      rw [show gn21EndpointVectorOfSlots lower upper first =
            upper firstPair.1 by
          simp [gn21EndpointVectorOfSlots, firstPair, hfirst_zero],
        show gn21EndpointVectorOfSlots lower upper second =
            upper secondPair.1 by
          simp [gn21EndpointVectorOfSlots, secondPair, hsecond_nonzero]]
      simpa [hslot]
  · have hslot_lt : firstPair.1 < secondPair.1 := by
      exact lt_of_le_of_ne hslot_le hslot
    have hfirst_upper :
        gn21EndpointVectorOfSlots lower upper first ≤ upper firstPair.1 := by
      by_cases hfirst_zero : firstPair.2 = 0
      · simpa [gn21EndpointVectorOfSlots, firstPair, hfirst_zero] using
          hwithin firstPair.1
      · simp [gn21EndpointVectorOfSlots, firstPair, hfirst_zero]
    have hsecond_lower :
        lower secondPair.1 ≤
          gn21EndpointVectorOfSlots lower upper second := by
      by_cases hsecond_zero : secondPair.2 = 0
      · simp [gn21EndpointVectorOfSlots, secondPair, hsecond_zero]
      · simpa [gn21EndpointVectorOfSlots, secondPair, hsecond_zero] using
          hwithin secondPair.1
    exact hfirst_upper.trans
      ((hbetween firstPair.1 secondPair.1 hslot_lt).trans hsecond_lower)

/-! ## Finite interval normalization -/

/-- A finite tuple sorted by endpoint value, retaining duplicate endpoints. -/
noncomputable def gn21SortedTuple {m : Nat} {α : Type*} [LinearOrder α]
    (raw : Fin m → α) : Fin m → α :=
  raw ∘ Tuple.sort raw

theorem monotone_gn21SortedTuple {m : Nat} {α : Type*} [LinearOrder α]
    (raw : Fin m → α) :
    Monotone (gn21SortedTuple raw) := by
  exact Tuple.monotone_sort raw

/-- Left coordinate of an adjacent cell in a sorted `m`-tuple. -/
def gn21SortedCellLeftIndex {m : Nat} (cell : Fin (m - 1)) : Fin m :=
  ⟨cell.1, by omega⟩

/-- Right coordinate of an adjacent cell in a sorted `m`-tuple. -/
def gn21SortedCellRightIndex {m : Nat} (cell : Fin (m - 1)) : Fin m :=
  ⟨cell.1 + 1, by omega⟩

theorem gn21SortedCellLeftIndex_lt_rightIndex {m : Nat}
    (cell : Fin (m - 1)) :
    gn21SortedCellLeftIndex cell < gn21SortedCellRightIndex cell := by
  exact Fin.mk_lt_mk.2 (Nat.lt_succ_self _)

/-- No raw tuple entry lies strictly inside one adjacent sorted cell. -/
theorem not_raw_between_adjacent_gn21SortedTuple {m : Nat}
    {α : Type*} [LinearOrder α]
    (raw : Fin m → α) (cell : Fin (m - 1)) (entry : Fin m) :
    ¬ (gn21SortedTuple raw (gn21SortedCellLeftIndex cell) < raw entry ∧
      raw entry < gn21SortedTuple raw (gn21SortedCellRightIndex cell)) := by
  intro hbetween
  let sortedEntry : Fin m := (Tuple.sort raw).symm entry
  have hentry : raw entry = gn21SortedTuple raw sortedEntry := by
    simp [gn21SortedTuple, sortedEntry]
  have hleft_entry : gn21SortedCellLeftIndex cell < sortedEntry := by
    by_contra hnot
    have hle : sortedEntry ≤ gn21SortedCellLeftIndex cell := le_of_not_gt hnot
    have hmono := monotone_gn21SortedTuple raw hle
    rw [← hentry] at hmono
    exact (not_lt_of_ge hmono) hbetween.1
  have hentry_right : sortedEntry < gn21SortedCellRightIndex cell := by
    by_contra hnot
    have hle : gn21SortedCellRightIndex cell ≤ sortedEntry := le_of_not_gt hnot
    have hmono := monotone_gn21SortedTuple raw hle
    rw [← hentry] at hmono
    exact (not_lt_of_ge hmono) hbetween.2
  have hleft_lt : cell.1 < sortedEntry.1 := by
    simpa [gn21SortedCellLeftIndex] using hleft_entry
  have hright_le : sortedEntry.1 ≤ cell.1 := by
    change sortedEntry.1 < (gn21SortedCellRightIndex cell).1 at hentry_right
    dsimp [gn21SortedCellRightIndex] at hentry_right
    omega
  omega

/--
A point strictly bracketed by raw entries and unequal to every raw entry lies
in one adjacent open cell of the sorted tuple.
-/
theorem exists_gn21SortedCell_of_raw_lt_and_lt_raw {m : Nat}
    {α : Type*} [LinearOrder α]
    (raw : Fin m → α) (x : α)
    (hlower : ∃ entry, raw entry < x)
    (hupper : ∃ entry, x < raw entry)
    (hne : ∀ entry, x ≠ raw entry) :
    ∃ cell : Fin (m - 1),
      gn21SortedTuple raw (gn21SortedCellLeftIndex cell) < x ∧
        x < gn21SortedTuple raw (gn21SortedCellRightIndex cell) := by
  classical
  let sorted := gn21SortedTuple raw
  let below : Finset (Fin m) := Finset.univ.filter fun i => sorted i < x
  have hbelow_nonempty : below.Nonempty := by
    rcases hlower with ⟨entry, hentry⟩
    let sortedEntry : Fin m := (Tuple.sort raw).symm entry
    refine ⟨sortedEntry, ?_⟩
    simp only [below, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [sorted, gn21SortedTuple, sortedEntry] using hentry
  have hbelow_ssubset : below ⊂ Finset.univ := by
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hreverse
    rcases hupper with ⟨entry, hentry⟩
    let sortedEntry : Fin m := (Tuple.sort raw).symm entry
    have hsorted_entry : sorted sortedEntry = raw entry := by
      simp [sorted, gn21SortedTuple, sortedEntry]
    have hmem : sortedEntry ∈ below := by
      exact hreverse (by simp)
    simp only [below, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [hsorted_entry] at hmem
    exact (not_lt_of_ge (le_of_lt hentry)) hmem
  have hcard_pos : 0 < below.card := Finset.card_pos.mpr hbelow_nonempty
  have hcard_lt : below.card < m := by
    have hcard := Finset.card_lt_card hbelow_ssubset
    simpa using hcard
  let cell : Fin (m - 1) := ⟨below.card - 1, by omega⟩
  have hsorted_monotone : Monotone sorted :=
    monotone_gn21SortedTuple raw
  have hleft_lt : sorted (gn21SortedCellLeftIndex cell) < x := by
    apply (Tuple.lt_card_lt_iff_apply_lt_of_monotone
      hsorted_monotone).1
    change (gn21SortedCellLeftIndex cell).1 < below.card
    simp [gn21SortedCellLeftIndex, cell]
    omega
  have hright_not_lt : ¬ sorted (gn21SortedCellRightIndex cell) < x := by
    intro hright
    have hindex_lt := (Tuple.lt_card_lt_iff_apply_lt_of_monotone
      hsorted_monotone).2 hright
    change (gn21SortedCellRightIndex cell).1 < below.card at hindex_lt
    simp [gn21SortedCellRightIndex, cell] at hindex_lt
    omega
  have hx_le_right : x ≤ sorted (gn21SortedCellRightIndex cell) :=
    le_of_not_gt hright_not_lt
  have hx_ne_right : x ≠ sorted (gn21SortedCellRightIndex cell) := by
    let entry := Tuple.sort raw (gn21SortedCellRightIndex cell)
    have hsorted_entry :
        sorted (gn21SortedCellRightIndex cell) = raw entry := by
      rfl
    rw [hsorted_entry]
    exact hne entry
  exact ⟨cell, hleft_lt, lt_of_le_of_ne hx_le_right hx_ne_right⟩

/-- Policy represented by a finite tuple of nonnegative open intervals. -/
def gn21FiniteNNIntervalTuplePolicy {n : Nat}
    (lower upper : Fin n → NNReal) : TripPolicy :=
  ⋃ slot : Fin n, Set.Ioo (lower slot : ℝ) (upper slot : ℝ)

/-- Interleaved raw lower and upper endpoints of a finite interval tuple. -/
noncomputable def gn21FiniteNNIntervalTupleRawEndpoints {n : Nat}
    (lower upper : Fin n → NNReal) : Fin (2 * n) → NNReal := fun coordinate =>
  let slotParity := (gn21SlotParityEquiv n).symm coordinate
  if slotParity.2 = 0 then lower slotParity.1 else upper slotParity.1

@[simp] theorem gn21FiniteNNIntervalTupleRawEndpoints_lower {n : Nat}
    (lower upper : Fin n → NNReal) (slot : Fin n) :
    gn21FiniteNNIntervalTupleRawEndpoints lower upper
        (gn21SlotParityEquiv n (slot, (0 : Fin 2))) = lower slot := by
  simp [gn21FiniteNNIntervalTupleRawEndpoints]

@[simp] theorem gn21FiniteNNIntervalTupleRawEndpoints_upper {n : Nat}
    (lower upper : Fin n → NNReal) (slot : Fin n) :
    gn21FiniteNNIntervalTupleRawEndpoints lower upper
        (gn21SlotParityEquiv n (slot, (1 : Fin 2))) = upper slot := by
  simp [gn21FiniteNNIntervalTupleRawEndpoints]

/-- Slot corresponding to one adjacent cell of the sorted raw endpoints. -/
def gn21NormalizedSlotOfCell {n : Nat}
    (cell : Fin (2 * n - 1)) : Fin (2 * n + 1) :=
  ⟨cell.1 + 1, by omega⟩

/-- The adjacent sorted cell is retained exactly when its midpoint is in the tuple policy. -/
def gn21FiniteNNIntervalTupleCellActive {n : Nat}
    (lower upper : Fin n → NNReal) (cell : Fin (2 * n - 1)) : Prop :=
  let raw := gn21FiniteNNIntervalTupleRawEndpoints lower upper
  let left := gn21SortedTuple raw (gn21SortedCellLeftIndex cell)
  let right := gn21SortedTuple raw (gn21SortedCellRightIndex cell)
  (((left : ℝ) + (right : ℝ)) / 2) ∈
    gn21FiniteNNIntervalTuplePolicy lower upper

/-- Decidable noncomputable flag for retaining one adjacent sorted cell. -/
noncomputable def gn21FiniteNNIntervalTupleCellIncluded {n : Nat}
    (lower upper : Fin n → NNReal) (cell : Fin (2 * n - 1)) : Bool := by
  classical
  exact decide (gn21FiniteNNIntervalTupleCellActive lower upper cell)

theorem gn21FiniteNNIntervalTupleCellIncluded_eq_true_iff {n : Nat}
    (lower upper : Fin n → NNReal) (cell : Fin (2 * n - 1)) :
    gn21FiniteNNIntervalTupleCellIncluded lower upper cell = true ↔
      gn21FiniteNNIntervalTupleCellActive lower upper cell := by
  classical
  simp [gn21FiniteNNIntervalTupleCellIncluded]

/-- Recover the adjacent-cell index from a nonboundary normalized slot. -/
def gn21CellOfNormalizedInteriorSlot {n : Nat}
    (slot : Fin (2 * n + 1))
    (hzero : slot ≠ 0) (hlast : slot ≠ Fin.last (2 * n)) :
    Fin (2 * n - 1) :=
  ⟨slot.1 - 1, by
    have hslot_pos : 0 < slot.1 := by
      by_contra hnot
      apply hzero
      apply Fin.ext
      change slot.1 = 0
      omega
    have hslot_lt : slot.1 < 2 * n := by
      have hslot_ne : slot.1 ≠ 2 * n := by
        intro hvalue
        apply hlast
        apply Fin.ext
        change slot.1 = 2 * n
        exact hvalue
      omega
    omega⟩

@[simp] theorem gn21CellOfNormalizedInteriorSlot_slotOfCell {n : Nat}
    (cell : Fin (2 * n - 1))
    (hzero : gn21NormalizedSlotOfCell cell ≠ 0)
    (hlast : gn21NormalizedSlotOfCell cell ≠ Fin.last (2 * n)) :
    gn21CellOfNormalizedInteriorSlot
      (gn21NormalizedSlotOfCell cell) hzero hlast = cell := by
  apply Fin.ext
  simp [gn21CellOfNormalizedInteriorSlot, gn21NormalizedSlotOfCell]

/-- Lower endpoint of one slot in the normalized finite interval tuple. -/
noncomputable def gn21FiniteNNIntervalTupleSlotLower {n : Nat}
    (lower upper : Fin n → NNReal) (slot : Fin (2 * n + 1)) : ℝ≥0∞ :=
  if hzero : slot = 0 then 0
  else if hlast : slot = Fin.last (2 * n) then ∞
  else
    let cell := gn21CellOfNormalizedInteriorSlot slot hzero hlast
    (gn21SortedTuple
      (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
      (gn21SortedCellLeftIndex cell) : NNReal)

/-- Upper endpoint of one slot in the normalized finite interval tuple. -/
noncomputable def gn21FiniteNNIntervalTupleSlotUpper {n : Nat}
    (lower upper : Fin n → NNReal) (slot : Fin (2 * n + 1)) : ℝ≥0∞ :=
  if hzero : slot = 0 then 0
  else if hlast : slot = Fin.last (2 * n) then ∞
  else
    let cell := gn21CellOfNormalizedInteriorSlot slot hzero hlast
    let raw := gn21FiniteNNIntervalTupleRawEndpoints lower upper
    if gn21FiniteNNIntervalTupleCellIncluded lower upper cell then
      (gn21SortedTuple raw (gn21SortedCellRightIndex cell) : NNReal)
    else
      (gn21SortedTuple raw (gn21SortedCellLeftIndex cell) : NNReal)

/-- Ordered endpoint-vector normalization of a finite nonnegative interval tuple. -/
noncomputable def gn21FiniteNNIntervalTupleEndpointVector {n : Nat}
    (lower upper : Fin n → NNReal) : GN21EndpointVector (2 * n + 1) :=
  gn21EndpointVectorOfSlots
    (gn21FiniteNNIntervalTupleSlotLower lower upper)
    (gn21FiniteNNIntervalTupleSlotUpper lower upper)

@[simp] theorem gn21FiniteNNIntervalTupleSlotLower_zero {n : Nat}
    (lower upper : Fin n → NNReal) :
    gn21FiniteNNIntervalTupleSlotLower lower upper 0 = 0 := by
  simp [gn21FiniteNNIntervalTupleSlotLower]

@[simp] theorem gn21FiniteNNIntervalTupleSlotUpper_zero {n : Nat}
    (lower upper : Fin n → NNReal) :
    gn21FiniteNNIntervalTupleSlotUpper lower upper 0 = 0 := by
  simp [gn21FiniteNNIntervalTupleSlotUpper]

@[simp] theorem gn21FiniteNNIntervalTupleSlotLower_last {n : Nat}
    (hn : 0 < n) (lower upper : Fin n → NNReal) :
    gn21FiniteNNIntervalTupleSlotLower lower upper (Fin.last (2 * n)) = ∞ := by
  have hlast_ne_zero : (Fin.last (2 * n) : Fin (2 * n + 1)) ≠ 0 := by
    intro h
    have hvalue := congrArg Fin.val h
    simp at hvalue
    omega
  simp [gn21FiniteNNIntervalTupleSlotLower, hlast_ne_zero]

@[simp] theorem gn21FiniteNNIntervalTupleSlotUpper_last {n : Nat}
    (hn : 0 < n) (lower upper : Fin n → NNReal) :
    gn21FiniteNNIntervalTupleSlotUpper lower upper (Fin.last (2 * n)) = ∞ := by
  have hlast_ne_zero : (Fin.last (2 * n) : Fin (2 * n + 1)) ≠ 0 := by
    intro h
    have hvalue := congrArg Fin.val h
    simp at hvalue
    omega
  simp [gn21FiniteNNIntervalTupleSlotUpper, hlast_ne_zero]

@[simp] theorem gn21FiniteNNIntervalTupleSlotLower_cell {n : Nat}
    (lower upper : Fin n → NNReal) (cell : Fin (2 * n - 1)) :
    gn21FiniteNNIntervalTupleSlotLower lower upper
        (gn21NormalizedSlotOfCell cell) =
      (gn21SortedTuple
        (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
        (gn21SortedCellLeftIndex cell) : NNReal) := by
  have hzero : gn21NormalizedSlotOfCell cell ≠ 0 := by
    apply Fin.ne_of_val_ne
    simp [gn21NormalizedSlotOfCell]
  have hlast :
      gn21NormalizedSlotOfCell cell ≠ Fin.last (2 * n) := by
    intro h
    have hvalue := congrArg Fin.val h
    simp [gn21NormalizedSlotOfCell] at hvalue
    omega
  rw [gn21FiniteNNIntervalTupleSlotLower, dif_neg hzero, dif_neg hlast]
  simp

theorem gn21FiniteNNIntervalTupleSlotUpper_cell {n : Nat}
    (lower upper : Fin n → NNReal) (cell : Fin (2 * n - 1)) :
    gn21FiniteNNIntervalTupleSlotUpper lower upper
        (gn21NormalizedSlotOfCell cell) =
      if gn21FiniteNNIntervalTupleCellIncluded lower upper cell then
        (gn21SortedTuple
          (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
          (gn21SortedCellRightIndex cell) : NNReal)
      else
        (gn21SortedTuple
          (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
          (gn21SortedCellLeftIndex cell) : NNReal) := by
  have hzero : gn21NormalizedSlotOfCell cell ≠ 0 := by
    apply Fin.ne_of_val_ne
    simp [gn21NormalizedSlotOfCell]
  have hlast :
      gn21NormalizedSlotOfCell cell ≠ Fin.last (2 * n) := by
    intro h
    have hvalue := congrArg Fin.val h
    simp [gn21NormalizedSlotOfCell] at hvalue
    omega
  rw [gn21FiniteNNIntervalTupleSlotUpper, dif_neg hzero, dif_neg hlast]
  simp
  by_cases hincluded :
      gn21FiniteNNIntervalTupleCellIncluded lower upper cell = true
  · simp [hincluded]
  · simp [hincluded]

@[simp] theorem gn21NormalizedSlotOfCell_cellOfInteriorSlot {n : Nat}
    (slot : Fin (2 * n + 1))
    (hzero : slot ≠ 0) (hlast : slot ≠ Fin.last (2 * n)) :
    gn21NormalizedSlotOfCell
      (gn21CellOfNormalizedInteriorSlot slot hzero hlast) = slot := by
  apply Fin.ext
  simp [gn21NormalizedSlotOfCell, gn21CellOfNormalizedInteriorSlot]
  have hslot_pos : 0 < slot.1 := by
    by_contra hnot
    apply hzero
    apply Fin.ext
    change slot.1 = 0
    omega
  omega

/-- The normalized lower endpoint never exceeds its slot's upper endpoint. -/
theorem gn21FiniteNNIntervalTupleSlotLower_le_upper {n : Nat}
    (hn : 0 < n) (lower upper : Fin n → NNReal) :
    ∀ slot,
      gn21FiniteNNIntervalTupleSlotLower lower upper slot ≤
        gn21FiniteNNIntervalTupleSlotUpper lower upper slot := by
  intro slot
  by_cases hzero : slot = 0
  · subst slot
    simp
  by_cases hlast : slot = Fin.last (2 * n)
  · subst slot
    simp [hn]
  let cell := gn21CellOfNormalizedInteriorSlot slot hzero hlast
  have hslot : gn21NormalizedSlotOfCell cell = slot := by
    exact gn21NormalizedSlotOfCell_cellOfInteriorSlot slot hzero hlast
  rw [← hslot, gn21FiniteNNIntervalTupleSlotLower_cell,
    gn21FiniteNNIntervalTupleSlotUpper_cell]
  by_cases hincluded :
      gn21FiniteNNIntervalTupleCellIncluded lower upper cell = true
  · rw [if_pos hincluded]
    exact_mod_cast monotone_gn21SortedTuple
      (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
      (le_of_lt (gn21SortedCellLeftIndex_lt_rightIndex cell))
  · rw [if_neg hincluded]

/-- Distinct normalized slots are ordered across their common sorted endpoint cells. -/
theorem gn21FiniteNNIntervalTupleSlotUpper_le_lower_of_lt {n : Nat}
    (hn : 0 < n) (lower upper : Fin n → NNReal) :
    ∀ left right, left < right →
      gn21FiniteNNIntervalTupleSlotUpper lower upper left ≤
        gn21FiniteNNIntervalTupleSlotLower lower upper right := by
  intro left right hleft_right
  by_cases hleft_zero : left = 0
  · subst left
    simp
  by_cases hright_last : right = Fin.last (2 * n)
  · subst right
    simp [hn]
  have hleft_last : left ≠ Fin.last (2 * n) := by
    intro hlast
    subst left
    have hvalue : (Fin.last (2 * n) : Fin (2 * n + 1)).1 < right.1 :=
      hleft_right
    simp at hvalue
    omega
  have hright_zero : right ≠ 0 := by
    intro hzero
    subst right
    have hvalue : left.1 < (0 : Fin (2 * n + 1)).1 := hleft_right
    simp at hvalue
  let leftCell :=
    gn21CellOfNormalizedInteriorSlot left hleft_zero hleft_last
  let rightCell :=
    gn21CellOfNormalizedInteriorSlot right hright_zero hright_last
  have hleft_slot : gn21NormalizedSlotOfCell leftCell = left := by
    exact gn21NormalizedSlotOfCell_cellOfInteriorSlot
      left hleft_zero hleft_last
  have hright_slot : gn21NormalizedSlotOfCell rightCell = right := by
    exact gn21NormalizedSlotOfCell_cellOfInteriorSlot
      right hright_zero hright_last
  rw [← hleft_slot, ← hright_slot,
    gn21FiniteNNIntervalTupleSlotUpper_cell,
    gn21FiniteNNIntervalTupleSlotLower_cell]
  have hcell_indices :
      gn21SortedCellRightIndex leftCell ≤
        gn21SortedCellLeftIndex rightCell := by
    apply Fin.mk_le_mk.2
    simp [leftCell, rightCell, gn21CellOfNormalizedInteriorSlot]
    have hleft_pos : 0 < left.1 := by
      by_contra hnot
      apply hleft_zero
      apply Fin.ext
      change left.1 = 0
      omega
    have hright_pos : 0 < right.1 := by
      by_contra hnot
      apply hright_zero
      apply Fin.ext
      change right.1 = 0
      omega
    omega
  have hsorted :
      gn21SortedTuple
          (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
          (gn21SortedCellRightIndex leftCell) ≤
        gn21SortedTuple
          (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
          (gn21SortedCellLeftIndex rightCell) :=
    monotone_gn21SortedTuple
      (gn21FiniteNNIntervalTupleRawEndpoints lower upper) hcell_indices
  by_cases hincluded :
      gn21FiniteNNIntervalTupleCellIncluded lower upper leftCell = true
  · rw [if_pos hincluded]
    exact_mod_cast hsorted
  · rw [if_neg hincluded]
    exact_mod_cast (monotone_gn21SortedTuple
      (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
      ((le_of_lt (gn21SortedCellLeftIndex_lt_rightIndex leftCell)).trans
        hcell_indices))

/-- The normalized finite interval tuple is an ordered endpoint vector. -/
theorem gn21FiniteNNIntervalTupleEndpointVector_ordered {n : Nat}
    (hn : 0 < n) (lower upper : Fin n → NNReal) :
    gn21FiniteNNIntervalTupleEndpointVector lower upper ∈
      gn21OrderedEndpointVectors (2 * n + 1) := by
  apply gn21EndpointVectorOfSlots_ordered
  · exact gn21FiniteNNIntervalTupleSlotLower_le_upper hn lower upper
  · exact gn21FiniteNNIntervalTupleSlotUpper_le_lower_of_lt hn lower upper

/-- A retained adjacent sorted cell is contained in the original finite interval union. -/
theorem gn21FiniteNNIntervalTuple_active_cell_subset {n : Nat}
    (lower upper : Fin n → NNReal) (cell : Fin (2 * n - 1))
    (hactive : gn21FiniteNNIntervalTupleCellActive lower upper cell) :
    Set.Ioo
        ((gn21SortedTuple
          (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
          (gn21SortedCellLeftIndex cell) : NNReal) : ℝ)
        ((gn21SortedTuple
          (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
          (gn21SortedCellRightIndex cell) : NNReal) : ℝ) ⊆
      gn21FiniteNNIntervalTuplePolicy lower upper := by
  let raw := gn21FiniteNNIntervalTupleRawEndpoints lower upper
  let leftEndpoint := gn21SortedTuple raw (gn21SortedCellLeftIndex cell)
  let rightEndpoint := gn21SortedTuple raw (gn21SortedCellRightIndex cell)
  change (((leftEndpoint : ℝ) + (rightEndpoint : ℝ)) / 2) ∈
      gn21FiniteNNIntervalTuplePolicy lower upper at hactive
  rcases Set.mem_iUnion.1 hactive with ⟨source, hmidpoint⟩
  intro x hx
  change (leftEndpoint : ℝ) < x ∧ x < (rightEndpoint : ℝ) at hx
  have hleft_right : (leftEndpoint : ℝ) < (rightEndpoint : ℝ) :=
    hx.1.trans hx.2
  have hleft_midpoint :
      (leftEndpoint : ℝ) <
        ((leftEndpoint : ℝ) + (rightEndpoint : ℝ)) / 2 := by
    linarith
  have hmidpoint_right :
      ((leftEndpoint : ℝ) + (rightEndpoint : ℝ)) / 2 <
        (rightEndpoint : ℝ) := by
    linarith
  let lowerEntry : Fin (2 * n) :=
    gn21SlotParityEquiv n (source, (0 : Fin 2))
  let upperEntry : Fin (2 * n) :=
    gn21SlotParityEquiv n (source, (1 : Fin 2))
  have hlower_raw : raw lowerEntry = lower source := by
    simp [raw, lowerEntry]
  have hupper_raw : raw upperEntry = upper source := by
    simp [raw, upperEntry]
  have hlower_le_left : lower source ≤ leftEndpoint := by
    by_contra hnot
    have hleft_lower : leftEndpoint < lower source := lt_of_not_ge hnot
    have hlower_right_real :
        (lower source : ℝ) < (rightEndpoint : ℝ) :=
      hmidpoint.1.trans hmidpoint_right
    have hlower_right : lower source < rightEndpoint := by
      exact_mod_cast hlower_right_real
    exact (not_raw_between_adjacent_gn21SortedTuple raw cell lowerEntry)
      ⟨by simpa [hlower_raw] using hleft_lower,
        by simpa [hlower_raw] using hlower_right⟩
  have hright_le_upper : rightEndpoint ≤ upper source := by
    by_contra hnot
    have hupper_right : upper source < rightEndpoint := lt_of_not_ge hnot
    have hleft_upper_real :
        (leftEndpoint : ℝ) < (upper source : ℝ) :=
      hleft_midpoint.trans hmidpoint.2
    have hleft_upper : leftEndpoint < upper source := by
      exact_mod_cast hleft_upper_real
    exact (not_raw_between_adjacent_gn21SortedTuple raw cell upperEntry)
      ⟨by simpa [hupper_raw] using hleft_upper,
        by simpa [hupper_raw] using hupper_right⟩
  apply Set.mem_iUnion.2
  refine ⟨source, ?_⟩
  constructor
  · exact lt_of_le_of_lt (by exact_mod_cast hlower_le_left) hx.1
  · exact lt_of_lt_of_le hx.2 (by exact_mod_cast hright_le_upper)

/-- Union of the retained adjacent sorted cells in a finite tuple normalization. -/
def gn21FiniteNNIntervalTupleNormalizedCellPolicy {n : Nat}
    (lower upper : Fin n → NNReal) : TripPolicy :=
  ⋃ cell : Fin (2 * n - 1),
    if gn21FiniteNNIntervalTupleCellIncluded lower upper cell then
      Set.Ioo
        ((gn21SortedTuple
          (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
          (gn21SortedCellLeftIndex cell) : NNReal) : ℝ)
        ((gn21SortedTuple
          (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
          (gn21SortedCellRightIndex cell) : NNReal) : ℝ)
    else ∅

/-- The normalized endpoint vector represents exactly its retained sorted cells. -/
theorem gn21EndpointVectorPolicy_finiteNNIntervalTupleEndpointVector {n : Nat}
    (hn : 0 < n) (lower upper : Fin n → NNReal) :
    gn21EndpointVectorPolicy
        (gn21FiniteNNIntervalTupleEndpointVector lower upper) =
      gn21FiniteNNIntervalTupleNormalizedCellPolicy lower upper := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨slot, hslot_mem⟩
    by_cases hzero : slot = 0
    · subst slot
      simp [gn21FiniteNNIntervalTupleEndpointVector] at hslot_mem
    by_cases hlast : slot = Fin.last (2 * n)
    · subst slot
      simp [gn21FiniteNNIntervalTupleEndpointVector, hn] at hslot_mem
    let cell := gn21CellOfNormalizedInteriorSlot slot hzero hlast
    have hslot : gn21NormalizedSlotOfCell cell = slot :=
      gn21NormalizedSlotOfCell_cellOfInteriorSlot slot hzero hlast
    rw [← hslot] at hslot_mem
    simp only [gn21FiniteNNIntervalTupleEndpointVector,
      gn21EndpointVectorOfSlots_lower, gn21EndpointVectorOfSlots_upper,
      gn21FiniteNNIntervalTupleSlotLower_cell,
      gn21FiniteNNIntervalTupleSlotUpper_cell] at hslot_mem
    by_cases hincluded :
        gn21FiniteNNIntervalTupleCellIncluded lower upper cell = true
    · rw [if_pos hincluded] at hslot_mem
      rw [gn21ExtendedMiddlePolicy_coe_coe_eq_Ioo] at hslot_mem
      apply Set.mem_iUnion.2
      exact ⟨cell, by simpa [hincluded]⟩
    · rw [if_neg hincluded] at hslot_mem
      rw [gn21ExtendedMiddlePolicy_self] at hslot_mem
      exact False.elim hslot_mem
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨cell, hcell⟩
    by_cases hincluded :
        gn21FiniteNNIntervalTupleCellIncluded lower upper cell = true
    · have hcell_mem :
          x ∈ Set.Ioo
            ((gn21SortedTuple
              (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
              (gn21SortedCellLeftIndex cell) : NNReal) : ℝ)
            ((gn21SortedTuple
              (gn21FiniteNNIntervalTupleRawEndpoints lower upper)
              (gn21SortedCellRightIndex cell) : NNReal) : ℝ) := by
        simpa [hincluded] using hcell
      apply Set.mem_iUnion.2
      refine ⟨gn21NormalizedSlotOfCell cell, ?_⟩
      simp only [gn21FiniteNNIntervalTupleEndpointVector,
        gn21EndpointVectorOfSlots_lower, gn21EndpointVectorOfSlots_upper,
        gn21FiniteNNIntervalTupleSlotLower_cell,
        gn21FiniteNNIntervalTupleSlotUpper_cell]
      rw [if_pos hincluded, gn21ExtendedMiddlePolicy_coe_coe_eq_Ioo]
      exact hcell_mem
    · simp [hincluded] at hcell

/-- Every original-policy point outside the finite endpoint set lies in a retained cell. -/
theorem mem_gn21FiniteNNIntervalTupleNormalizedCellPolicy_of_not_endpoint
    {n : Nat} (lower upper : Fin n → NNReal) {x : ℝ}
    (hx : x ∈ gn21FiniteNNIntervalTuplePolicy lower upper)
    (hne : ∀ entry : Fin (2 * n),
      x ≠ (gn21FiniteNNIntervalTupleRawEndpoints lower upper entry : ℝ)) :
    x ∈ gn21FiniteNNIntervalTupleNormalizedCellPolicy lower upper := by
  rcases Set.mem_iUnion.1 hx with ⟨source, hsource⟩
  have hx_nonneg : 0 ≤ x := by
    exact le_trans (by positivity : 0 ≤ (lower source : ℝ))
      (le_of_lt hsource.1)
  let xNN : NNReal := ⟨x, hx_nonneg⟩
  let raw := gn21FiniteNNIntervalTupleRawEndpoints lower upper
  let lowerEntry : Fin (2 * n) :=
    gn21SlotParityEquiv n (source, (0 : Fin 2))
  let upperEntry : Fin (2 * n) :=
    gn21SlotParityEquiv n (source, (1 : Fin 2))
  have hlower_raw : raw lowerEntry = lower source := by
    simp [raw, lowerEntry]
  have hupper_raw : raw upperEntry = upper source := by
    simp [raw, upperEntry]
  have hlower_x : raw lowerEntry < xNN := by
    rw [hlower_raw]
    exact_mod_cast hsource.1
  have hx_upper : xNN < raw upperEntry := by
    rw [hupper_raw]
    exact_mod_cast hsource.2
  have hne_nn : ∀ entry : Fin (2 * n), xNN ≠ raw entry := by
    intro entry heq
    apply hne entry
    have hvalue := congrArg Subtype.val heq
    simpa [xNN, raw] using hvalue
  rcases exists_gn21SortedCell_of_raw_lt_and_lt_raw
      raw xNN ⟨lowerEntry, hlower_x⟩ ⟨upperEntry, hx_upper⟩ hne_nn with
    ⟨cell, hleft_x, hx_right⟩
  let leftEndpoint := gn21SortedTuple raw (gn21SortedCellLeftIndex cell)
  let rightEndpoint := gn21SortedTuple raw (gn21SortedCellRightIndex cell)
  change leftEndpoint < xNN at hleft_x
  change xNN < rightEndpoint at hx_right
  have hlower_le_left : lower source ≤ leftEndpoint := by
    by_contra hnot
    have hleft_lower : leftEndpoint < lower source := lt_of_not_ge hnot
    have hlower_right : lower source < rightEndpoint := by
      exact (by rw [← hlower_raw]; exact hlower_x.trans hx_right)
    exact (not_raw_between_adjacent_gn21SortedTuple raw cell lowerEntry)
      ⟨by simpa [hlower_raw] using hleft_lower,
        by simpa [hlower_raw] using hlower_right⟩
  have hright_le_upper : rightEndpoint ≤ upper source := by
    by_contra hnot
    have hupper_right : upper source < rightEndpoint := lt_of_not_ge hnot
    have hleft_upper : leftEndpoint < upper source := by
      exact hleft_x.trans (by rw [← hupper_raw]; exact hx_upper)
    exact (not_raw_between_adjacent_gn21SortedTuple raw cell upperEntry)
      ⟨by simpa [hupper_raw] using hleft_upper,
        by simpa [hupper_raw] using hupper_right⟩
  have hleft_right : leftEndpoint < rightEndpoint := hleft_x.trans hx_right
  have hleft_right_real :
      (leftEndpoint : ℝ) < (rightEndpoint : ℝ) := by
    exact_mod_cast hleft_right
  have hactive : gn21FiniteNNIntervalTupleCellActive lower upper cell := by
    change (((leftEndpoint : ℝ) + (rightEndpoint : ℝ)) / 2) ∈
      gn21FiniteNNIntervalTuplePolicy lower upper
    apply Set.mem_iUnion.2
    refine ⟨source, ?_⟩
    constructor
    · have hleft_mid :
          (leftEndpoint : ℝ) <
            ((leftEndpoint : ℝ) + (rightEndpoint : ℝ)) / 2 := by
        linarith
      exact lt_of_le_of_lt (by exact_mod_cast hlower_le_left) hleft_mid
    · have hmid_right :
          ((leftEndpoint : ℝ) + (rightEndpoint : ℝ)) / 2 <
            (rightEndpoint : ℝ) := by
        linarith
      exact lt_of_lt_of_le hmid_right (by exact_mod_cast hright_le_upper)
  have hincluded :
      gn21FiniteNNIntervalTupleCellIncluded lower upper cell = true :=
    (gn21FiniteNNIntervalTupleCellIncluded_eq_true_iff
      lower upper cell).2 hactive
  apply Set.mem_iUnion.2
  refine ⟨cell, ?_⟩
  simp only [if_pos hincluded]
  exact ⟨by exact_mod_cast hleft_x, by exact_mod_cast hx_right⟩

/-- Retained sorted cells are an exact subset of the original finite interval union. -/
theorem gn21FiniteNNIntervalTupleNormalizedCellPolicy_subset {n : Nat}
    (lower upper : Fin n → NNReal) :
    gn21FiniteNNIntervalTupleNormalizedCellPolicy lower upper ⊆
      gn21FiniteNNIntervalTuplePolicy lower upper := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨cell, hcell⟩
  by_cases hincluded :
      gn21FiniteNNIntervalTupleCellIncluded lower upper cell = true
  · have hactive :
        gn21FiniteNNIntervalTupleCellActive lower upper cell :=
      (gn21FiniteNNIntervalTupleCellIncluded_eq_true_iff
        lower upper cell).1 hincluded
    apply gn21FiniteNNIntervalTuple_active_cell_subset
      lower upper cell hactive
    simpa [hincluded] using hcell
  · simp [hincluded] at hcell

/-- Any point omitted by normalization is one of the finitely many raw endpoints. -/
theorem gn21FiniteNNIntervalTuple_diff_normalizedCellPolicy_subset_endpoints
    {n : Nat} (lower upper : Fin n → NNReal) :
    gn21FiniteNNIntervalTuplePolicy lower upper \
        gn21FiniteNNIntervalTupleNormalizedCellPolicy lower upper ⊆
      Set.range (fun entry : Fin (2 * n) =>
        (gn21FiniteNNIntervalTupleRawEndpoints lower upper entry : ℝ)) := by
  intro x hx
  by_contra hnot_range
  have hne : ∀ entry : Fin (2 * n),
      x ≠ (gn21FiniteNNIntervalTupleRawEndpoints lower upper entry : ℝ) := by
    intro entry heq
    apply hnot_range
    exact ⟨entry, heq.symm⟩
  exact hx.2
    (mem_gn21FiniteNNIntervalTupleNormalizedCellPolicy_of_not_endpoint
      lower upper hx.1 hne)

/-- Finite interval normalization preserves the represented policy modulo null endpoints. -/
theorem policyAlmostEverywhereEq_finiteNNIntervalTuple_endpointVector
    (mu : Measure TripLength) [NoAtoms mu]
    {n : Nat} (hn : 0 < n) (lower upper : Fin n → NNReal) :
    policyAlmostEverywhereEq mu
      (gn21FiniteNNIntervalTuplePolicy lower upper)
      (gn21EndpointVectorPolicy
        (gn21FiniteNNIntervalTupleEndpointVector lower upper)) := by
  rw [gn21EndpointVectorPolicy_finiteNNIntervalTupleEndpointVector
    hn lower upper]
  apply policyAlmostEverywhereEq_of_diff_null mu
  · apply measure_mono_null
      (gn21FiniteNNIntervalTuple_diff_normalizedCellPolicy_subset_endpoints
        lower upper)
    exact (Set.finite_range fun entry : Fin (2 * n) =>
      (gn21FiniteNNIntervalTupleRawEndpoints lower upper entry : ℝ)).measure_zero mu
  · rw [Set.diff_eq_empty.2
      (gn21FiniteNNIntervalTupleNormalizedCellPolicy_subset lower upper)]
    exact measure_empty

/-- A nonempty open interval contained in positive trip lengths has nonnegative lower endpoint. -/
theorem lower_nonneg_of_Ioo_subset_acceptAllPolicy
    {lower upper : ℝ} (hlower_upper : lower < upper)
    (hsubset : Set.Ioo lower upper ⊆ acceptAllPolicy) :
    0 ≤ lower := by
  by_contra hnot
  have hlower_neg : lower < 0 := lt_of_not_ge hnot
  let cap : ℝ := min upper 0
  have hlower_cap : lower < cap := lt_min hlower_upper hlower_neg
  let x : ℝ := (lower + cap) / 2
  have hlower_x : lower < x := by
    dsimp [x]
    linarith
  have hx_cap : x < cap := by
    dsimp [x]
    linarith
  have hx_upper : x < upper := hx_cap.trans_le (min_le_left _ _)
  have hx_nonpos : x ≤ 0 :=
    le_trans (le_of_lt hx_cap) (min_le_right _ _)
  have hx_positive := hsubset ⟨hlower_x, hx_upper⟩
  have hx_zero_lt : 0 < x := by
    simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using
      hx_positive
  exact (not_lt_of_ge hx_nonpos) hx_zero_lt

/-- Feasibility of a finite interval policy forces every lower endpoint nonnegative. -/
theorem GN21FiniteIntervalPolicy.lower_nonneg_of_policy_subset_acceptAll
    (P : GN21FiniteIntervalPolicy) (hsubset : P.policy ⊆ acceptAllPolicy)
    (slot : P.index) :
    0 ≤ P.lower slot := by
  apply lower_nonneg_of_Ioo_subset_acceptAllPolicy (P.lower_lt_upper slot)
  intro x hx
  apply hsubset
  exact Set.mem_iUnion.2 ⟨slot, hx⟩

/-- Enumerate a finite interval policy's arbitrary finite index type. -/
noncomputable def GN21FiniteIntervalPolicy.indexEquivFin
    (P : GN21FiniteIntervalPolicy) : Fin P.complexity ≃ P.index := by
  letI := P.finite_index
  exact (Fintype.equivFin P.index).symm

/-- Enumerated nonnegative lower endpoints of a feasible finite interval policy. -/
noncomputable def GN21FiniteIntervalPolicy.nnLower
    (P : GN21FiniteIntervalPolicy) (hsubset : P.policy ⊆ acceptAllPolicy) :
    Fin P.complexity → NNReal := fun slot =>
  let source := P.indexEquivFin slot
  ⟨P.lower source, P.lower_nonneg_of_policy_subset_acceptAll hsubset source⟩

/-- Enumerated nonnegative upper endpoints of a feasible finite interval policy. -/
noncomputable def GN21FiniteIntervalPolicy.nnUpper
    (P : GN21FiniteIntervalPolicy) (hsubset : P.policy ⊆ acceptAllPolicy) :
    Fin P.complexity → NNReal := fun slot =>
  let source := P.indexEquivFin slot
  ⟨P.upper source,
    (P.lower_nonneg_of_policy_subset_acceptAll hsubset source).trans
      (le_of_lt (P.lower_lt_upper source))⟩

/-- Enumeration preserves the finite interval policy exactly. -/
theorem GN21FiniteIntervalPolicy.policy_nn_endpoints
    (P : GN21FiniteIntervalPolicy) (hsubset : P.policy ⊆ acceptAllPolicy) :
    gn21FiniteNNIntervalTuplePolicy
        (P.nnLower hsubset) (P.nnUpper hsubset) = P.policy := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨slot, hslot⟩
    apply Set.mem_iUnion.2
    refine ⟨P.indexEquivFin slot, ?_⟩
    simpa [GN21FiniteIntervalPolicy.nnLower,
      GN21FiniteIntervalPolicy.nnUpper] using hslot
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨source, hsource⟩
    let slot : Fin P.complexity := P.indexEquivFin.symm source
    apply Set.mem_iUnion.2
    refine ⟨slot, ?_⟩
    simpa [GN21FiniteIntervalPolicy.nnLower,
      GN21FiniteIntervalPolicy.nnUpper, slot] using hsource

/-- A nonempty feasible finite interval policy has a positive enumerated complexity. -/
theorem GN21FiniteIntervalPolicy.complexity_pos
    (P : GN21FiniteIntervalPolicy) [Nonempty P.index] :
    0 < P.complexity := by
  letI := P.finite_index
  exact Fintype.card_pos

/-- Existing finite approximants normalize to ordered endpoint vectors modulo null endpoints. -/
theorem GN21FiniteIntervalPolicy.policyAlmostEverywhereEq_endpointVector
    (mu : Measure TripLength) [NoAtoms mu]
    (P : GN21FiniteIntervalPolicy) [Nonempty P.index]
    (hsubset : P.policy ⊆ acceptAllPolicy) :
    policyAlmostEverywhereEq mu P.policy
      (gn21EndpointVectorPolicy
        (gn21FiniteNNIntervalTupleEndpointVector
          (P.nnLower hsubset) (P.nnUpper hsubset))) := by
  rw [← P.policy_nn_endpoints hsubset]
  exact policyAlmostEverywhereEq_finiteNNIntervalTuple_endpointVector
    mu P.complexity_pos (P.nnLower hsubset) (P.nnUpper hsubset)

/--
A reward-close Step 1 approximant is nonempty when its tolerance is smaller
than the source policy's strict reward advantage over the empty policy.
-/
theorem exists_gn21FiniteIntervalPolicy_reward_close_nonempty
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop]
    (Rhat : SingleStateReward) {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hcontinuous : GN21SymmDiffContinuousAt mu Rhat sigma)
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_gap : epsilon < Rhat sigma - Rhat ∅) :
    ∃ P : GN21FiniteIntervalPolicy,
      Nonempty P.index ∧ P.policy ⊆ sigma ∧
        |Rhat P.policy - Rhat sigma| < epsilon := by
  rcases exists_gn21FiniteIntervalPolicy_reward_close
      mu Rhat hsigma_open hcontinuous hepsilon_pos with
    ⟨P, hP_subset, hP_close⟩
  have hP_nonempty : Nonempty P.index := by
    by_contra hnot
    have hP_empty : P.policy = (∅ : TripPolicy) := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      rcases Set.mem_iUnion.1 hx with ⟨slot, _hslot⟩
      exact hnot ⟨slot⟩
    rw [hP_empty] at hP_close
    have hgap_lt : Rhat sigma - Rhat ∅ < epsilon := by
      have hleft := (abs_lt.1 hP_close).1
      linarith
    exact (not_lt_of_ge (le_of_lt hepsilon_gap)) hgap_lt
  exact ⟨P, hP_nonempty, hP_subset, hP_close⟩

theorem gn21EndpointVectorPolicy_open {n : Nat}
    (endpoints : GN21EndpointVector n) :
    IsOpen (gn21EndpointVectorPolicy endpoints) := by
  unfold gn21EndpointVectorPolicy
  exact isOpen_iUnion fun i =>
    gn21ExtendedMiddlePolicy_open
      (endpoints (gn21LowerEndpointIndex i))
      (endpoints (gn21UpperEndpointIndex i))

theorem gn21EndpointVectorPolicy_measurable {n : Nat}
    (endpoints : GN21EndpointVector n) :
    MeasurableSet (gn21EndpointVectorPolicy endpoints) :=
  (gn21EndpointVectorPolicy_open endpoints).measurableSet

theorem gn21EndpointVectorPolicy_subset_acceptAll {n : Nat}
    (endpoints : GN21EndpointVector n) :
    gn21EndpointVectorPolicy endpoints ⊆ acceptAllPolicy := by
  intro τ hτ
  rcases Set.mem_iUnion.1 hτ with ⟨i, hi⟩
  exact gn21ExtendedMiddlePolicy_subset_acceptAll
    (endpoints (gn21LowerEndpointIndex i))
    (endpoints (gn21UpperEndpointIndex i)) hi

/-- Remove the first interval slot from an endpoint vector. -/
def gn21EndpointVectorTail {n : Nat}
    (endpoints : GN21EndpointVector (n + 1)) : GN21EndpointVector n :=
  fun j => endpoints ⟨j.1 + 2, by omega⟩

/-- Endpoint-vector policy decomposition into the first interval and the tail. -/
theorem gn21EndpointVectorPolicy_succ {n : Nat}
    (endpoints : GN21EndpointVector (n + 1)) :
    gn21EndpointVectorPolicy endpoints =
      gn21ExtendedMiddlePolicy (endpoints 0) (endpoints 1) ∪
        gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints) := by
  ext τ
  constructor
  · intro hτ
    rcases Set.mem_iUnion.1 hτ with ⟨i, hi⟩
    have hmem : ∀ i : Fin (n + 1),
        τ ∈ gn21ExtendedMiddlePolicy
            (endpoints (gn21LowerEndpointIndex i))
            (endpoints (gn21UpperEndpointIndex i)) →
          τ ∈ gn21ExtendedMiddlePolicy (endpoints 0) (endpoints 1) ∪
            gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints) := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hzero
        exact Or.inl (by
          simpa [gn21LowerEndpointIndex, gn21UpperEndpointIndex] using hzero)
      · intro hsucc
        exact Or.inr (Set.mem_iUnion.2 ⟨j, by
          simpa [gn21EndpointVectorTail, gn21LowerEndpointIndex,
            gn21UpperEndpointIndex] using hsucc⟩)
    exact hmem i hi
  · rintro (hfirst | htail)
    · exact Set.mem_iUnion.2 ⟨0, by
        simpa [gn21LowerEndpointIndex, gn21UpperEndpointIndex] using hfirst⟩
    · rcases Set.mem_iUnion.1 htail with ⟨j, hj⟩
      exact Set.mem_iUnion.2 ⟨Fin.succ j, by
        simpa [gn21EndpointVectorTail, gn21LowerEndpointIndex,
          gn21UpperEndpointIndex] using hj⟩

theorem gn21EndpointVectorTail_ordered {n : Nat}
    {endpoints : GN21EndpointVector (n + 1)}
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (n + 1)) :
    gn21EndpointVectorTail endpoints ∈ gn21OrderedEndpointVectors n := by
  intro i j hij
  apply hordered
  apply Fin.mk_le_mk.2
  change i.1 + 2 ≤ j.1 + 2
  omega

/-- Coordinate `side` of an interval slot in the flattened endpoint vector. -/
def gn21EndpointCoordinate {n : Nat}
    (slot : Fin n) (side : Fin 2) : Fin (2 * n) :=
  Fin.cast (Nat.mul_comm n 2) (finProdFinEquiv (slot, side))

@[simp] theorem gn21EndpointCoordinate_zero {n : Nat} (slot : Fin n) :
    gn21EndpointCoordinate slot 0 = gn21LowerEndpointIndex slot := by
  apply Fin.ext
  simp [gn21EndpointCoordinate, gn21LowerEndpointIndex, finProdFinEquiv]

@[simp] theorem gn21EndpointCoordinate_one {n : Nat} (slot : Fin n) :
    gn21EndpointCoordinate slot 1 = gn21UpperEndpointIndex slot := by
  apply Fin.ext
  simp [gn21EndpointCoordinate, gn21UpperEndpointIndex, finProdFinEquiv]
  omega

/-- Remove one interval slot and its two coordinates from an endpoint vector. -/
def gn21EraseInterval {n : Nat}
    (endpoints : GN21EndpointVector (n + 1)) (removed : Fin (n + 1)) :
    GN21EndpointVector n := fun coordinate =>
  let pair : Fin n × Fin 2 :=
    finProdFinEquiv.symm
      (Fin.cast (Nat.mul_comm 2 n) coordinate)
  endpoints (gn21EndpointCoordinate (removed.succAbove pair.1) pair.2)

theorem gn21_succAbove_monotone {n : Nat} (removed : Fin (n + 1)) :
    Monotone removed.succAbove := by
  intro i j hij
  by_cases hi : i.castSucc < removed
  · rw [Fin.succAbove_of_castSucc_lt removed i hi]
    by_cases hj : j.castSucc < removed
    · rw [Fin.succAbove_of_castSucc_lt removed j hj]
      exact Fin.castSucc_le_castSucc_iff.mpr hij
    · rw [Fin.succAbove_of_le_castSucc removed j (le_of_not_gt hj)]
      exact (Fin.castSucc_le_castSucc_iff.mpr hij).trans
        (Fin.castSucc_le_succ j)
  · have hremoved_i : removed ≤ i.castSucc := le_of_not_gt hi
    have hremoved_j : removed ≤ j.castSucc :=
      hremoved_i.trans (Fin.castSucc_le_castSucc_iff.mpr hij)
    rw [Fin.succAbove_of_le_castSucc removed i hremoved_i,
      Fin.succAbove_of_le_castSucc removed j hremoved_j]
    exact Fin.succ_le_succ_iff.mpr hij

@[simp] theorem gn21EraseInterval_coordinate {n : Nat}
    (endpoints : GN21EndpointVector (n + 1)) (removed : Fin (n + 1))
    (slot : Fin n) (side : Fin 2) :
    gn21EraseInterval endpoints removed (gn21EndpointCoordinate slot side) =
      endpoints (gn21EndpointCoordinate (removed.succAbove slot) side) := by
  have hcast :
      Fin.cast (Nat.mul_comm 2 n) (gn21EndpointCoordinate slot side) =
        finProdFinEquiv (slot, side) := by
    apply Fin.ext
    simp [gn21EndpointCoordinate, finProdFinEquiv]
  unfold gn21EraseInterval
  rw [hcast]
  simp

theorem gn21EndpointCoordinate_succAbove_mono {n : Nat}
    (removed : Fin (n + 1)) (left right : Fin n × Fin 2)
    (hleft_right :
      gn21EndpointCoordinate left.1 left.2 ≤
        gn21EndpointCoordinate right.1 right.2) :
    gn21EndpointCoordinate (removed.succAbove left.1) left.2 ≤
      gn21EndpointCoordinate (removed.succAbove right.1) right.2 := by
  have hflat := hleft_right
  change left.2.1 + 2 * left.1.1 ≤ right.2.1 + 2 * right.1.1 at hflat
  have hslot : left.1 ≤ right.1 := by
    apply Fin.mk_le_mk.2
    change left.1.1 ≤ right.1.1
    have hleft_side := left.2.isLt
    have hright_side := right.2.isLt
    omega
  apply Fin.mk_le_mk.2
  change left.2.1 + 2 * (removed.succAbove left.1).1 ≤
    right.2.1 + 2 * (removed.succAbove right.1).1
  by_cases hslots : left.1 = right.1
  · have hslots_value := congrArg Fin.val hslots
    have hsides : left.2.1 ≤ right.2.1 := by omega
    rw [hslots]
    exact Nat.add_le_add_right hsides _
  · have hslot_strict : left.1 < right.1 := lt_of_le_of_ne hslot hslots
    have hsucc_le := gn21_succAbove_monotone removed hslot
    have hsucc_ne :
        removed.succAbove left.1 ≠ removed.succAbove right.1 := by
      exact fun heq => hslots (Fin.succAbove_right_injective heq)
    have hsucc_strict :
        removed.succAbove left.1 < removed.succAbove right.1 :=
      lt_of_le_of_ne hsucc_le hsucc_ne
    have hleft_side := left.2.isLt
    have hright_side := right.2.isLt
    omega

theorem gn21EraseInterval_ordered {n : Nat}
    {endpoints : GN21EndpointVector (n + 1)}
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (n + 1))
    (removed : Fin (n + 1)) :
    gn21EraseInterval endpoints removed ∈ gn21OrderedEndpointVectors n := by
  intro left right hleft_right
  let leftPair : Fin n × Fin 2 :=
    finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 n) left)
  let rightPair : Fin n × Fin 2 :=
    finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 2 n) right)
  have hleft_coordinate :
      gn21EndpointCoordinate leftPair.1 leftPair.2 = left := by
    have hpair :
        finProdFinEquiv leftPair = Fin.cast (Nat.mul_comm 2 n) left := by
      exact finProdFinEquiv.apply_symm_apply _
    unfold gn21EndpointCoordinate
    rw [show (leftPair.1, leftPair.2) = leftPair by cases leftPair; rfl,
      hpair]
    rfl
  have hright_coordinate :
      gn21EndpointCoordinate rightPair.1 rightPair.2 = right := by
    have hpair :
        finProdFinEquiv rightPair = Fin.cast (Nat.mul_comm 2 n) right := by
      exact finProdFinEquiv.apply_symm_apply _
    unfold gn21EndpointCoordinate
    rw [show (rightPair.1, rightPair.2) = rightPair by cases rightPair; rfl,
      hpair]
    rfl
  rw [← hleft_coordinate, ← hright_coordinate] at hleft_right ⊢
  simp only [gn21EraseInterval_coordinate]
  exact hordered
    (gn21EndpointCoordinate_succAbove_mono
      removed leftPair rightPair hleft_right)

@[simp] theorem gn21EraseInterval_lower {n : Nat}
    (endpoints : GN21EndpointVector (n + 1)) (removed : Fin (n + 1))
    (slot : Fin n) :
    gn21EraseInterval endpoints removed (gn21LowerEndpointIndex slot) =
      endpoints (gn21LowerEndpointIndex (removed.succAbove slot)) := by
  have hcast :
      Fin.cast (Nat.mul_comm 2 n) (gn21LowerEndpointIndex slot) =
        finProdFinEquiv (slot, (0 : Fin 2)) := by
    apply Fin.ext
    simp [gn21LowerEndpointIndex, finProdFinEquiv]
  unfold gn21EraseInterval
  rw [hcast]
  simp

@[simp] theorem gn21EraseInterval_upper {n : Nat}
    (endpoints : GN21EndpointVector (n + 1)) (removed : Fin (n + 1))
    (slot : Fin n) :
    gn21EraseInterval endpoints removed (gn21UpperEndpointIndex slot) =
      endpoints (gn21UpperEndpointIndex (removed.succAbove slot)) := by
  have hcast :
      Fin.cast (Nat.mul_comm 2 n) (gn21UpperEndpointIndex slot) =
        finProdFinEquiv (slot, (1 : Fin 2)) := by
    apply Fin.ext
    simp [gn21UpperEndpointIndex, finProdFinEquiv]
    omega
  unfold gn21EraseInterval
  rw [hcast]
  simp

/-- Deleting a collapsed interval slot preserves the represented policy exactly. -/
theorem gn21EndpointVectorPolicy_eraseInterval_of_collapsed {n : Nat}
    (endpoints : GN21EndpointVector (n + 1)) (removed : Fin (n + 1))
    (hcollapsed :
      endpoints (gn21LowerEndpointIndex removed) =
        endpoints (gn21UpperEndpointIndex removed)) :
    gn21EndpointVectorPolicy (gn21EraseInterval endpoints removed) =
      gn21EndpointVectorPolicy endpoints := by
  ext τ
  constructor
  · intro hτ
    rcases Set.mem_iUnion.1 hτ with ⟨slot, hslot⟩
    rw [gn21EraseInterval_lower, gn21EraseInterval_upper] at hslot
    exact Set.mem_iUnion.2 ⟨removed.succAbove slot, hslot⟩
  · intro hτ
    rcases Set.mem_iUnion.1 hτ with ⟨slot, hslot⟩
    rcases Fin.eq_self_or_eq_succAbove removed slot with hremoved | ⟨kept, hkept⟩
    · subst slot
      rw [hcollapsed, gn21ExtendedMiddlePolicy_self] at hslot
      exact False.elim hslot
    · subst slot
      exact Set.mem_iUnion.2 ⟨kept, by
        rw [gn21EraseInterval_lower, gn21EraseInterval_upper]
        exact hslot⟩

/--
Prepare a touching-gap merge by extending the left interval through the right
interval and collapsing the right slot at its old upper endpoint.
-/
def gn21GapMergePreparation {n : Nat}
    (endpoints : GN21EndpointVector (n + 2)) (gap : Fin (n + 1)) :
    GN21EndpointVector (n + 2) := fun coordinate =>
  if coordinate = gn21UpperEndpointIndex (Fin.castSucc gap) ∨
      coordinate = gn21LowerEndpointIndex (Fin.succ gap) then
    endpoints (gn21UpperEndpointIndex (Fin.succ gap))
  else endpoints coordinate

theorem gn21GapMergePreparation_ordered {n : Nat}
    {endpoints : GN21EndpointVector (n + 2)}
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (n + 2))
    (gap : Fin (n + 1)) :
    gn21GapMergePreparation endpoints gap ∈
      gn21OrderedEndpointVectors (n + 2) := by
  intro left right hleft_right
  by_cases hleft :
      left = gn21UpperEndpointIndex (Fin.castSucc gap) ∨
        left = gn21LowerEndpointIndex (Fin.succ gap)
  · by_cases hright :
      right = gn21UpperEndpointIndex (Fin.castSucc gap) ∨
        right = gn21LowerEndpointIndex (Fin.succ gap)
    · simp [gn21GapMergePreparation, hleft, hright]
    · rw [gn21GapMergePreparation, if_pos hleft,
        gn21GapMergePreparation, if_neg hright]
      apply hordered
      apply Fin.mk_le_mk.2
      change 2 * (gap.1 + 1) + 1 ≤ right.1
      have hleft_right_val : left.1 ≤ right.1 := hleft_right
      have hright_ne_left_val : right.1 ≠ 2 * gap.1 + 1 := by
        intro heq
        apply hright
        left
        apply Fin.ext
        simpa [gn21UpperEndpointIndex] using heq
      have hright_ne_right_val : right.1 ≠ 2 * (gap.1 + 1) := by
        intro heq
        apply hright
        right
        apply Fin.ext
        simpa [gn21LowerEndpointIndex] using heq
      rcases hleft with hleft | hleft
      · have hleft_val := congrArg Fin.val hleft
        simp [gn21UpperEndpointIndex] at hleft_val
        omega
      · have hleft_val := congrArg Fin.val hleft
        simp [gn21LowerEndpointIndex] at hleft_val
        omega
  · by_cases hright :
      right = gn21UpperEndpointIndex (Fin.castSucc gap) ∨
        right = gn21LowerEndpointIndex (Fin.succ gap)
    · rw [gn21GapMergePreparation, if_neg hleft,
        gn21GapMergePreparation, if_pos hright]
      apply hordered
      apply Fin.mk_le_mk.2
      have hleft_right_val : left.1 ≤ right.1 := hleft_right
      change left.1 ≤ 2 * (gap.1 + 1) + 1
      rcases hright with hright | hright
      · have hright_val := congrArg Fin.val hright
        simp [gn21UpperEndpointIndex] at hright_val
        omega
      · have hright_val := congrArg Fin.val hright
        simp [gn21LowerEndpointIndex] at hright_val
        omega
    · simp [gn21GapMergePreparation, hleft, hright]
      exact hordered hleft_right

@[simp] theorem gn21GapMergePreparation_left_lower {n : Nat}
    (endpoints : GN21EndpointVector (n + 2)) (gap : Fin (n + 1)) :
    gn21GapMergePreparation endpoints gap
        (gn21LowerEndpointIndex (Fin.castSucc gap)) =
      endpoints (gn21LowerEndpointIndex (Fin.castSucc gap)) := by
  rw [gn21GapMergePreparation, if_neg]
  intro h
  rcases h with h | h <;>
    have hval := congrArg Fin.val h <;>
    simp [gn21LowerEndpointIndex, gn21UpperEndpointIndex] at hval

@[simp] theorem gn21GapMergePreparation_left_upper {n : Nat}
    (endpoints : GN21EndpointVector (n + 2)) (gap : Fin (n + 1)) :
    gn21GapMergePreparation endpoints gap
        (gn21UpperEndpointIndex (Fin.castSucc gap)) =
      endpoints (gn21UpperEndpointIndex (Fin.succ gap)) := by
  simp [gn21GapMergePreparation]

@[simp] theorem gn21GapMergePreparation_right_lower {n : Nat}
    (endpoints : GN21EndpointVector (n + 2)) (gap : Fin (n + 1)) :
    gn21GapMergePreparation endpoints gap
        (gn21LowerEndpointIndex (Fin.succ gap)) =
      endpoints (gn21UpperEndpointIndex (Fin.succ gap)) := by
  simp [gn21GapMergePreparation]

@[simp] theorem gn21GapMergePreparation_right_upper {n : Nat}
    (endpoints : GN21EndpointVector (n + 2)) (gap : Fin (n + 1)) :
    gn21GapMergePreparation endpoints gap
        (gn21UpperEndpointIndex (Fin.succ gap)) =
      endpoints (gn21UpperEndpointIndex (Fin.succ gap)) := by
  rw [gn21GapMergePreparation, if_neg]
  intro h
  rcases h with h | h <;>
    have hval := congrArg Fin.val h <;>
    simp [gn21LowerEndpointIndex, gn21UpperEndpointIndex] at hval

theorem gn21GapMergePreparation_lower_of_ne_right {n : Nat}
    (endpoints : GN21EndpointVector (n + 2)) (gap : Fin (n + 1))
    (slot : Fin (n + 2)) (hright : slot ≠ Fin.succ gap) :
    gn21GapMergePreparation endpoints gap
        (gn21LowerEndpointIndex slot) =
      endpoints (gn21LowerEndpointIndex slot) := by
  rw [gn21GapMergePreparation, if_neg]
  intro h
  rcases h with h | h
  · have hval := congrArg Fin.val h
    simp [gn21LowerEndpointIndex, gn21UpperEndpointIndex] at hval
    omega
  · apply hright
    apply Fin.ext
    have hval := congrArg Fin.val h
    simpa [gn21LowerEndpointIndex] using hval

theorem gn21GapMergePreparation_upper_of_ne_left {n : Nat}
    (endpoints : GN21EndpointVector (n + 2)) (gap : Fin (n + 1))
    (slot : Fin (n + 2)) (hleft : slot ≠ Fin.castSucc gap) :
    gn21GapMergePreparation endpoints gap
        (gn21UpperEndpointIndex slot) =
      endpoints (gn21UpperEndpointIndex slot) := by
  rw [gn21GapMergePreparation, if_neg]
  intro h
  rcases h with h | h
  · apply hleft
    apply Fin.ext
    have hval := congrArg Fin.val h
    simpa [gn21UpperEndpointIndex] using hval
  · have hval := congrArg Fin.val h
    simp [gn21LowerEndpointIndex, gn21UpperEndpointIndex] at hval
    omega

theorem gn21GapMergePreparation_interval_eq_of_ne {n : Nat}
    (endpoints : GN21EndpointVector (n + 2)) (gap : Fin (n + 1))
    (slot : Fin (n + 2))
    (hleft : slot ≠ Fin.castSucc gap) (hright : slot ≠ Fin.succ gap) :
    gn21ExtendedMiddlePolicy
        (gn21GapMergePreparation endpoints gap
          (gn21LowerEndpointIndex slot))
        (gn21GapMergePreparation endpoints gap
          (gn21UpperEndpointIndex slot)) =
      gn21ExtendedMiddlePolicy
        (endpoints (gn21LowerEndpointIndex slot))
        (endpoints (gn21UpperEndpointIndex slot)) := by
  have hlower :
      gn21GapMergePreparation endpoints gap
          (gn21LowerEndpointIndex slot) =
        endpoints (gn21LowerEndpointIndex slot) := by
    rw [gn21GapMergePreparation, if_neg]
    intro h
    rcases h with h | h
    · have hval := congrArg Fin.val h
      simp [gn21LowerEndpointIndex, gn21UpperEndpointIndex] at hval
      omega
    · apply hright
      apply Fin.ext
      have hval := congrArg Fin.val h
      simpa [gn21LowerEndpointIndex] using hval
  have hupper :
      gn21GapMergePreparation endpoints gap
          (gn21UpperEndpointIndex slot) =
        endpoints (gn21UpperEndpointIndex slot) := by
    rw [gn21GapMergePreparation, if_neg]
    intro h
    rcases h with h | h
    · apply hleft
      apply Fin.ext
      have hval := congrArg Fin.val h
      simpa [gn21UpperEndpointIndex] using hval
    · have hval := congrArg Fin.val h
      simp [gn21LowerEndpointIndex, gn21UpperEndpointIndex] at hval
      omega
  rw [hlower, hupper]

theorem policyAlmostEverywhereEq_gapMergePreparation {n : Nat}
    (mu : Measure TripLength) [NoAtoms mu]
    {endpoints : GN21EndpointVector (n + 2)}
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (n + 2))
    (gap : Fin (n + 1))
    (htouching :
      endpoints (gn21UpperEndpointIndex (Fin.castSucc gap)) =
        endpoints (gn21LowerEndpointIndex (Fin.succ gap))) :
    policyAlmostEverywhereEq mu (gn21EndpointVectorPolicy endpoints)
      (gn21EndpointVectorPolicy (gn21GapMergePreparation endpoints gap)) := by
  let leftSlot : Fin (n + 2) := Fin.castSucc gap
  let rightSlot : Fin (n + 2) := Fin.succ gap
  let original : Fin (n + 2) → TripPolicy := fun slot =>
    gn21ExtendedMiddlePolicy
      (endpoints (gn21LowerEndpointIndex slot))
      (endpoints (gn21UpperEndpointIndex slot))
  let prepared : Fin (n + 2) → TripPolicy := fun slot =>
    gn21ExtendedMiddlePolicy
      (gn21GapMergePreparation endpoints gap
        (gn21LowerEndpointIndex slot))
      (gn21GapMergePreparation endpoints gap
        (gn21UpperEndpointIndex slot))
  have hsame : ∀ slot, slot ≠ leftSlot → slot ≠ rightSlot →
      original slot = prepared slot := by
    intro slot hleft hright
    exact (gn21GapMergePreparation_interval_eq_of_ne
      endpoints gap slot hleft hright).symm
  have hlower_middle :
      endpoints (gn21LowerEndpointIndex leftSlot) ≤
        endpoints (gn21LowerEndpointIndex rightSlot) := by
    apply hordered
    apply Fin.mk_le_mk.2
    simp [leftSlot, rightSlot]
  have hmiddle_upper :
      endpoints (gn21LowerEndpointIndex rightSlot) ≤
        endpoints (gn21UpperEndpointIndex rightSlot) := by
    apply hordered
    apply Fin.mk_le_mk.2
    simp [rightSlot]
  have hpair : policyAlmostEverywhereEq mu
      (original leftSlot ∪ original rightSlot)
      (prepared leftSlot ∪ prepared rightSlot) := by
    have hmerge :=
      policyAlmostEverywhereEq_extendedMiddle_union_touching mu
        hlower_middle hmiddle_upper
    simpa [original, prepared, leftSlot, rightSlot, htouching] using hmerge
  have hall := policyAlmostEverywhereEq_iUnion_of_two
    mu original prepared leftSlot rightSlot hsame hpair
  simpa [original, prepared, gn21EndpointVectorPolicy] using hall

/-- Close a touching gap and remove the resulting collapsed right slot. -/
def gn21MergeGap {n : Nat}
    (endpoints : GN21EndpointVector (n + 2)) (gap : Fin (n + 1)) :
    GN21EndpointVector (n + 1) :=
  gn21EraseInterval (gn21GapMergePreparation endpoints gap) (Fin.succ gap)

theorem gn21MergeGap_ordered {n : Nat}
    {endpoints : GN21EndpointVector (n + 2)}
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (n + 2))
    (gap : Fin (n + 1)) :
    gn21MergeGap endpoints gap ∈ gn21OrderedEndpointVectors (n + 1) :=
  gn21EraseInterval_ordered
    (gn21GapMergePreparation_ordered hordered gap) (Fin.succ gap)

theorem policyAlmostEverywhereEq_mergeGap {n : Nat}
    (mu : Measure TripLength) [NoAtoms mu]
    {endpoints : GN21EndpointVector (n + 2)}
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (n + 2))
    (gap : Fin (n + 1))
    (htouching :
      endpoints (gn21UpperEndpointIndex (Fin.castSucc gap)) =
        endpoints (gn21LowerEndpointIndex (Fin.succ gap))) :
    policyAlmostEverywhereEq mu (gn21EndpointVectorPolicy endpoints)
      (gn21EndpointVectorPolicy (gn21MergeGap endpoints gap)) := by
  have hprepare := policyAlmostEverywhereEq_gapMergePreparation
    mu hordered gap htouching
  have hcollapsed :
      gn21GapMergePreparation endpoints gap
          (gn21LowerEndpointIndex (Fin.succ gap)) =
        gn21GapMergePreparation endpoints gap
          (gn21UpperEndpointIndex (Fin.succ gap)) := by
    simp
  rw [gn21MergeGap,
    gn21EndpointVectorPolicy_eraseInterval_of_collapsed
      (gn21GapMergePreparation endpoints gap) (Fin.succ gap) hcollapsed]
  exact hprepare

theorem isClosed_gn21OrderedEndpointVectors (n : Nat) :
    IsClosed (gn21OrderedEndpointVectors n) := by
  unfold gn21OrderedEndpointVectors
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun i =>
    isClosed_iInter fun j =>
      isClosed_iInter fun _hij =>
        isClosed_le (continuous_apply i) (continuous_apply j)

theorem isCompact_gn21OrderedEndpointVectors (n : Nat) :
    IsCompact (gn21OrderedEndpointVectors n) :=
  (isClosed_gn21OrderedEndpointVectors n).isCompact

theorem gn21OrderedEndpointVectors_nonempty (n : Nat) :
    (gn21OrderedEndpointVectors n).Nonempty := by
  refine ⟨fun _ => 0, ?_⟩
  intro i j hij
  exact le_rfl

/-- A continuous reward on the compact ordered endpoint domain has a maximizer. -/
theorem exists_gn21OrderedEndpointVector_reward_maximum
    (n : Nat) (Rhat : SingleStateReward)
    (hcontinuous :
      ContinuousOn
        (fun endpoints : GN21EndpointVector n =>
          Rhat (gn21EndpointVectorPolicy endpoints))
        (gn21OrderedEndpointVectors n)) :
    ∃ endpoints ∈ gn21OrderedEndpointVectors n,
      ∀ candidate ∈ gn21OrderedEndpointVectors n,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints) := by
  rcases (isCompact_gn21OrderedEndpointVectors n).exists_isMaxOn
      (gn21OrderedEndpointVectors_nonempty n) hcontinuous with
    ⟨endpoints, hordered, hmax⟩
  rw [isMaxOn_iff] at hmax
  exact ⟨endpoints, hordered, hmax⟩

/-- Replace one coordinate of an endpoint vector by a finite real endpoint. -/
def gn21UpdateEndpoint {n : Nat} (endpoints : GN21EndpointVector n)
    (coordinate : Fin (2 * n)) (value : ℝ) : GN21EndpointVector n :=
  Function.update endpoints coordinate (ENNReal.ofReal value)

/-- Updating a coordinate between all preceding and following coordinates preserves order. -/
theorem gn21UpdateEndpoint_mem_ordered
    {n : Nat} {endpoints : GN21EndpointVector n}
    (hordered : endpoints ∈ gn21OrderedEndpointVectors n)
    (coordinate : Fin (2 * n)) (value : ℝ)
    (hbefore :
      ∀ j : Fin (2 * n), j < coordinate →
        endpoints j ≤ ENNReal.ofReal value)
    (hafter :
      ∀ j : Fin (2 * n), coordinate < j →
        ENNReal.ofReal value ≤ endpoints j) :
    gn21UpdateEndpoint endpoints coordinate value ∈
      gn21OrderedEndpointVectors n := by
  intro i j hij
  by_cases hi : i = coordinate
  · subst i
    by_cases hj : j = coordinate
    · subst j
      exact le_rfl
    · have hcj : coordinate < j := lt_of_le_of_ne hij (Ne.symm hj)
      simpa [gn21UpdateEndpoint, Function.update_self,
        Function.update_of_ne hj] using hafter j hcj
  · by_cases hj : j = coordinate
    · subst j
      have hic : i < coordinate := lt_of_le_of_ne hij hi
      simpa [gn21UpdateEndpoint, Function.update_self,
        Function.update_of_ne hi] using hbefore i hic
    · simpa [gn21UpdateEndpoint, Function.update_of_ne hi,
        Function.update_of_ne hj] using hordered hij

/--
At a maximizing ordered endpoint vector, any endpoint coordinate that can move
in a two-sided real neighborhood has zero derivative.  This is the compact-max
replacement for the source proof's informal endpoint-switching trajectories.
-/
theorem endpoint_derivative_eq_zero_of_ordered_vector_maximum
    {n : Nat} (Rhat : SingleStateReward)
    {endpoints : GN21EndpointVector n}
    (hmax :
      ∀ candidate ∈ gn21OrderedEndpointVectors n,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (coordinate : Fin (2 * n))
    {lower value upper derivativeValue : ℝ}
    (hcoordinate : endpoints coordinate = ENNReal.ofReal value)
    (hlower : lower < value) (hupper : value < upper)
    (hfeasible :
      ∀ x ∈ Set.Ioo lower upper,
        gn21UpdateEndpoint endpoints coordinate x ∈
          gn21OrderedEndpointVectors n)
    (hderiv :
      HasDerivAt
        (fun x =>
          Rhat (gn21EndpointVectorPolicy
            (gn21UpdateEndpoint endpoints coordinate x)))
        derivativeValue value) :
    derivativeValue = 0 := by
  have hupdate_value :
      gn21UpdateEndpoint endpoints coordinate value = endpoints := by
    unfold gn21UpdateEndpoint
    rw [← hcoordinate]
    exact Function.update_eq_self coordinate endpoints
  have hlocal :
      IsLocalMax
        (fun x =>
          Rhat (gn21EndpointVectorPolicy
            (gn21UpdateEndpoint endpoints coordinate x))) value := by
    filter_upwards [Ioo_mem_nhds hlower hupper] with x hx
    simpa [hupdate_value] using hmax _ (hfeasible x hx)
  exact hlocal.hasDerivAt_eq_zero hderiv

/-- Real lower and upper coordinate bounds provide the feasible neighborhood above. -/
theorem endpoint_derivative_eq_zero_of_ordered_vector_maximum_of_real_bounds
    {n : Nat} (Rhat : SingleStateReward)
    {endpoints : GN21EndpointVector n}
    (hordered : endpoints ∈ gn21OrderedEndpointVectors n)
    (hmax :
      ∀ candidate ∈ gn21OrderedEndpointVectors n,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (coordinate : Fin (2 * n))
    {lower value upper derivativeValue : ℝ}
    (hcoordinate : endpoints coordinate = ENNReal.ofReal value)
    (hlower : lower < value) (hupper : value < upper)
    (hbefore :
      ∀ j : Fin (2 * n), j < coordinate →
        endpoints j ≤ ENNReal.ofReal lower)
    (hafter :
      ∀ j : Fin (2 * n), coordinate < j →
        ENNReal.ofReal upper ≤ endpoints j)
    (hderiv :
      HasDerivAt
        (fun x =>
          Rhat (gn21EndpointVectorPolicy
            (gn21UpdateEndpoint endpoints coordinate x)))
        derivativeValue value) :
    derivativeValue = 0 := by
  apply endpoint_derivative_eq_zero_of_ordered_vector_maximum
      Rhat hmax coordinate hcoordinate hlower hupper
  · intro x hx
    apply gn21UpdateEndpoint_mem_ordered hordered coordinate x
    · intro j hj
      exact (hbefore j hj).trans
        (ENNReal.ofReal_mono (le_of_lt hx.1))
    · intro j hj
      exact (ENNReal.ofReal_mono (le_of_lt hx.2)).trans
        (hafter j hj)
  · exact hderiv

/-!
The next two lemmas record the one-sided Fermat conditions needed when an
ordered endpoint is blocked on only one side by a neighboring coordinate or a
source boundary.  They work for an arbitrary endpoint-vector domain, so the
same proof applies to every shape-specific compact domain below.
-/

theorem endpoint_derivative_nonpos_of_endpoint_domain_maximum
    {n : Nat} (Rhat : SingleStateReward)
    {domain : Set (GN21EndpointVector n)}
    {endpoints : GN21EndpointVector n}
    (hmax :
      ∀ candidate ∈ domain,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (coordinate : Fin (2 * n))
    {value upper derivativeValue : ℝ}
    (hcoordinate : endpoints coordinate = ENNReal.ofReal value)
    (hupper : value < upper)
    (hfeasible :
      ∀ x ∈ Set.Ioo value upper,
        gn21UpdateEndpoint endpoints coordinate x ∈ domain)
    (hderiv :
      HasDerivAt
        (fun x =>
          Rhat (gn21EndpointVectorPolicy
            (gn21UpdateEndpoint endpoints coordinate x)))
        derivativeValue value) :
    derivativeValue ≤ 0 := by
  by_contra hnot
  have hpositive : 0 < derivativeValue := lt_of_not_ge hnot
  rcases exists_pos_right_improvement_of_hasDerivAt_pos_lt
      hderiv hpositive (sub_pos.2 hupper) with
    ⟨ε, hε_pos, hε_lt, himprove⟩
  have hvalue_update :
      gn21UpdateEndpoint endpoints coordinate value = endpoints := by
    unfold gn21UpdateEndpoint
    rw [← hcoordinate]
    exact Function.update_eq_self coordinate endpoints
  have hcandidate :
      gn21UpdateEndpoint endpoints coordinate (value + ε) ∈ domain :=
    hfeasible (value + ε) (by constructor <;> linarith)
  have hbound := hmax
    (gn21UpdateEndpoint endpoints coordinate (value + ε)) hcandidate
  rw [hvalue_update] at himprove
  exact (not_lt_of_ge hbound) himprove

theorem endpoint_derivative_nonneg_of_endpoint_domain_maximum
    {n : Nat} (Rhat : SingleStateReward)
    {domain : Set (GN21EndpointVector n)}
    {endpoints : GN21EndpointVector n}
    (hmax :
      ∀ candidate ∈ domain,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (coordinate : Fin (2 * n))
    {lower value derivativeValue : ℝ}
    (hcoordinate : endpoints coordinate = ENNReal.ofReal value)
    (hlower : lower < value)
    (hfeasible :
      ∀ x ∈ Set.Ioo lower value,
        gn21UpdateEndpoint endpoints coordinate x ∈ domain)
    (hderiv :
      HasDerivAt
        (fun x =>
          Rhat (gn21EndpointVectorPolicy
            (gn21UpdateEndpoint endpoints coordinate x)))
        derivativeValue value) :
    0 ≤ derivativeValue := by
  by_contra hnot
  have hnegative : derivativeValue < 0 := lt_of_not_ge hnot
  rcases exists_pos_left_improvement_of_hasDerivAt_neg_lt
      hderiv hnegative (sub_pos.2 hlower) with
    ⟨ε, hε_pos, hε_lt, himprove⟩
  have hvalue_update :
      gn21UpdateEndpoint endpoints coordinate value = endpoints := by
    unfold gn21UpdateEndpoint
    rw [← hcoordinate]
    exact Function.update_eq_self coordinate endpoints
  have hcandidate :
      gn21UpdateEndpoint endpoints coordinate (value - ε) ∈ domain :=
    hfeasible (value - ε) (by constructor <;> linarith)
  have hbound := hmax
    (gn21UpdateEndpoint endpoints coordinate (value - ε)) hcandidate
  rw [hvalue_update] at himprove
  exact (not_lt_of_ge hbound) himprove

/-! ## Ordered endpoint neighborhoods -/

/-- A strict extended-real gap has a finite real right neighborhood at its lower end. -/
theorem exists_real_right_neighborhood_of_ennreal_lt
    {a b : ℝ≥0∞} (hab : a < b) :
    ∃ value upper : ℝ,
      a = ENNReal.ofReal value ∧ value < upper ∧
        ENNReal.ofReal upper ≤ b := by
  have ha_top : a ≠ ∞ := ne_top_of_lt hab
  let value : ℝ := a.toReal
  by_cases hb_top : b = ∞
  · refine ⟨value, value + 1, ?_, by linarith, ?_⟩
    · exact (ENNReal.ofReal_toReal ha_top).symm
    · rw [hb_top]
      exact le_top
  · have hab_real : a.toReal < b.toReal :=
      (ENNReal.toReal_lt_toReal ha_top hb_top).2 hab
    let upper : ℝ := (a.toReal + b.toReal) / 2
    refine ⟨value, upper, ?_, ?_, ?_⟩
    · exact (ENNReal.ofReal_toReal ha_top).symm
    · dsimp [value, upper]
      linarith
    · apply ENNReal.ofReal_le_of_le_toReal
      dsimp [upper]
      linarith

/-- A strict gap below a finite extended endpoint has a finite real left neighborhood. -/
theorem exists_real_left_neighborhood_of_ennreal_lt
    {a b : ℝ≥0∞} (hab : a < b) (hb_top : b ≠ ∞) :
    ∃ lower value : ℝ,
      a ≤ ENNReal.ofReal lower ∧ lower < value ∧
        b = ENNReal.ofReal value := by
  have ha_top : a ≠ ∞ := ne_top_of_lt hab
  have hab_real : a.toReal < b.toReal :=
    (ENNReal.toReal_lt_toReal ha_top hb_top).2 hab
  let lower : ℝ := (a.toReal + b.toReal) / 2
  let value : ℝ := b.toReal
  refine ⟨lower, value, ?_, ?_, ?_⟩
  · rw [← ENNReal.ofReal_toReal ha_top]
    exact ENNReal.ofReal_mono (by dsimp [lower]; linarith)
  · dsimp [lower, value]
    linarith
  · exact (ENNReal.ofReal_toReal hb_top).symm

/-- Every positive extended endpoint dominates some positive finite real endpoint. -/
theorem exists_pos_real_of_zero_lt_ennreal
    {b : ℝ≥0∞} (hb : 0 < b) :
    ∃ upper : ℝ, 0 < upper ∧ ENNReal.ofReal upper ≤ b := by
  by_cases hb_top : b = ∞
  · refine ⟨1, by norm_num, ?_⟩
    rw [hb_top]
    exact le_top
  · have hb_real : 0 < b.toReal :=
      ENNReal.toReal_pos (ne_of_gt hb) hb_top
    refine ⟨b.toReal / 2, by linarith, ?_⟩
    exact ENNReal.ofReal_le_of_le_toReal (by linarith)

/-! ## Shape-specific compact endpoint domains -/

/-- `extra + 1` interval slots leave room for the boundary tails used in Step 1. -/
abbrev GN21Lemma5EndpointVector (extra : Nat) :=
  GN21EndpointVector (extra + 1)

/-- First coordinate in a nonempty Lemma 5 endpoint vector. -/
def gn21Lemma5FirstEndpointIndex (extra : Nat) : Fin (2 * (extra + 1)) :=
  ⟨0, by omega⟩

/-- Last coordinate in a nonempty Lemma 5 endpoint vector. -/
def gn21Lemma5LastEndpointIndex (extra : Nat) : Fin (2 * (extra + 1)) :=
  ⟨2 * (extra + 1) - 1, by omega⟩

theorem gn21Lemma5FirstEndpointIndex_eq_lower_zero (extra : Nat) :
    gn21Lemma5FirstEndpointIndex extra =
      gn21LowerEndpointIndex (0 : Fin (extra + 1)) := by
  rfl

theorem gn21Lemma5LastEndpointIndex_eq_upper_last (extra : Nat) :
    gn21Lemma5LastEndpointIndex extra =
      gn21UpperEndpointIndex (Fin.last extra) := by
  apply Fin.ext
  simp [gn21Lemma5LastEndpointIndex, gn21UpperEndpointIndex]
  omega

theorem gn21MergeGap_first {n : Nat}
    (endpoints : GN21EndpointVector (n + 2)) (gap : Fin (n + 1)) :
    gn21MergeGap endpoints gap (gn21Lemma5FirstEndpointIndex n) =
      endpoints (gn21Lemma5FirstEndpointIndex (n + 1)) := by
  rw [gn21MergeGap, gn21Lemma5FirstEndpointIndex_eq_lower_zero,
    gn21EraseInterval_lower,
    Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero gap),
    gn21GapMergePreparation_lower_of_ne_right]
  · rw [← gn21Lemma5FirstEndpointIndex_eq_lower_zero]
  · exact (Fin.succ_ne_zero gap).symm

theorem gn21MergeGap_last {n : Nat}
    (endpoints : GN21EndpointVector (n + 2)) (gap : Fin (n + 1)) :
    gn21MergeGap endpoints gap (gn21Lemma5LastEndpointIndex n) =
      endpoints (gn21Lemma5LastEndpointIndex (n + 1)) := by
  rw [gn21MergeGap, gn21Lemma5LastEndpointIndex_eq_upper_last,
    gn21EraseInterval_upper]
  by_cases hright_last : Fin.succ gap = Fin.last (n + 1)
  · have hgap_last : gap = Fin.last n := by
      apply Fin.succ_injective
      simpa using hright_last
    have hsucc_last : (Fin.last n).succ = Fin.last (n + 1) := by
      apply Fin.ext
      simp
    rw [hright_last, Fin.succAbove_last_apply, hgap_last,
      gn21GapMergePreparation_left_upper, hsucc_last]
    rw [← gn21Lemma5LastEndpointIndex_eq_upper_last]
  · rw [Fin.succAbove_ne_last_last hright_last,
      gn21GapMergePreparation_upper_of_ne_left]
    · rw [← gn21Lemma5LastEndpointIndex_eq_upper_last]
    · intro hleft_last
      have hval := congrArg Fin.val hleft_last
      have hgap_lt := gap.isLt
      simp at hval
      omega

/-- Upper coordinate immediately before gap `i`. -/
def gn21Lemma5GapUpperIndex {extra : Nat}
    (i : Fin extra) : Fin (2 * (extra + 1)) :=
  ⟨2 * i.1 + 1, by omega⟩

/-- Lower coordinate immediately after gap `i`. -/
def gn21Lemma5GapLowerIndex {extra : Nat}
    (i : Fin extra) : Fin (2 * (extra + 1)) :=
  ⟨2 * i.1 + 2, by omega⟩

theorem gn21Lemma5GapLowerIndex_eq_lower_succ
    {extra : Nat} (i : Fin extra) :
    gn21Lemma5GapLowerIndex i = gn21LowerEndpointIndex i.succ := by
  apply Fin.ext
  simp [gn21Lemma5GapLowerIndex, gn21LowerEndpointIndex]
  omega

theorem gn21Lemma5GapUpperIndex_lt_lowerIndex
    {extra : Nat} (i : Fin extra) :
    gn21Lemma5GapUpperIndex i < gn21Lemma5GapLowerIndex i := by
  apply Fin.mk_lt_mk.2
  omega

theorem gn21Lemma5GapLowerIndex_le_of_upperIndex_lt
    {extra : Nat} (i : Fin extra)
    {j : Fin (2 * (extra + 1))}
    (hj : gn21Lemma5GapUpperIndex i < j) :
    gn21Lemma5GapLowerIndex i ≤ j := by
  apply Fin.mk_le_mk.2
  change 2 * i.1 + 1 < j.1 at hj
  omega

theorem gn21Lemma5GapUpperIndex_ne_first
    {extra : Nat} (i : Fin extra) :
    gn21Lemma5GapUpperIndex i ≠ gn21Lemma5FirstEndpointIndex extra := by
  intro h
  have := congrArg Fin.val h
  simp [gn21Lemma5GapUpperIndex, gn21Lemma5FirstEndpointIndex] at this

theorem gn21Lemma5GapUpperIndex_ne_last
    {extra : Nat} (i : Fin extra) :
    gn21Lemma5GapUpperIndex i ≠ gn21Lemma5LastEndpointIndex extra := by
  intro h
  have hi := i.isLt
  have := congrArg Fin.val h
  simp [gn21Lemma5GapUpperIndex, gn21Lemma5LastEndpointIndex] at this
  omega

theorem gn21Lemma5GapLowerIndex_ne_first
    {extra : Nat} (i : Fin extra) :
    gn21Lemma5GapLowerIndex i ≠ gn21Lemma5FirstEndpointIndex extra := by
  intro h
  have := congrArg Fin.val h
  simp [gn21Lemma5GapLowerIndex, gn21Lemma5FirstEndpointIndex] at this

theorem gn21EndpointVectorTail_first
    {extra : Nat}
    (endpoints : GN21Lemma5EndpointVector (extra + 1)) :
    gn21EndpointVectorTail endpoints (gn21Lemma5FirstEndpointIndex extra) =
      endpoints (gn21Lemma5GapLowerIndex (0 : Fin (extra + 1))) := by
  rfl

theorem gn21EndpointVectorTail_last
    {extra : Nat}
    (endpoints : GN21Lemma5EndpointVector (extra + 1)) :
    gn21EndpointVectorTail endpoints (gn21Lemma5LastEndpointIndex extra) =
      endpoints (gn21Lemma5LastEndpointIndex (extra + 1)) := by
  apply congrArg endpoints
  apply Fin.ext
  simp [gn21Lemma5LastEndpointIndex]
  omega

/--
Closing every gap in an ordered endpoint vector merges its finite interval
chain into the interval between the two outer endpoints, modulo the finitely
many shared endpoints.
-/
theorem policyAlmostEverywhereEq_endpointVectorPolicy_of_all_gaps_eq
    (mu : Measure TripLength) [NoAtoms mu]
    (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (extra + 1))
    (hgaps : ∀ i : Fin extra,
      endpoints (gn21Lemma5GapUpperIndex i) =
        endpoints (gn21Lemma5GapLowerIndex i)) :
    policyAlmostEverywhereEq mu (gn21EndpointVectorPolicy endpoints)
      (gn21ExtendedMiddlePolicy
        (endpoints (gn21Lemma5FirstEndpointIndex extra))
        (endpoints (gn21Lemma5LastEndpointIndex extra))) := by
  induction extra with
  | zero =>
      rw [gn21EndpointVectorPolicy_succ]
      simp [gn21EndpointVectorPolicy, gn21Lemma5FirstEndpointIndex,
        gn21Lemma5LastEndpointIndex, policyAlmostEverywhereEq]
  | succ extra ih =>
      let tail := gn21EndpointVectorTail endpoints
      have htail_ordered :
          tail ∈ gn21OrderedEndpointVectors (extra + 1) := by
        exact gn21EndpointVectorTail_ordered hordered
      have htail_gaps : ∀ i : Fin extra,
          tail (gn21Lemma5GapUpperIndex i) =
            tail (gn21Lemma5GapLowerIndex i) := by
        intro i
        simpa [tail, gn21EndpointVectorTail, gn21Lemma5GapUpperIndex,
          gn21Lemma5GapLowerIndex] using hgaps (Fin.succ i)
      have htail_ae := ih tail htail_ordered htail_gaps
      dsimp [tail] at htail_ae
      have hunion_ae := policyAlmostEverywhereEq_union_left mu
        (gn21ExtendedMiddlePolicy (endpoints 0) (endpoints 1)) htail_ae
      rw [gn21EndpointVectorPolicy_succ]
      refine policyAlmostEverywhereEq.trans' mu hunion_ae ?_
      rw [gn21EndpointVectorTail_first endpoints,
        gn21EndpointVectorTail_last endpoints]
      have hgap_zero := hgaps (0 : Fin (extra + 1))
      have hfirst_le_gap :
          endpoints (gn21Lemma5FirstEndpointIndex (extra + 1)) ≤
            endpoints (gn21Lemma5GapUpperIndex (0 : Fin (extra + 1))) :=
        hordered (by
          apply Fin.mk_le_mk.2
          change 0 ≤ 1
          omega)
      have hgap_le_last :
          endpoints (gn21Lemma5GapUpperIndex (0 : Fin (extra + 1))) ≤
            endpoints (gn21Lemma5LastEndpointIndex (extra + 1)) :=
        hordered (by
          apply Fin.mk_le_mk.2
          change 1 ≤ 2 * (extra + 1 + 1) - 1
          omega)
      rw [← hgap_zero]
      exact policyAlmostEverywhereEq_extendedMiddle_union_touching mu
        hfirst_le_gap hgap_le_last

/--
Shape-specific compact domains corresponding to the source's Step 1 seeds.
Positive and quasi-convex seeds retain both tails, increasing seeds retain a
right tail, decreasing seeds retain a left tail, and quasi-concave seeds have
no forced tail.
-/
def gn21Lemma5EndpointDomain
    (shape : Lemma5DerivativeShape) (extra : Nat) :
    Set (GN21Lemma5EndpointVector extra) :=
  match shape with
  | .positive =>
      gn21OrderedEndpointVectors (extra + 1) ∩
        {endpoints | endpoints (gn21Lemma5FirstEndpointIndex extra) = 0} ∩
        {endpoints | endpoints (gn21Lemma5LastEndpointIndex extra) = ∞}
  | .strictlyIncreasing =>
      gn21OrderedEndpointVectors (extra + 1) ∩
        {endpoints | endpoints (gn21Lemma5LastEndpointIndex extra) = ∞}
  | .strictlyDecreasing =>
      gn21OrderedEndpointVectors (extra + 1) ∩
        {endpoints | endpoints (gn21Lemma5FirstEndpointIndex extra) = 0}
  | .strictlyQuasiConvex =>
      gn21OrderedEndpointVectors (extra + 1) ∩
        {endpoints | endpoints (gn21Lemma5FirstEndpointIndex extra) = 0} ∩
        {endpoints | endpoints (gn21Lemma5LastEndpointIndex extra) = ∞}
  | .strictlyQuasiConcave =>
      gn21OrderedEndpointVectors (extra + 1)

theorem gn21Lemma5EndpointDomain_ordered
    {shape : Lemma5DerivativeShape} {extra : Nat}
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain shape extra) :
    endpoints ∈ gn21OrderedEndpointVectors (extra + 1) := by
  cases shape with
  | positive => exact hdomain.1.1
  | strictlyIncreasing => exact hdomain.1
  | strictlyDecreasing => exact hdomain.1
  | strictlyQuasiConvex => exact hdomain.1.1
  | strictlyQuasiConcave => exact hdomain

/-- Every nonempty feasible finite-tuple normalization belongs to each shape domain. -/
theorem gn21FiniteNNIntervalTupleEndpointVector_mem_lemma5EndpointDomain
    (shape : Lemma5DerivativeShape) {n : Nat} (hn : 0 < n)
    (lower upper : Fin n → NNReal) :
    gn21FiniteNNIntervalTupleEndpointVector lower upper ∈
      gn21Lemma5EndpointDomain shape (2 * n) := by
  have hordered :
      gn21FiniteNNIntervalTupleEndpointVector lower upper ∈
        gn21OrderedEndpointVectors (2 * n + 1) :=
    gn21FiniteNNIntervalTupleEndpointVector_ordered hn lower upper
  have hfirst :
      gn21FiniteNNIntervalTupleEndpointVector lower upper
          (gn21Lemma5FirstEndpointIndex (2 * n)) = 0 := by
    rw [gn21Lemma5FirstEndpointIndex_eq_lower_zero]
    simp [gn21FiniteNNIntervalTupleEndpointVector]
  have hlast :
      gn21FiniteNNIntervalTupleEndpointVector lower upper
          (gn21Lemma5LastEndpointIndex (2 * n)) = ∞ := by
    rw [gn21Lemma5LastEndpointIndex_eq_upper_last]
    simp [gn21FiniteNNIntervalTupleEndpointVector, hn]
  cases shape with
  | positive => exact ⟨⟨hordered, hfirst⟩, hlast⟩
  | strictlyIncreasing => exact ⟨hordered, hlast⟩
  | strictlyDecreasing => exact ⟨hordered, hfirst⟩
  | strictlyQuasiConvex => exact ⟨⟨hordered, hfirst⟩, hlast⟩
  | strictlyQuasiConcave => exact hordered

/-- Add a collapsed interval after the last slot of a Lemma 5 endpoint vector. -/
def gn21PadCollapsedLast (extra : Nat)
    (endpoints : GN21Lemma5EndpointVector extra) :
    GN21Lemma5EndpointVector (extra + 1) := fun coordinate =>
  if hcoordinate : coordinate.1 < 2 * (extra + 1) then
    endpoints ⟨coordinate.1, hcoordinate⟩
  else endpoints (gn21Lemma5LastEndpointIndex extra)

theorem gn21PadCollapsedLast_apply_cast (extra : Nat)
    (endpoints : GN21Lemma5EndpointVector extra)
    (coordinate : Fin (2 * (extra + 1))) :
    gn21PadCollapsedLast extra endpoints
        ⟨coordinate.1, by omega⟩ =
      endpoints coordinate := by
  simp [gn21PadCollapsedLast, coordinate.isLt]

theorem gn21PadCollapsedLast_first (extra : Nat)
    (endpoints : GN21Lemma5EndpointVector extra) :
    gn21PadCollapsedLast extra endpoints
        (gn21Lemma5FirstEndpointIndex (extra + 1)) =
      endpoints (gn21Lemma5FirstEndpointIndex extra) := by
  simp [gn21PadCollapsedLast, gn21Lemma5FirstEndpointIndex]

theorem gn21PadCollapsedLast_last (extra : Nat)
    (endpoints : GN21Lemma5EndpointVector extra) :
    gn21PadCollapsedLast extra endpoints
        (gn21Lemma5LastEndpointIndex (extra + 1)) =
      endpoints (gn21Lemma5LastEndpointIndex extra) := by
  rw [gn21PadCollapsedLast]
  split
  · rename_i hlt
    simp [gn21Lemma5LastEndpointIndex] at hlt
    omega
  · rfl

theorem gn21PadCollapsedLast_ordered (extra : Nat)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (extra + 1)) :
    gn21PadCollapsedLast extra endpoints ∈
      gn21OrderedEndpointVectors (extra + 2) := by
  intro i j hij
  have hij_val : i.1 ≤ j.1 := hij
  by_cases hj : j.1 < 2 * (extra + 1)
  · have hi : i.1 < 2 * (extra + 1) := lt_of_le_of_lt hij_val hj
    rw [gn21PadCollapsedLast, dif_pos hi,
      gn21PadCollapsedLast, dif_pos hj]
    apply hordered
    exact Fin.mk_le_mk.2 hij_val
  · by_cases hi : i.1 < 2 * (extra + 1)
    · rw [gn21PadCollapsedLast, dif_pos hi,
        gn21PadCollapsedLast, dif_neg hj]
      apply hordered
      apply Fin.mk_le_mk.2
      change i.1 ≤ 2 * (extra + 1) - 1
      omega
    · simp [gn21PadCollapsedLast, hi, hj]

@[simp] theorem gn21PadCollapsedLast_lower_castSucc (extra : Nat)
    (endpoints : GN21Lemma5EndpointVector extra)
    (slot : Fin (extra + 1)) :
    gn21PadCollapsedLast extra endpoints
        (gn21LowerEndpointIndex (Fin.castSucc slot)) =
      endpoints (gn21LowerEndpointIndex slot) := by
  rw [gn21PadCollapsedLast, dif_pos (by
    simp [gn21LowerEndpointIndex]
    omega)]
  apply congrArg endpoints
  apply Fin.ext
  rfl

@[simp] theorem gn21PadCollapsedLast_upper_castSucc (extra : Nat)
    (endpoints : GN21Lemma5EndpointVector extra)
    (slot : Fin (extra + 1)) :
    gn21PadCollapsedLast extra endpoints
        (gn21UpperEndpointIndex (Fin.castSucc slot)) =
      endpoints (gn21UpperEndpointIndex slot) := by
  rw [gn21PadCollapsedLast, dif_pos (by
    simp [gn21UpperEndpointIndex]
    omega)]
  apply congrArg endpoints
  apply Fin.ext
  rfl

theorem gn21PadCollapsedLast_new_interval_collapsed (extra : Nat)
    (endpoints : GN21Lemma5EndpointVector extra) :
    gn21PadCollapsedLast extra endpoints
        (gn21LowerEndpointIndex (Fin.last (extra + 1))) =
      gn21PadCollapsedLast extra endpoints
        (gn21UpperEndpointIndex (Fin.last (extra + 1))) := by
  simp [gn21PadCollapsedLast, gn21LowerEndpointIndex,
    gn21UpperEndpointIndex]

theorem gn21EndpointVectorPolicy_padCollapsedLast (extra : Nat)
    (endpoints : GN21Lemma5EndpointVector extra) :
    gn21EndpointVectorPolicy (gn21PadCollapsedLast extra endpoints) =
      gn21EndpointVectorPolicy endpoints := by
  ext τ
  constructor
  · intro hτ
    rcases Set.mem_iUnion.1 hτ with ⟨slot, hslot⟩
    by_cases hslot_old : slot.1 < extra + 1
    · let oldSlot : Fin (extra + 1) := ⟨slot.1, hslot_old⟩
      have hslot_eq : slot = Fin.castSucc oldSlot := by
        apply Fin.ext
        rfl
      rw [hslot_eq] at hslot
      apply Set.mem_iUnion.2
      refine ⟨oldSlot, ?_⟩
      simpa only [gn21PadCollapsedLast_lower_castSucc,
        gn21PadCollapsedLast_upper_castSucc] using hslot
    · have hslot_last : slot = Fin.last (extra + 1) := by
        apply Fin.ext
        simp
        omega
      subst slot
      rw [gn21PadCollapsedLast_new_interval_collapsed,
        gn21ExtendedMiddlePolicy_self] at hslot
      exact False.elim hslot
  · intro hτ
    rcases Set.mem_iUnion.1 hτ with ⟨slot, hslot⟩
    apply Set.mem_iUnion.2
    refine ⟨Fin.castSucc slot, ?_⟩
    simpa only [gn21PadCollapsedLast_lower_castSucc,
      gn21PadCollapsedLast_upper_castSucc] using hslot

theorem gn21PadCollapsedLast_mem_lemma5EndpointDomain
    (shape : Lemma5DerivativeShape) (extra : Nat)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain shape extra) :
    gn21PadCollapsedLast extra endpoints ∈
      gn21Lemma5EndpointDomain shape (extra + 1) := by
  have hpadded_ordered :=
    gn21PadCollapsedLast_ordered extra
      (gn21Lemma5EndpointDomain_ordered hdomain)
  cases shape with
  | positive =>
      rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
      change endpoints (gn21Lemma5FirstEndpointIndex extra) = 0 at hfirst
      change endpoints (gn21Lemma5LastEndpointIndex extra) = ∞ at hlast
      refine ⟨⟨hpadded_ordered, ?_⟩, ?_⟩
      · change gn21PadCollapsedLast extra endpoints
            (gn21Lemma5FirstEndpointIndex (extra + 1)) = 0
        rw [gn21PadCollapsedLast_first]
        exact hfirst
      · change gn21PadCollapsedLast extra endpoints
            (gn21Lemma5LastEndpointIndex (extra + 1)) = ∞
        rw [gn21PadCollapsedLast_last]
        exact hlast
  | strictlyIncreasing =>
      rcases hdomain with ⟨hordered, hlast⟩
      change endpoints (gn21Lemma5LastEndpointIndex extra) = ∞ at hlast
      refine ⟨hpadded_ordered, ?_⟩
      change gn21PadCollapsedLast extra endpoints
          (gn21Lemma5LastEndpointIndex (extra + 1)) = ∞
      rw [gn21PadCollapsedLast_last]
      exact hlast
  | strictlyDecreasing =>
      rcases hdomain with ⟨hordered, hfirst⟩
      change endpoints (gn21Lemma5FirstEndpointIndex extra) = 0 at hfirst
      refine ⟨hpadded_ordered, ?_⟩
      change gn21PadCollapsedLast extra endpoints
          (gn21Lemma5FirstEndpointIndex (extra + 1)) = 0
      rw [gn21PadCollapsedLast_first]
      exact hfirst
  | strictlyQuasiConvex =>
      rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
      change endpoints (gn21Lemma5FirstEndpointIndex extra) = 0 at hfirst
      change endpoints (gn21Lemma5LastEndpointIndex extra) = ∞ at hlast
      refine ⟨⟨hpadded_ordered, ?_⟩, ?_⟩
      · change gn21PadCollapsedLast extra endpoints
            (gn21Lemma5FirstEndpointIndex (extra + 1)) = 0
        rw [gn21PadCollapsedLast_first]
        exact hfirst
      · change gn21PadCollapsedLast extra endpoints
            (gn21Lemma5LastEndpointIndex (extra + 1)) = ∞
        rw [gn21PadCollapsedLast_last]
        exact hlast
  | strictlyQuasiConcave =>
      exact hpadded_ordered

/--
Updating a non-forced coordinate between all preceding and following
coordinates preserves the shape-specific endpoint domain.
-/
theorem gn21UpdateEndpoint_mem_lemma5EndpointDomain
    (shape : Lemma5DerivativeShape) (extra : Nat)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain shape extra)
    (coordinate : Fin (2 * (extra + 1))) (value : ℝ)
    (hbefore :
      ∀ j : Fin (2 * (extra + 1)), j < coordinate →
        endpoints j ≤ ENNReal.ofReal value)
    (hafter :
      ∀ j : Fin (2 * (extra + 1)), coordinate < j →
        ENNReal.ofReal value ≤ endpoints j)
    (hfirst_free :
      (shape = .positive ∨ shape = .strictlyDecreasing ∨
          shape = .strictlyQuasiConvex) →
        coordinate ≠ gn21Lemma5FirstEndpointIndex extra)
    (hlast_free :
      (shape = .positive ∨ shape = .strictlyIncreasing ∨
          shape = .strictlyQuasiConvex) →
        coordinate ≠ gn21Lemma5LastEndpointIndex extra) :
    gn21UpdateEndpoint endpoints coordinate value ∈
      gn21Lemma5EndpointDomain shape extra := by
  cases shape with
  | positive =>
      rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
      have hfirst_ne := hfirst_free (Or.inl rfl)
      have hlast_ne := hlast_free (Or.inl rfl)
      refine ⟨⟨gn21UpdateEndpoint_mem_ordered hordered coordinate value
        hbefore hafter, ?_⟩, ?_⟩
      · simpa [gn21UpdateEndpoint, Ne.symm hfirst_ne] using hfirst
      · simpa [gn21UpdateEndpoint, Ne.symm hlast_ne] using hlast
  | strictlyIncreasing =>
      rcases hdomain with ⟨hordered, hlast⟩
      have hlast_ne := hlast_free (Or.inr (Or.inl rfl))
      refine ⟨gn21UpdateEndpoint_mem_ordered hordered coordinate value
        hbefore hafter, ?_⟩
      simpa [gn21UpdateEndpoint, Ne.symm hlast_ne] using hlast
  | strictlyDecreasing =>
      rcases hdomain with ⟨hordered, hfirst⟩
      have hfirst_ne := hfirst_free (Or.inr (Or.inl rfl))
      refine ⟨gn21UpdateEndpoint_mem_ordered hordered coordinate value
        hbefore hafter, ?_⟩
      simpa [gn21UpdateEndpoint, Ne.symm hfirst_ne] using hfirst
  | strictlyQuasiConvex =>
      rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
      have hfirst_ne := hfirst_free (Or.inr (Or.inr rfl))
      have hlast_ne := hlast_free (Or.inr (Or.inr rfl))
      refine ⟨⟨gn21UpdateEndpoint_mem_ordered hordered coordinate value
        hbefore hafter, ?_⟩, ?_⟩
      · simpa [gn21UpdateEndpoint, Ne.symm hfirst_ne] using hfirst
      · simpa [gn21UpdateEndpoint, Ne.symm hlast_ne] using hlast
  | strictlyQuasiConcave =>
      exact gn21UpdateEndpoint_mem_ordered hdomain coordinate value
        hbefore hafter

/--
Erasing a non-forced interval slot preserves the shape-specific compact
endpoint domain.  Forced boundary tails are intentionally excluded here.
-/
theorem gn21EraseInterval_mem_lemma5EndpointDomain
    (shape : Lemma5DerivativeShape) (extra : Nat)
    {endpoints : GN21Lemma5EndpointVector (extra + 1)}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain shape (extra + 1))
    (removed : Fin (extra + 2))
    (hfirst_free :
      (shape = .positive ∨ shape = .strictlyDecreasing ∨
          shape = .strictlyQuasiConvex) →
        removed ≠ 0)
    (hlast_free :
      (shape = .positive ∨ shape = .strictlyIncreasing ∨
          shape = .strictlyQuasiConvex) →
        removed ≠ Fin.last (extra + 1)) :
    gn21EraseInterval endpoints removed ∈
      gn21Lemma5EndpointDomain shape extra := by
  have herased_ordered :=
    gn21EraseInterval_ordered
      (gn21Lemma5EndpointDomain_ordered hdomain) removed
  have herased_first :
      ∀ hremoved : removed ≠ 0,
        gn21EraseInterval endpoints removed
            (gn21Lemma5FirstEndpointIndex extra) =
          endpoints (gn21Lemma5FirstEndpointIndex (extra + 1)) := by
    intro hremoved
    rw [gn21Lemma5FirstEndpointIndex_eq_lower_zero,
      gn21EraseInterval_lower,
      Fin.succAbove_ne_zero_zero hremoved,
      ← gn21Lemma5FirstEndpointIndex_eq_lower_zero]
  have herased_last :
      ∀ hremoved : removed ≠ Fin.last (extra + 1),
        gn21EraseInterval endpoints removed
            (gn21Lemma5LastEndpointIndex extra) =
          endpoints (gn21Lemma5LastEndpointIndex (extra + 1)) := by
    intro hremoved
    rw [gn21Lemma5LastEndpointIndex_eq_upper_last,
      gn21EraseInterval_upper,
      Fin.succAbove_ne_last_last hremoved,
      ← gn21Lemma5LastEndpointIndex_eq_upper_last]
  cases shape with
  | positive =>
      rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
      change endpoints (gn21Lemma5FirstEndpointIndex (extra + 1)) = 0 at hfirst
      change endpoints (gn21Lemma5LastEndpointIndex (extra + 1)) = ∞ at hlast
      refine ⟨⟨herased_ordered, ?_⟩, ?_⟩
      · change gn21EraseInterval endpoints removed
            (gn21Lemma5FirstEndpointIndex extra) = 0
        rw [herased_first (hfirst_free (Or.inl rfl))]
        exact hfirst
      · change gn21EraseInterval endpoints removed
            (gn21Lemma5LastEndpointIndex extra) = ∞
        rw [herased_last (hlast_free (Or.inl rfl))]
        exact hlast
  | strictlyIncreasing =>
      rcases hdomain with ⟨hordered, hlast⟩
      change endpoints (gn21Lemma5LastEndpointIndex (extra + 1)) = ∞ at hlast
      refine ⟨herased_ordered, ?_⟩
      change gn21EraseInterval endpoints removed
          (gn21Lemma5LastEndpointIndex extra) = ∞
      rw [herased_last (hlast_free (Or.inr (Or.inl rfl)))]
      exact hlast
  | strictlyDecreasing =>
      rcases hdomain with ⟨hordered, hfirst⟩
      change endpoints (gn21Lemma5FirstEndpointIndex (extra + 1)) = 0 at hfirst
      refine ⟨herased_ordered, ?_⟩
      change gn21EraseInterval endpoints removed
          (gn21Lemma5FirstEndpointIndex extra) = 0
      rw [herased_first (hfirst_free (Or.inr (Or.inl rfl)))]
      exact hfirst
  | strictlyQuasiConvex =>
      rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
      change endpoints (gn21Lemma5FirstEndpointIndex (extra + 1)) = 0 at hfirst
      change endpoints (gn21Lemma5LastEndpointIndex (extra + 1)) = ∞ at hlast
      refine ⟨⟨herased_ordered, ?_⟩, ?_⟩
      · change gn21EraseInterval endpoints removed
            (gn21Lemma5FirstEndpointIndex extra) = 0
        rw [herased_first (hfirst_free (Or.inr (Or.inr rfl)))]
        exact hfirst
      · change gn21EraseInterval endpoints removed
            (gn21Lemma5LastEndpointIndex extra) = ∞
        rw [herased_last (hlast_free (Or.inr (Or.inr rfl)))]
        exact hlast
  | strictlyQuasiConcave =>
      exact herased_ordered

/-- Closing a touching gap preserves every shape-specific compact endpoint domain. -/
theorem gn21MergeGap_mem_lemma5EndpointDomain
    (shape : Lemma5DerivativeShape) (extra : Nat)
    {endpoints : GN21Lemma5EndpointVector (extra + 1)}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain shape (extra + 1))
    (gap : Fin (extra + 1)) :
    gn21MergeGap endpoints gap ∈ gn21Lemma5EndpointDomain shape extra := by
  have hmerged_ordered :=
    gn21MergeGap_ordered (gn21Lemma5EndpointDomain_ordered hdomain) gap
  have hmerged_first :
      gn21MergeGap endpoints gap (gn21Lemma5FirstEndpointIndex extra) =
        endpoints (gn21Lemma5FirstEndpointIndex (extra + 1)) :=
    gn21MergeGap_first endpoints gap
  have hmerged_last :
      gn21MergeGap endpoints gap (gn21Lemma5LastEndpointIndex extra) =
        endpoints (gn21Lemma5LastEndpointIndex (extra + 1)) :=
    gn21MergeGap_last endpoints gap
  cases shape with
  | positive =>
      rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
      change endpoints (gn21Lemma5FirstEndpointIndex (extra + 1)) = 0 at hfirst
      change endpoints (gn21Lemma5LastEndpointIndex (extra + 1)) = ∞ at hlast
      refine ⟨⟨hmerged_ordered, ?_⟩, ?_⟩
      · change gn21MergeGap endpoints gap
            (gn21Lemma5FirstEndpointIndex extra) = 0
        rw [hmerged_first]
        exact hfirst
      · change gn21MergeGap endpoints gap
            (gn21Lemma5LastEndpointIndex extra) = ∞
        rw [hmerged_last]
        exact hlast
  | strictlyIncreasing =>
      rcases hdomain with ⟨hordered, hlast⟩
      change endpoints (gn21Lemma5LastEndpointIndex (extra + 1)) = ∞ at hlast
      refine ⟨hmerged_ordered, ?_⟩
      change gn21MergeGap endpoints gap
          (gn21Lemma5LastEndpointIndex extra) = ∞
      rw [hmerged_last]
      exact hlast
  | strictlyDecreasing =>
      rcases hdomain with ⟨hordered, hfirst⟩
      change endpoints (gn21Lemma5FirstEndpointIndex (extra + 1)) = 0 at hfirst
      refine ⟨hmerged_ordered, ?_⟩
      change gn21MergeGap endpoints gap
          (gn21Lemma5FirstEndpointIndex extra) = 0
      rw [hmerged_first]
      exact hfirst
  | strictlyQuasiConvex =>
      rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
      change endpoints (gn21Lemma5FirstEndpointIndex (extra + 1)) = 0 at hfirst
      change endpoints (gn21Lemma5LastEndpointIndex (extra + 1)) = ∞ at hlast
      refine ⟨⟨hmerged_ordered, ?_⟩, ?_⟩
      · change gn21MergeGap endpoints gap
            (gn21Lemma5FirstEndpointIndex extra) = 0
        rw [hmerged_first]
        exact hfirst
      · change gn21MergeGap endpoints gap
            (gn21Lemma5LastEndpointIndex extra) = ∞
        rw [hmerged_last]
        exact hlast
  | strictlyQuasiConcave =>
      exact hmerged_ordered

/--
If a larger endpoint-domain maximizer is represented by a compressed policy,
padding smaller candidates transports maximality to the compressed domain.
-/
theorem gn21Lemma5EndpointDomain_maximum_of_compression
    (shape : Lemma5DerivativeShape) (extra : Nat)
    (Rhat : SingleStateReward)
    {source : GN21Lemma5EndpointVector (extra + 1)}
    {compressed : GN21Lemma5EndpointVector extra}
    (hsource_max :
      ∀ candidate ∈ gn21Lemma5EndpointDomain shape (extra + 1),
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy source))
    (hreward :
      Rhat (gn21EndpointVectorPolicy source) =
        Rhat (gn21EndpointVectorPolicy compressed)) :
    ∀ candidate ∈ gn21Lemma5EndpointDomain shape extra,
      Rhat (gn21EndpointVectorPolicy candidate) ≤
        Rhat (gn21EndpointVectorPolicy compressed) := by
  intro candidate hcandidate
  calc
    Rhat (gn21EndpointVectorPolicy candidate) =
        Rhat (gn21EndpointVectorPolicy
          (gn21PadCollapsedLast extra candidate)) := by
      rw [gn21EndpointVectorPolicy_padCollapsedLast]
    _ ≤ Rhat (gn21EndpointVectorPolicy source) :=
      hsource_max (gn21PadCollapsedLast extra candidate)
        (gn21PadCollapsedLast_mem_lemma5EndpointDomain
          shape extra hcandidate)
    _ = Rhat (gn21EndpointVectorPolicy compressed) := hreward

/--
Failure of strict endpoint separation is witnessed either by a collapsed
interval or by a touching adjacent gap.
-/
theorem exists_collapsed_interval_or_touching_gap_of_not_strict
    (extra : Nat) {endpoints : GN21Lemma5EndpointVector extra}
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (extra + 1))
    (hnot_strict : ¬ gn21StrictEndpointVector endpoints) :
    (∃ slot : Fin (extra + 1),
      endpoints (gn21LowerEndpointIndex slot) =
        endpoints (gn21UpperEndpointIndex slot)) ∨
    (∃ gap : Fin extra,
      endpoints (gn21Lemma5GapUpperIndex gap) =
        endpoints (gn21Lemma5GapLowerIndex gap)) := by
  rw [gn21StrictEndpointVector] at hnot_strict
  push Not at hnot_strict
  rcases hnot_strict with ⟨left, right, hleft_right, hright_left⟩
  let next : Fin (2 * (extra + 1)) :=
    ⟨left.1 + 1, by
      have hright_lt := right.isLt
      have hleft_right_val : left.1 < right.1 := hleft_right
      omega⟩
  have hleft_next : left < next := by
    apply Fin.mk_lt_mk.2
    exact Nat.lt_succ_self _
  have hnext_right : next ≤ right := by
    apply Fin.mk_le_mk.2
    change left.1 + 1 ≤ right.1
    exact hleft_right
  have hleft_next_eq : endpoints left = endpoints next := by
    apply le_antisymm
    · exact hordered (le_of_lt hleft_next)
    · exact (hordered hnext_right).trans hright_left
  rcases left.1.even_or_odd' with ⟨index, heven | hodd⟩
  · left
    have hindex_lt : index < extra + 1 := by
      have hnext_lt := next.isLt
      simp [next] at hnext_lt
      omega
    let slot : Fin (extra + 1) := ⟨index, hindex_lt⟩
    refine ⟨slot, ?_⟩
    have hlower : gn21LowerEndpointIndex slot = left := by
      apply Fin.ext
      simp [gn21LowerEndpointIndex, slot]
      omega
    have hupper : gn21UpperEndpointIndex slot = next := by
      apply Fin.ext
      simp [gn21UpperEndpointIndex, slot, next]
      omega
    rw [hlower, hupper]
    exact hleft_next_eq
  · right
    have hindex_lt : index < extra := by
      have hnext_lt := next.isLt
      simp [next] at hnext_lt
      omega
    let gap : Fin extra := ⟨index, hindex_lt⟩
    refine ⟨gap, ?_⟩
    have hupper : gn21Lemma5GapUpperIndex gap = left := by
      apply Fin.ext
      simp [gn21Lemma5GapUpperIndex, gap]
      omega
    have hlower : gn21Lemma5GapLowerIndex gap = next := by
      apply Fin.ext
      simp [gn21Lemma5GapLowerIndex, gap, next]
      omega
    rw [hupper, hlower]
    exact hleft_next_eq

/--
An interval slot is irreducible when it is the sole remaining slot or when it
is one of the boundary tails forced by the source's finite seed construction.
-/
def gn21Lemma5IrreducibleIntervalSlot
    (shape : Lemma5DerivativeShape) (extra : Nat)
    (slot : Fin (extra + 1)) : Prop :=
  extra = 0 ∨
    ((shape = .positive ∨ shape = .strictlyDecreasing ∨
        shape = .strictlyQuasiConvex) ∧ slot = 0) ∨
    ((shape = .positive ∨ shape = .strictlyIncreasing ∨
        shape = .strictlyQuasiConvex) ∧ slot = Fin.last extra)

/-- No policy-preserving interval or gap compression remains. -/
def gn21Lemma5CompressionReduced
    (shape : Lemma5DerivativeShape) (extra : Nat)
    (endpoints : GN21Lemma5EndpointVector extra) : Prop :=
  (∀ slot : Fin (extra + 1),
      endpoints (gn21LowerEndpointIndex slot) =
          endpoints (gn21UpperEndpointIndex slot) →
        gn21Lemma5IrreducibleIntervalSlot shape extra slot) ∧
    ∀ gap : Fin extra,
      endpoints (gn21Lemma5GapUpperIndex gap) <
        endpoints (gn21Lemma5GapLowerIndex gap)

/--
Every finite endpoint-domain maximizer has an equal-reward compression-reduced
representative.  Reward invariance under null endpoint changes is a visible
premise because the source identifies policies up to measure-zero endpoints.
-/
theorem exists_gn21Lemma5CompressionReduced_maximum
    (mu : Measure TripLength) [NoAtoms mu]
    (shape : Lemma5DerivativeShape) (Rhat : SingleStateReward)
    (hRhat_ae : ∀ {sigma tau : TripPolicy},
      policyAlmostEverywhereEq mu sigma tau → Rhat sigma = Rhat tau)
    (extra : Nat) {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain shape extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain shape extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints)) :
    ∃ reducedExtra : Nat, reducedExtra ≤ extra ∧
      ∃ reduced : GN21Lemma5EndpointVector reducedExtra,
        reduced ∈ gn21Lemma5EndpointDomain shape reducedExtra ∧
          (∀ candidate ∈ gn21Lemma5EndpointDomain shape reducedExtra,
            Rhat (gn21EndpointVectorPolicy candidate) ≤
              Rhat (gn21EndpointVectorPolicy reduced)) ∧
          Rhat (gn21EndpointVectorPolicy reduced) =
            Rhat (gn21EndpointVectorPolicy endpoints) ∧
          gn21Lemma5CompressionReduced shape reducedExtra reduced := by
  induction extra with
  | zero =>
      refine ⟨0, le_rfl, endpoints, hdomain, hmax, rfl, ?_⟩
      constructor
      · intro slot hcollapsed
        exact Or.inl rfl
      · intro gap
        exact Fin.elim0 gap
  | succ extra ih =>
      have hordered := gn21Lemma5EndpointDomain_ordered hdomain
      by_cases hintervals :
          ∀ slot : Fin (extra + 2),
            endpoints (gn21LowerEndpointIndex slot) =
                endpoints (gn21UpperEndpointIndex slot) →
              gn21Lemma5IrreducibleIntervalSlot shape (extra + 1) slot
      · by_cases hgaps : ∀ gap : Fin (extra + 1),
            endpoints (gn21Lemma5GapUpperIndex gap) <
              endpoints (gn21Lemma5GapLowerIndex gap)
        · exact ⟨extra + 1, le_rfl, endpoints, hdomain, hmax, rfl,
            ⟨hintervals, hgaps⟩⟩
        · push Not at hgaps
          rcases hgaps with ⟨gap, hgap_not_lt⟩
          have hgap_le :
              endpoints (gn21Lemma5GapUpperIndex gap) ≤
                endpoints (gn21Lemma5GapLowerIndex gap) :=
            hordered (le_of_lt (gn21Lemma5GapUpperIndex_lt_lowerIndex gap))
          have htouching :
              endpoints (gn21Lemma5GapUpperIndex gap) =
                endpoints (gn21Lemma5GapLowerIndex gap) :=
            le_antisymm hgap_le hgap_not_lt
          let compressed := gn21MergeGap endpoints gap
          have hcompressed_domain :
              compressed ∈ gn21Lemma5EndpointDomain shape extra := by
            exact gn21MergeGap_mem_lemma5EndpointDomain
              shape extra hdomain gap
          have hae : policyAlmostEverywhereEq mu
              (gn21EndpointVectorPolicy endpoints)
              (gn21EndpointVectorPolicy compressed) := by
            exact policyAlmostEverywhereEq_mergeGap
              mu hordered gap htouching
          have hreward_source_compressed :
              Rhat (gn21EndpointVectorPolicy endpoints) =
                Rhat (gn21EndpointVectorPolicy compressed) :=
            hRhat_ae hae
          have hcompressed_max :
              ∀ candidate ∈ gn21Lemma5EndpointDomain shape extra,
                Rhat (gn21EndpointVectorPolicy candidate) ≤
                  Rhat (gn21EndpointVectorPolicy compressed) :=
            gn21Lemma5EndpointDomain_maximum_of_compression
              shape extra Rhat hmax hreward_source_compressed
          rcases ih hcompressed_domain hcompressed_max with
            ⟨reducedExtra, hreducedExtra, reduced, hreduced_domain,
              hreduced_max, hreduced_reward, hreduced⟩
          refine ⟨reducedExtra, hreducedExtra.trans (Nat.le_succ extra),
            reduced, hreduced_domain, hreduced_max, ?_, hreduced⟩
          exact hreduced_reward.trans hreward_source_compressed.symm
      · push Not at hintervals
        rcases hintervals with ⟨removed, hcollapsed, hremovable⟩
        have hfirst_free :
            (shape = .positive ∨ shape = .strictlyDecreasing ∨
                shape = .strictlyQuasiConvex) →
              removed ≠ 0 := by
          intro hshape hzero
          apply hremovable
          exact Or.inr (Or.inl ⟨hshape, hzero⟩)
        have hlast_free :
            (shape = .positive ∨ shape = .strictlyIncreasing ∨
                shape = .strictlyQuasiConvex) →
              removed ≠ Fin.last (extra + 1) := by
          intro hshape hlast
          apply hremovable
          exact Or.inr (Or.inr ⟨hshape, hlast⟩)
        let compressed := gn21EraseInterval endpoints removed
        have hcompressed_domain :
            compressed ∈ gn21Lemma5EndpointDomain shape extra := by
          exact gn21EraseInterval_mem_lemma5EndpointDomain
            shape extra hdomain removed hfirst_free hlast_free
        have hpolicy :
            gn21EndpointVectorPolicy compressed =
              gn21EndpointVectorPolicy endpoints := by
          exact gn21EndpointVectorPolicy_eraseInterval_of_collapsed
            endpoints removed hcollapsed
        have hreward_source_compressed :
            Rhat (gn21EndpointVectorPolicy endpoints) =
              Rhat (gn21EndpointVectorPolicy compressed) := by
          rw [hpolicy]
        have hcompressed_max :
            ∀ candidate ∈ gn21Lemma5EndpointDomain shape extra,
              Rhat (gn21EndpointVectorPolicy candidate) ≤
                Rhat (gn21EndpointVectorPolicy compressed) :=
          gn21Lemma5EndpointDomain_maximum_of_compression
            shape extra Rhat hmax hreward_source_compressed
        rcases ih hcompressed_domain hcompressed_max with
          ⟨reducedExtra, hreducedExtra, reduced, hreduced_domain,
            hreduced_max, hreduced_reward, hreduced⟩
        refine ⟨reducedExtra, hreducedExtra.trans (Nat.le_succ extra),
          reduced, hreduced_domain, hreduced_max, ?_, hreduced⟩
        exact hreduced_reward.trans hreward_source_compressed.symm

/-- Every removable interval in a reduced ordered vector is nondegenerate. -/
theorem gn21Lemma5CompressionReduced_interval_strict
    (shape : Lemma5DerivativeShape) (extra : Nat)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (extra + 1))
    (hreduced : gn21Lemma5CompressionReduced shape extra endpoints)
    (slot : Fin (extra + 1))
    (hremovable :
      ¬ gn21Lemma5IrreducibleIntervalSlot shape extra slot) :
    endpoints (gn21LowerEndpointIndex slot) <
      endpoints (gn21UpperEndpointIndex slot) := by
  apply lt_of_le_of_ne
  · apply hordered
    apply Fin.mk_le_mk.2
    simp
  · intro hcollapsed
    exact hremovable (hreduced.1 slot hcollapsed)

/-- A maximizing non-forced coordinate that can move right has nonpositive derivative. -/
theorem endpoint_derivative_nonpos_of_lemma5EndpointDomain_maximum
    (shape : Lemma5DerivativeShape) (extra : Nat)
    (Rhat : SingleStateReward)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain shape extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain shape extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (coordinate : Fin (2 * (extra + 1)))
    {value upper derivativeValue : ℝ}
    (hcoordinate : endpoints coordinate = ENNReal.ofReal value)
    (hupper : value < upper)
    (hupper_bounds :
      ∀ j : Fin (2 * (extra + 1)), coordinate < j →
        ENNReal.ofReal upper ≤ endpoints j)
    (hfirst_free :
      (shape = .positive ∨ shape = .strictlyDecreasing ∨
          shape = .strictlyQuasiConvex) →
        coordinate ≠ gn21Lemma5FirstEndpointIndex extra)
    (hlast_free :
      (shape = .positive ∨ shape = .strictlyIncreasing ∨
          shape = .strictlyQuasiConvex) →
        coordinate ≠ gn21Lemma5LastEndpointIndex extra)
    (hderiv :
      HasDerivAt
        (fun x =>
          Rhat (gn21EndpointVectorPolicy
            (gn21UpdateEndpoint endpoints coordinate x)))
        derivativeValue value) :
    derivativeValue ≤ 0 := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  apply endpoint_derivative_nonpos_of_endpoint_domain_maximum
      Rhat hmax coordinate hcoordinate hupper
  · intro x hx
    apply gn21UpdateEndpoint_mem_lemma5EndpointDomain
        shape extra hdomain coordinate x
    · intro j hj
      calc
        endpoints j ≤ endpoints coordinate := hordered (le_of_lt hj)
        _ = ENNReal.ofReal value := hcoordinate
        _ ≤ ENNReal.ofReal x := ENNReal.ofReal_mono (le_of_lt hx.1)
    · intro j hj
      exact (ENNReal.ofReal_mono (le_of_lt hx.2)).trans
        (hupper_bounds j hj)
    · exact hfirst_free
    · exact hlast_free
  · exact hderiv

/-- A maximizing non-forced coordinate that can move left has nonnegative derivative. -/
theorem endpoint_derivative_nonneg_of_lemma5EndpointDomain_maximum
    (shape : Lemma5DerivativeShape) (extra : Nat)
    (Rhat : SingleStateReward)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain shape extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain shape extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (coordinate : Fin (2 * (extra + 1)))
    {lower value derivativeValue : ℝ}
    (hcoordinate : endpoints coordinate = ENNReal.ofReal value)
    (hlower : lower < value)
    (hlower_bounds :
      ∀ j : Fin (2 * (extra + 1)), j < coordinate →
        endpoints j ≤ ENNReal.ofReal lower)
    (hfirst_free :
      (shape = .positive ∨ shape = .strictlyDecreasing ∨
          shape = .strictlyQuasiConvex) →
        coordinate ≠ gn21Lemma5FirstEndpointIndex extra)
    (hlast_free :
      (shape = .positive ∨ shape = .strictlyIncreasing ∨
          shape = .strictlyQuasiConvex) →
        coordinate ≠ gn21Lemma5LastEndpointIndex extra)
    (hderiv :
      HasDerivAt
        (fun x =>
          Rhat (gn21EndpointVectorPolicy
            (gn21UpdateEndpoint endpoints coordinate x)))
        derivativeValue value) :
    0 ≤ derivativeValue := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  apply endpoint_derivative_nonneg_of_endpoint_domain_maximum
      Rhat hmax coordinate hcoordinate hlower
  · intro x hx
    apply gn21UpdateEndpoint_mem_lemma5EndpointDomain
        shape extra hdomain coordinate x
    · intro j hj
      exact (hlower_bounds j hj).trans
        (ENNReal.ofReal_mono (le_of_lt hx.1))
    · intro j hj
      calc
        ENNReal.ofReal x ≤ ENNReal.ofReal value :=
          ENNReal.ofReal_mono (le_of_lt hx.2)
        _ = endpoints coordinate := hcoordinate.symm
        _ ≤ endpoints j := hordered (le_of_lt hj)
    · exact hfirst_free
    · exact hlast_free
  · exact hderiv

/--
A right-movable endpoint at a maximum has nonpositive response whenever its
actual derivative has the same strict sign as that response.
-/
theorem endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
    (shape : Lemma5DerivativeShape) (extra : Nat)
    (Rhat : SingleStateReward)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain shape extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain shape extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (coordinate : Fin (2 * (extra + 1)))
    {value upper responseValue : ℝ}
    (hcoordinate : endpoints coordinate = ENNReal.ofReal value)
    (hupper : value < upper)
    (hupper_bounds :
      ∀ j : Fin (2 * (extra + 1)), coordinate < j →
        ENNReal.ofReal upper ≤ endpoints j)
    (hfirst_free :
      (shape = .positive ∨ shape = .strictlyDecreasing ∨
          shape = .strictlyQuasiConvex) →
        coordinate ≠ gn21Lemma5FirstEndpointIndex extra)
    (hlast_free :
      (shape = .positive ∨ shape = .strictlyIncreasing ∨
          shape = .strictlyQuasiConvex) →
        coordinate ≠ gn21Lemma5LastEndpointIndex extra)
    (hderiv :
      ∃ derivativeValue : ℝ,
        HasDerivAt
            (fun x =>
              Rhat (gn21EndpointVectorPolicy
                (gn21UpdateEndpoint endpoints coordinate x)))
            derivativeValue value ∧
          sameStrictSign derivativeValue responseValue) :
    responseValue ≤ 0 := by
  rcases hderiv with ⟨derivativeValue, hderivative, hsame_sign⟩
  apply sameStrictSign_nonpos_right hsame_sign
  exact endpoint_derivative_nonpos_of_lemma5EndpointDomain_maximum
    shape extra Rhat hdomain hmax coordinate hcoordinate hupper
    hupper_bounds hfirst_free hlast_free hderivative

/--
A left-movable endpoint at a maximum has nonnegative response whenever its
actual derivative has the same strict sign as that response.
-/
theorem endpoint_response_nonneg_of_lemma5EndpointDomain_maximum
    (shape : Lemma5DerivativeShape) (extra : Nat)
    (Rhat : SingleStateReward)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain shape extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain shape extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (coordinate : Fin (2 * (extra + 1)))
    {lower value responseValue : ℝ}
    (hcoordinate : endpoints coordinate = ENNReal.ofReal value)
    (hlower : lower < value)
    (hlower_bounds :
      ∀ j : Fin (2 * (extra + 1)), j < coordinate →
        endpoints j ≤ ENNReal.ofReal lower)
    (hfirst_free :
      (shape = .positive ∨ shape = .strictlyDecreasing ∨
          shape = .strictlyQuasiConvex) →
        coordinate ≠ gn21Lemma5FirstEndpointIndex extra)
    (hlast_free :
      (shape = .positive ∨ shape = .strictlyIncreasing ∨
          shape = .strictlyQuasiConvex) →
        coordinate ≠ gn21Lemma5LastEndpointIndex extra)
    (hderiv :
      ∃ derivativeValue : ℝ,
        HasDerivAt
            (fun x =>
              Rhat (gn21EndpointVectorPolicy
                (gn21UpdateEndpoint endpoints coordinate x)))
            derivativeValue value ∧
          sameStrictSign derivativeValue responseValue) :
    0 ≤ responseValue := by
  rcases hderiv with ⟨derivativeValue, hderivative, hsame_sign⟩
  apply sameStrictSign_nonneg_right hsame_sign
  exact endpoint_derivative_nonneg_of_lemma5EndpointDomain_maximum
    shape extra Rhat hdomain hmax coordinate hcoordinate hlower
    hlower_bounds hfirst_free hlast_free hderivative

theorem isClosed_gn21Lemma5EndpointDomain
    (shape : Lemma5DerivativeShape) (extra : Nat) :
    IsClosed (gn21Lemma5EndpointDomain shape extra) := by
  cases shape with
  | positive =>
      exact ((isClosed_gn21OrderedEndpointVectors (extra + 1)).inter
        (isClosed_eq (continuous_apply _) continuous_const)).inter
          (isClosed_eq (continuous_apply _) continuous_const)
  | strictlyIncreasing =>
      exact (isClosed_gn21OrderedEndpointVectors (extra + 1)).inter
        (isClosed_eq (continuous_apply _) continuous_const)
  | strictlyDecreasing =>
      exact (isClosed_gn21OrderedEndpointVectors (extra + 1)).inter
        (isClosed_eq (continuous_apply _) continuous_const)
  | strictlyQuasiConvex =>
      exact ((isClosed_gn21OrderedEndpointVectors (extra + 1)).inter
        (isClosed_eq (continuous_apply _) continuous_const)).inter
          (isClosed_eq (continuous_apply _) continuous_const)
  | strictlyQuasiConcave =>
      exact isClosed_gn21OrderedEndpointVectors (extra + 1)

theorem isCompact_gn21Lemma5EndpointDomain
    (shape : Lemma5DerivativeShape) (extra : Nat) :
    IsCompact (gn21Lemma5EndpointDomain shape extra) :=
  (isClosed_gn21Lemma5EndpointDomain shape extra).isCompact

/-- A monotone zero-then-infinity vector supplies both boundary tails. -/
def gn21ZeroThenTopEndpointVector (extra : Nat) :
    GN21Lemma5EndpointVector extra :=
  fun i => if i = gn21Lemma5FirstEndpointIndex extra then 0 else ∞

theorem gn21ZeroThenTopEndpointVector_ordered (extra : Nat) :
    gn21ZeroThenTopEndpointVector extra ∈
      gn21OrderedEndpointVectors (extra + 1) := by
  intro i j hij
  by_cases hi : i = gn21Lemma5FirstEndpointIndex extra
  · simp [gn21ZeroThenTopEndpointVector, hi]
  · have hj : j ≠ gn21Lemma5FirstEndpointIndex extra := by
      intro hj
      subst j
      have hi_zero : i = gn21Lemma5FirstEndpointIndex extra := by
        apply Fin.ext
        change i.1 = 0
        have hle : i.1 ≤ 0 := by
          simpa [gn21Lemma5FirstEndpointIndex] using hij
        exact Nat.eq_zero_of_le_zero hle
      exact hi hi_zero
    simp [gn21ZeroThenTopEndpointVector, hi, hj]

theorem gn21ZeroThenTopEndpointVector_first (extra : Nat) :
    gn21ZeroThenTopEndpointVector extra
      (gn21Lemma5FirstEndpointIndex extra) = 0 := by
  simp [gn21ZeroThenTopEndpointVector]

theorem gn21ZeroThenTopEndpointVector_last (extra : Nat) :
    gn21ZeroThenTopEndpointVector extra
      (gn21Lemma5LastEndpointIndex extra) = ∞ := by
  simp [gn21ZeroThenTopEndpointVector, gn21Lemma5FirstEndpointIndex,
    gn21Lemma5LastEndpointIndex]
  omega

theorem gn21Lemma5EndpointDomain_nonempty
    (shape : Lemma5DerivativeShape) (extra : Nat) :
    (gn21Lemma5EndpointDomain shape extra).Nonempty := by
  cases shape with
  | positive =>
      exact ⟨gn21ZeroThenTopEndpointVector extra,
        ⟨⟨gn21ZeroThenTopEndpointVector_ordered extra,
          gn21ZeroThenTopEndpointVector_first extra⟩,
          gn21ZeroThenTopEndpointVector_last extra⟩⟩
  | strictlyIncreasing =>
      refine ⟨fun _ => ∞, ?_⟩
      exact ⟨by intro i j hij; exact le_rfl, rfl⟩
  | strictlyDecreasing =>
      refine ⟨fun _ => 0, ?_⟩
      exact ⟨by intro i j hij; exact le_rfl, rfl⟩
  | strictlyQuasiConvex =>
      exact ⟨gn21ZeroThenTopEndpointVector extra,
        ⟨⟨gn21ZeroThenTopEndpointVector_ordered extra,
          gn21ZeroThenTopEndpointVector_first extra⟩,
          gn21ZeroThenTopEndpointVector_last extra⟩⟩
  | strictlyQuasiConcave =>
      refine ⟨fun _ => 0, ?_⟩
      intro i j hij
      exact le_rfl

/-- Continuous reward attains a maximum on each shape-specific endpoint domain. -/
theorem exists_gn21Lemma5EndpointDomain_reward_maximum
    (shape : Lemma5DerivativeShape) (extra : Nat)
    (Rhat : SingleStateReward)
    (hcontinuous :
      ContinuousOn
        (fun endpoints : GN21Lemma5EndpointVector extra =>
          Rhat (gn21EndpointVectorPolicy endpoints))
        (gn21Lemma5EndpointDomain shape extra)) :
    ∃ endpoints ∈ gn21Lemma5EndpointDomain shape extra,
      ∀ candidate ∈ gn21Lemma5EndpointDomain shape extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints) := by
  rcases (isCompact_gn21Lemma5EndpointDomain shape extra).exists_isMaxOn
      (gn21Lemma5EndpointDomain_nonempty shape extra) hcontinuous with
    ⟨endpoints, hdomain, hmax⟩
  rw [isMaxOn_iff] at hmax
  exact ⟨endpoints, hdomain, hmax⟩

/--
Finite normalization and compact attainment produce a shape-domain maximizer
whose reward is arbitrarily close to an arbitrary open source policy from
below.  All continuity inputs remain visible.
-/
theorem exists_gn21Lemma5EndpointDomain_maximum_above_source_sub
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (shape : Lemma5DerivativeShape) (Rhat : SingleStateReward)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain shape extra))
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_gap : epsilon < Rhat sigma - Rhat ∅) :
    ∃ extra : Nat, ∃ endpoints : GN21Lemma5EndpointVector extra,
      endpoints ∈ gn21Lemma5EndpointDomain shape extra ∧
        (∀ candidate ∈ gn21Lemma5EndpointDomain shape extra,
          Rhat (gn21EndpointVectorPolicy candidate) ≤
            Rhat (gn21EndpointVectorPolicy endpoints)) ∧
        Rhat sigma - epsilon <
          Rhat (gn21EndpointVectorPolicy endpoints) := by
  rcases exists_gn21FiniteIntervalPolicy_reward_close_nonempty
      mu Rhat hsigma_open (hcontinuous sigma) hepsilon_pos hepsilon_gap with
    ⟨P, hP_nonempty, hP_subset_sigma, hP_close⟩
  letI : Nonempty P.index := hP_nonempty
  have hP_subset : P.policy ⊆ acceptAllPolicy :=
    hP_subset_sigma.trans hsigma_subset
  let seed : GN21Lemma5EndpointVector (2 * P.complexity) :=
    gn21FiniteNNIntervalTupleEndpointVector
      (P.nnLower hP_subset) (P.nnUpper hP_subset)
  have hseed_domain : seed ∈
      gn21Lemma5EndpointDomain shape (2 * P.complexity) := by
    exact gn21FiniteNNIntervalTupleEndpointVector_mem_lemma5EndpointDomain
      shape P.complexity_pos (P.nnLower hP_subset) (P.nnUpper hP_subset)
  have hP_seed_ae : policyAlmostEverywhereEq mu P.policy
      (gn21EndpointVectorPolicy seed) := by
    exact P.policyAlmostEverywhereEq_endpointVector mu hP_subset
  have hP_seed_reward :
      Rhat P.policy = Rhat (gn21EndpointVectorPolicy seed) :=
    reward_eq_of_symmDiffContinuousAt_of_policyAlmostEverywhereEq
      mu Rhat (hcontinuous P.policy) hP_seed_ae
  rcases exists_gn21Lemma5EndpointDomain_reward_maximum
      shape (2 * P.complexity) Rhat
      (hendpoint_continuous (2 * P.complexity)) with
    ⟨endpoints, hdomain, hmax⟩
  refine ⟨2 * P.complexity, endpoints, hdomain, hmax, ?_⟩
  have hP_below : Rhat sigma - epsilon < Rhat P.policy := by
    have hleft := (abs_lt.1 hP_close).1
    linarith
  calc
    Rhat sigma - epsilon < Rhat P.policy := hP_below
    _ = Rhat (gn21EndpointVectorPolicy seed) := hP_seed_reward
    _ ≤ Rhat (gn21EndpointVectorPolicy endpoints) :=
      hmax seed hseed_domain

/-- A right derivative at a constrained maximum on `[0, ∞)` is nonpositive. -/
theorem right_derivative_nonpos_of_maximum_on_Icc
    (f : ℝ → ℝ) (derivativeValue upper : ℝ)
    (hupper : 0 < upper)
    (hmax : ∀ x ∈ Set.Icc (0 : ℝ) upper, f x ≤ f 0)
    (hderiv : HasDerivWithinAt f derivativeValue (Set.Ici 0) 0) :
    derivativeValue ≤ 0 := by
  have hlocal : IsLocalMaxOn f (Set.Ici 0) 0 := by
    unfold IsLocalMaxOn IsMaxFilter
    filter_upwards [
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hupper),
      self_mem_nhdsWithin] with x hxupper hxnonneg
    exact hmax x ⟨hxnonneg, le_of_lt hxupper⟩
  have hone_tangent :
      (1 : ℝ) ∈ posTangentConeAt (Set.Ici (0 : ℝ)) 0 := by
    have hsegment :
        segment ℝ (0 : ℝ) 1 ⊆ Set.Ici (0 : ℝ) := by
      rw [segment_eq_Icc (by norm_num : (0 : ℝ) ≤ 1)]
      exact Set.Icc_subset_Ici_self
    simpa using sub_mem_posTangentConeAt_of_segment_subset hsegment
  have hnonpos := hlocal.hasFDerivWithinAt_nonpos
    hderiv.hasFDerivWithinAt hone_tangent
  simpa using hnonpos

/--
One-sided endpoint Fermat condition for a coordinate fixed at zero in a
shape-specific compact endpoint domain.
-/
theorem endpoint_right_derivative_nonpos_of_lemma5EndpointDomain_maximum
    (shape : Lemma5DerivativeShape) (extra : Nat)
    (Rhat : SingleStateReward)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain shape extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain shape extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (coordinate : Fin (2 * (extra + 1)))
    (hcoordinate_zero : endpoints coordinate = 0)
    (upper : ℝ) (hupper : 0 < upper)
    (hfeasible : ∀ x ∈ Set.Icc (0 : ℝ) upper,
      gn21UpdateEndpoint endpoints coordinate x ∈
        gn21Lemma5EndpointDomain shape extra)
    (derivativeValue : ℝ)
    (hderiv :
      HasDerivWithinAt
        (fun x =>
          Rhat (gn21EndpointVectorPolicy
            (gn21UpdateEndpoint endpoints coordinate x)))
        derivativeValue (Set.Ici 0) 0) :
    derivativeValue ≤ 0 := by
  let path : ℝ → ℝ := fun x =>
    Rhat (gn21EndpointVectorPolicy
      (gn21UpdateEndpoint endpoints coordinate x))
  have hstart : gn21UpdateEndpoint endpoints coordinate 0 = endpoints := by
    unfold gn21UpdateEndpoint
    rw [ENNReal.ofReal_zero, ← hcoordinate_zero]
    exact Function.update_eq_self _ _
  apply right_derivative_nonpos_of_maximum_on_Icc
      path derivativeValue upper hupper
  · intro x hx
    simpa [path, hstart] using hmax
      (gn21UpdateEndpoint endpoints coordinate x) (hfeasible x hx)
  · exact hderiv

/-- The response-sign version of the one-sided zero-endpoint Fermat condition. -/
theorem endpoint_right_response_nonpos_of_lemma5EndpointDomain_maximum
    (shape : Lemma5DerivativeShape) (extra : Nat)
    (Rhat : SingleStateReward)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain shape extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain shape extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (coordinate : Fin (2 * (extra + 1)))
    (hcoordinate_zero : endpoints coordinate = 0)
    (upper : ℝ) (hupper : 0 < upper)
    (hfeasible : ∀ x ∈ Set.Icc (0 : ℝ) upper,
      gn21UpdateEndpoint endpoints coordinate x ∈
        gn21Lemma5EndpointDomain shape extra)
    (responseValue : ℝ)
    (hderiv :
      ∃ derivativeValue : ℝ,
        HasDerivWithinAt
            (fun x =>
              Rhat (gn21EndpointVectorPolicy
                (gn21UpdateEndpoint endpoints coordinate x)))
            derivativeValue (Set.Ici 0) 0 ∧
          sameStrictSign derivativeValue responseValue) :
    responseValue ≤ 0 := by
  rcases hderiv with ⟨derivativeValue, hderivative, hsame_sign⟩
  apply sameStrictSign_nonpos_right hsame_sign
  exact endpoint_right_derivative_nonpos_of_lemma5EndpointDomain_maximum
    shape extra Rhat hdomain hmax coordinate hcoordinate_zero upper hupper
    hfeasible derivativeValue hderivative

/-! ## Interior response-shape exclusions at an endpoint maximizer -/

/--
In the positive-response case, a maximizing vector cannot retain a genuine
gap after a positive upper endpoint.  This is the interior part of the source
positive-case expansion argument.  The endpoint derivative premise is
unbundled and refers to the current policy directly.
-/
theorem positive_endpoint_maximum_gap_eq_of_upper_pos
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .positive extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_positive :
      ∀ u : TripLength, 0 < u →
        0 < response (gn21EndpointVectorPolicy endpoints) u)
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (i : Fin extra)
    (hupper_pos : 0 < endpoints (gn21Lemma5GapUpperIndex i)) :
    endpoints (gn21Lemma5GapUpperIndex i) =
      endpoints (gn21Lemma5GapLowerIndex i) := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  have hle :
      endpoints (gn21Lemma5GapUpperIndex i) ≤
        endpoints (gn21Lemma5GapLowerIndex i) :=
    hordered (le_of_lt (gn21Lemma5GapUpperIndex_lt_lowerIndex i))
  apply le_antisymm hle
  by_contra hnot
  have hgap :
      endpoints (gn21Lemma5GapUpperIndex i) <
        endpoints (gn21Lemma5GapLowerIndex i) :=
    lt_of_not_ge hnot
  rcases exists_real_right_neighborhood_of_ennreal_lt hgap with
    ⟨value, upper, hvalue, hvalue_upper, hupper_bound⟩
  have hvalue_pos : 0 < value := by
    rw [hvalue, ENNReal.ofReal_pos] at hupper_pos
    exact hupper_pos
  rcases hupper_derivative i hvalue with
    ⟨derivativeValue, hderivative, hsame_sign⟩
  have hderivative_nonpos : derivativeValue ≤ 0 := by
    apply endpoint_derivative_nonpos_of_lemma5EndpointDomain_maximum
        .positive extra Rhat hdomain hmax
        (gn21Lemma5GapUpperIndex i) hvalue hvalue_upper
    · intro j hj
      exact hupper_bound.trans
        (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt i hj))
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_first i
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_last i
    · exact hderivative
  have hresponse_nonpos :
      response (gn21EndpointVectorPolicy endpoints) value ≤ 0 :=
    sameStrictSign_nonpos_right hsame_sign hderivative_nonpos
  exact (not_lt_of_ge hresponse_nonpos)
    (hresponse_positive value hvalue_pos)

/--
Zero-endpoint part of the positive-response expansion argument.  Positivity is
required only at interior positive endpoints; strict endpoint-path monotonicity
then excludes a gap beginning at zero without assigning a derivative sign at
zero itself.
-/
theorem positive_endpoint_maximum_gap_eq_of_upper_zero
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .positive extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_positive :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        ∀ u : TripLength, 0 < u →
          0 < response (gn21EndpointVectorPolicy candidate) u)
    (hpath_continuous :
      ∀ (i : Fin extra) (upper : ℝ), 0 < upper →
        ContinuousOn
          (fun x =>
            Rhat (gn21EndpointVectorPolicy
              (gn21UpdateEndpoint endpoints
                (gn21Lemma5GapUpperIndex i) x)))
          (Set.Icc 0 upper))
    (hpath_derivative :
      ∀ (i : Fin extra) (upper : ℝ) (x : ℝ),
        x ∈ Set.Ioo 0 upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun y =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) y)))
              derivativeValue x ∧
            sameStrictSign derivativeValue
              (response
                (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)) x))
    (i : Fin extra)
    (hupper_zero : endpoints (gn21Lemma5GapUpperIndex i) = 0) :
    endpoints (gn21Lemma5GapUpperIndex i) =
      endpoints (gn21Lemma5GapLowerIndex i) := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  have hle :
      endpoints (gn21Lemma5GapUpperIndex i) ≤
        endpoints (gn21Lemma5GapLowerIndex i) :=
    hordered (le_of_lt (gn21Lemma5GapUpperIndex_lt_lowerIndex i))
  apply le_antisymm hle
  by_contra hnot
  have hlower_pos : 0 < endpoints (gn21Lemma5GapLowerIndex i) := by
    rw [hupper_zero] at hnot
    exact lt_of_not_ge hnot
  rcases exists_pos_real_of_zero_lt_ennreal hlower_pos with
    ⟨upper, hupper_pos, hupper_bound⟩
  let path : ℝ → ℝ := fun x =>
    Rhat (gn21EndpointVectorPolicy
      (gn21UpdateEndpoint endpoints (gn21Lemma5GapUpperIndex i) x))
  have hcandidate_mem :
      ∀ x ∈ Set.Icc (0 : ℝ) upper,
        gn21UpdateEndpoint endpoints (gn21Lemma5GapUpperIndex i) x ∈
          gn21Lemma5EndpointDomain .positive extra := by
    intro x hx
    apply gn21UpdateEndpoint_mem_lemma5EndpointDomain
        .positive extra hdomain (gn21Lemma5GapUpperIndex i) x
    · intro j hj
      calc
        endpoints j ≤ endpoints (gn21Lemma5GapUpperIndex i) :=
          hordered (le_of_lt hj)
        _ = 0 := hupper_zero
        _ ≤ ENNReal.ofReal x := bot_le
    · intro j hj
      exact (ENNReal.ofReal_mono hx.2).trans
        (hupper_bound.trans
          (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt i hj)))
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_first i
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_last i
  have hpath_lt : path 0 < path upper := by
    apply endpoint_path_lt_of_exists_hasDerivAt_pos_on_Icc hupper_pos
    · exact hpath_continuous i upper hupper_pos
    · intro x hx
      rcases hpath_derivative i upper x hx with
        ⟨derivativeValue, hderivative, hsame_sign⟩
      refine ⟨derivativeValue, hderivative, ?_⟩
      apply sameStrictSign_pos_left hsame_sign
      exact hresponse_positive
        (gn21UpdateEndpoint endpoints (gn21Lemma5GapUpperIndex i) x)
        (hcandidate_mem x ⟨le_of_lt hx.1, le_of_lt hx.2⟩) x hx.1
  have hstart :
      gn21UpdateEndpoint endpoints (gn21Lemma5GapUpperIndex i) 0 =
        endpoints := by
    unfold gn21UpdateEndpoint
    rw [ENNReal.ofReal_zero, ← hupper_zero]
    exact Function.update_eq_self _ _
  have hbound := hmax
    (gn21UpdateEndpoint endpoints (gn21Lemma5GapUpperIndex i) upper)
    (hcandidate_mem upper ⟨le_of_lt hupper_pos, le_rfl⟩)
  have hstrict :
      Rhat (gn21EndpointVectorPolicy endpoints) <
        Rhat (gn21EndpointVectorPolicy
          (gn21UpdateEndpoint endpoints
            (gn21Lemma5GapUpperIndex i) upper)) := by
    simpa [path, hstart] using hpath_lt
  exact (not_lt_of_ge hbound) hstrict

/-- Positive response closes every adjacent gap of a maximizing endpoint vector. -/
theorem positive_endpoint_maximum_all_gaps_eq
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .positive extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_positive :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        ∀ u : TripLength, 0 < u →
          0 < response (gn21EndpointVectorPolicy candidate) u)
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hpath_continuous :
      ∀ (i : Fin extra) (upper : ℝ), 0 < upper →
        ContinuousOn
          (fun x =>
            Rhat (gn21EndpointVectorPolicy
              (gn21UpdateEndpoint endpoints
                (gn21Lemma5GapUpperIndex i) x)))
          (Set.Icc 0 upper))
    (hpath_derivative :
      ∀ (i : Fin extra) (upper : ℝ) (x : ℝ),
        x ∈ Set.Ioo 0 upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun y =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) y)))
              derivativeValue x ∧
            sameStrictSign derivativeValue
              (response
                (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)) x)) :
    ∀ i : Fin extra,
      endpoints (gn21Lemma5GapUpperIndex i) =
        endpoints (gn21Lemma5GapLowerIndex i) := by
  intro i
  rcases eq_zero_or_pos
      (endpoints (gn21Lemma5GapUpperIndex i)) with hzero | hpos
  · exact positive_endpoint_maximum_gap_eq_of_upper_zero
      extra Rhat response hdomain hmax hresponse_positive
      hpath_continuous hpath_derivative i hzero
  · exact positive_endpoint_maximum_gap_eq_of_upper_pos
      extra Rhat response hdomain hmax
      (hresponse_positive endpoints hdomain) hupper_derivative i hpos

/--
A positive-response endpoint maximizer is accept-all modulo the atomless
endpoint set.  This is the exact policy-form conclusion of the positive row of
the source table for a finite endpoint family.
-/
theorem positive_endpoint_maximum_source_form_ae
    (mu : Measure TripLength) [NoAtoms mu]
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .positive extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_positive :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        ∀ u : TripLength, 0 < u →
          0 < response (gn21EndpointVectorPolicy candidate) u)
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hpath_continuous :
      ∀ (i : Fin extra) (upper : ℝ), 0 < upper →
        ContinuousOn
          (fun x =>
            Rhat (gn21EndpointVectorPolicy
              (gn21UpdateEndpoint endpoints
                (gn21Lemma5GapUpperIndex i) x)))
          (Set.Icc 0 upper))
    (hpath_derivative :
      ∀ (i : Fin extra) (upper : ℝ) (x : ℝ),
        x ∈ Set.Ioo 0 upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun y =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) y)))
              derivativeValue x ∧
            sameStrictSign derivativeValue
              (response
                (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)) x)) :
    lemma5SourcePolicyFormAlmostEverywhere mu .positive
      (gn21EndpointVectorPolicy endpoints) := by
  rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
  change endpoints (gn21Lemma5FirstEndpointIndex extra) = 0 at hfirst
  change endpoints (gn21Lemma5LastEndpointIndex extra) = ∞ at hlast
  have hgaps := positive_endpoint_maximum_all_gaps_eq
    extra Rhat response ⟨⟨hordered, hfirst⟩, hlast⟩ hmax
    hresponse_positive hupper_derivative hpath_continuous hpath_derivative
  refine ⟨acceptAllPolicy, rfl, ?_⟩
  have hae :=
    policyAlmostEverywhereEq_endpointVectorPolicy_of_all_gaps_eq
      mu extra endpoints hordered hgaps
  rw [hfirst, hlast] at hae
  simpa using hae

/--
A strictly increasing response excludes a fully separated accepted interval
followed by another interval at an endpoint-domain maximizer.  Both endpoint
derivatives are taken at the current policy: the upper endpoint cannot profit
from moving right, while the lower endpoint cannot profit from moving right;
strict increase makes those two signs incompatible.
-/
theorem increasing_endpoint_maximum_not_strict_at_positive_interval
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyIncreasing extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyIncreasing extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_increasing :
      StrictMonoOn (response (gn21EndpointVectorPolicy endpoints))
        (Set.Ioi 0))
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints
            (gn21LowerEndpointIndex (Fin.castSucc i)) =
              ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (i : Fin extra)
    (hinterval_strict :
      endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) <
        endpoints (gn21Lemma5GapUpperIndex i))
    (hgap_strict :
      endpoints (gn21Lemma5GapUpperIndex i) <
        endpoints (gn21Lemma5GapLowerIndex i))
    (hlower_pos :
      0 < endpoints (gn21LowerEndpointIndex (Fin.castSucc i))) : False := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  have hlower_upper := hinterval_strict
  have hupper_next := hgap_strict
  rcases exists_real_right_neighborhood_of_ennreal_lt hupper_next with
    ⟨upperValue, upperBound, hupper_value, hupper_lt_bound,
      hupper_bound⟩
  rcases exists_real_right_neighborhood_of_ennreal_lt hlower_upper with
    ⟨lowerValue, lowerBound, hlower_value, hlower_lt_bound,
      hlower_bound⟩
  have hupper_response_nonpos :
      response (gn21EndpointVectorPolicy endpoints) upperValue ≤ 0 := by
    apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
        .strictlyIncreasing extra Rhat hdomain hmax
        (gn21Lemma5GapUpperIndex i) hupper_value hupper_lt_bound
    · intro j hj
      exact hupper_bound.trans
        (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt i hj))
    · intro hshape
      simp at hshape
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_last i
    · exact hupper_derivative i hupper_value
  have hlower_response_nonneg :
      0 ≤ response (gn21EndpointVectorPolicy endpoints) lowerValue := by
    have hlower_derivative_nonpos :
        -response (gn21EndpointVectorPolicy endpoints) lowerValue ≤ 0 := by
      apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
          .strictlyIncreasing extra Rhat hdomain hmax
          (gn21LowerEndpointIndex (Fin.castSucc i)) hlower_value
          hlower_lt_bound
      · intro j hj
        exact hlower_bound.trans
          (hordered (by
            apply Fin.mk_le_mk.2
            change 2 * i.1 + 1 ≤ j.1
            have hj' : 2 * i.1 < j.1 := by
              simpa [gn21LowerEndpointIndex] using hj
            omega))
      · intro hshape
        simp at hshape
      · intro _ hlast
        have hval := congrArg Fin.val hlast
        simp [gn21LowerEndpointIndex, gn21Lemma5LastEndpointIndex] at hval
        omega
      · exact hlower_derivative i hlower_value
    linarith
  have hlower_value_pos : 0 < lowerValue := by
    rw [hlower_value, ENNReal.ofReal_pos] at hlower_pos
    exact hlower_pos
  have hlower_value_lt_upperValue : lowerValue < upperValue := by
    rw [hlower_value, hupper_value] at hlower_upper
    exact ((ENNReal.ofReal_lt_ofReal_iff').mp hlower_upper).1
  have hupper_value_pos : 0 < upperValue :=
    lt_trans hlower_value_pos hlower_value_lt_upperValue
  have hresponse_lt :
      response (gn21EndpointVectorPolicy endpoints) lowerValue <
        response (gn21EndpointVectorPolicy endpoints) upperValue :=
    hresponse_increasing hlower_value_pos hupper_value_pos
      hlower_value_lt_upperValue
  linarith

/--
The zero-lower-endpoint companion to the increasing-response exclusion.  The
lower endpoint uses a right derivative on the feasible half-line, so no
two-sided derivative or response-sign assumption at negative trip lengths is
introduced.
-/
theorem increasing_endpoint_maximum_not_strict_at_zero_interval
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyIncreasing extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyIncreasing extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_increasing :
      StrictMonoOn (response (gn21EndpointVectorPolicy endpoints))
        (Set.Ici 0))
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (i : Fin extra)
    (hinterval_strict :
      endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) <
        endpoints (gn21Lemma5GapUpperIndex i))
    (hgap_strict :
      endpoints (gn21Lemma5GapUpperIndex i) <
        endpoints (gn21Lemma5GapLowerIndex i))
    (hlower_zero :
      endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) = 0)
    (hlower_right_derivative :
      ∃ derivativeValue : ℝ,
        HasDerivWithinAt
            (fun x =>
              Rhat (gn21EndpointVectorPolicy
                (gn21UpdateEndpoint endpoints
                  (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
            derivativeValue (Set.Ici 0) 0 ∧
          sameStrictSign derivativeValue
            (-response (gn21EndpointVectorPolicy endpoints) 0)) : False := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  have hupper_pos :
      0 < endpoints (gn21Lemma5GapUpperIndex i) := by
    rw [← hlower_zero]
    exact hinterval_strict
  rcases exists_real_right_neighborhood_of_ennreal_lt hgap_strict with
    ⟨upperValue, upperBound, hupper_value, hupper_lt_bound,
      hupper_bound⟩
  have hupper_response_nonpos :
      response (gn21EndpointVectorPolicy endpoints) upperValue ≤ 0 := by
    apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
        .strictlyIncreasing extra Rhat hdomain hmax
        (gn21Lemma5GapUpperIndex i) hupper_value hupper_lt_bound
    · intro j hj
      exact hupper_bound.trans
        (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt i hj))
    · intro hshape
      simp at hshape
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_last i
    · exact hupper_derivative i hupper_value
  rcases exists_pos_real_of_zero_lt_ennreal hupper_pos with
    ⟨moveBound, hmoveBound_pos, hmoveBound_upper⟩
  have hlower_feasible : ∀ x ∈ Set.Icc (0 : ℝ) moveBound,
      gn21UpdateEndpoint endpoints
          (gn21LowerEndpointIndex (Fin.castSucc i)) x ∈
        gn21Lemma5EndpointDomain .strictlyIncreasing extra := by
    intro x hx
    apply gn21UpdateEndpoint_mem_lemma5EndpointDomain
        .strictlyIncreasing extra hdomain
        (gn21LowerEndpointIndex (Fin.castSucc i)) x
    · intro j hj
      calc
        endpoints j ≤
            endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) :=
          hordered (le_of_lt hj)
        _ = 0 := hlower_zero
        _ ≤ ENNReal.ofReal x := bot_le
    · intro j hj
      calc
        ENNReal.ofReal x ≤ ENNReal.ofReal moveBound :=
          ENNReal.ofReal_mono hx.2
        _ ≤ endpoints (gn21Lemma5GapUpperIndex i) := hmoveBound_upper
        _ ≤ endpoints j := hordered (by
          apply Fin.mk_le_mk.2
          change 2 * i.1 + 1 ≤ j.1
          have hj' : 2 * i.1 < j.1 := by
            simpa [gn21LowerEndpointIndex] using hj
          omega)
    · intro hshape
      simp at hshape
    · intro _ hlast
      have hval := congrArg Fin.val hlast
      simp [gn21LowerEndpointIndex, gn21Lemma5LastEndpointIndex] at hval
      omega
  have hlower_derivative_nonpos :
      -response (gn21EndpointVectorPolicy endpoints) 0 ≤ 0 := by
    exact endpoint_right_response_nonpos_of_lemma5EndpointDomain_maximum
      .strictlyIncreasing extra Rhat hdomain hmax
      (gn21LowerEndpointIndex (Fin.castSucc i)) hlower_zero
      moveBound hmoveBound_pos hlower_feasible
      (-response (gn21EndpointVectorPolicy endpoints) 0)
      hlower_right_derivative
  have hresponse_zero_nonneg :
      0 ≤ response (gn21EndpointVectorPolicy endpoints) 0 := by
    linarith
  have hupper_value_pos : 0 < upperValue := by
    rw [hlower_zero, hupper_value, ENNReal.ofReal_pos] at hinterval_strict
    exact hinterval_strict
  have hresponse_lt :
      response (gn21EndpointVectorPolicy endpoints) 0 <
        response (gn21EndpointVectorPolicy endpoints) upperValue :=
    hresponse_increasing (by simp) (by exact le_of_lt hupper_value_pos)
      hupper_value_pos
  linarith

/-- A reduced strictly-increasing endpoint maximizer has one interval slot. -/
theorem increasing_compressionReduced_extra_eq_zero
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyIncreasing extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyIncreasing extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hreduced :
      gn21Lemma5CompressionReduced .strictlyIncreasing extra endpoints)
    (hresponse_increasing :
      StrictMonoOn (response (gn21EndpointVectorPolicy endpoints))
        (Set.Ici 0))
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints
            (gn21LowerEndpointIndex (Fin.castSucc i)) =
              ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_right_derivative :
      ∀ (i : Fin extra),
        endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (-response (gn21EndpointVectorPolicy endpoints) 0)) :
    extra = 0 := by
  cases extra with
  | zero => rfl
  | succ extra =>
      exfalso
      let i : Fin (extra + 1) := Fin.last extra
      have hordered := gn21Lemma5EndpointDomain_ordered hdomain
      have hremovable :
          ¬ gn21Lemma5IrreducibleIntervalSlot .strictlyIncreasing
            (extra + 1) (Fin.castSucc i) := by
        simp [gn21Lemma5IrreducibleIntervalSlot]
      have hinterval_strict :
          endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) <
            endpoints (gn21Lemma5GapUpperIndex i) := by
        simpa [gn21Lemma5GapUpperIndex] using
          gn21Lemma5CompressionReduced_interval_strict
            .strictlyIncreasing (extra + 1) hordered hreduced
            (Fin.castSucc i) hremovable
      have hgap_strict :
          endpoints (gn21Lemma5GapUpperIndex i) <
            endpoints (gn21Lemma5GapLowerIndex i) := hreduced.2 i
      rcases eq_zero_or_pos
          (endpoints (gn21LowerEndpointIndex (Fin.castSucc i))) with
        hlower_zero | hlower_pos
      · exact increasing_endpoint_maximum_not_strict_at_zero_interval
          (extra + 1) Rhat response hdomain hmax hresponse_increasing
          hupper_derivative i hinterval_strict hgap_strict hlower_zero
          (hlower_right_derivative i hlower_zero)
      · exact increasing_endpoint_maximum_not_strict_at_positive_interval
          (extra + 1) Rhat response hdomain hmax
          (hresponse_increasing.mono Set.Ioi_subset_Ici_self)
          hupper_derivative hlower_derivative i hinterval_strict
          hgap_strict hlower_pos

/--
A strictly decreasing response excludes a separated gap followed by a
nondegenerate interval at an endpoint-domain maximizer.  The upper endpoint
and the following lower endpoint can both move right; their necessary signs
contradict strict decrease.
-/
theorem decreasing_endpoint_maximum_not_strict_at_positive_gap
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyDecreasing extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyDecreasing extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_decreasing :
      StrictAntiOn (response (gn21EndpointVectorPolicy endpoints))
        (Set.Ioi 0))
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hnext_lower_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapLowerIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapLowerIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (i : Fin extra)
    (hgap_strict :
      endpoints (gn21Lemma5GapUpperIndex i) <
        endpoints (gn21Lemma5GapLowerIndex i))
    (hnext_interval_strict :
      endpoints (gn21Lemma5GapLowerIndex i) <
        endpoints (gn21UpperEndpointIndex (Fin.succ i)))
    (hupper_pos :
      0 < endpoints (gn21Lemma5GapUpperIndex i)) : False := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  have hupper_next := hgap_strict
  have hnext_upper := hnext_interval_strict
  rcases exists_real_right_neighborhood_of_ennreal_lt hupper_next with
    ⟨upperValue, upperBound, hupper_value, hupper_lt_bound,
      hupper_bound⟩
  rcases exists_real_right_neighborhood_of_ennreal_lt hnext_upper with
    ⟨nextValue, nextBound, hnext_value, hnext_lt_bound,
      hnext_bound⟩
  have hupper_response_nonpos :
      response (gn21EndpointVectorPolicy endpoints) upperValue ≤ 0 := by
    apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
        .strictlyDecreasing extra Rhat hdomain hmax
        (gn21Lemma5GapUpperIndex i) hupper_value hupper_lt_bound
    · intro j hj
      exact hupper_bound.trans
        (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt i hj))
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_first i
    · intro hshape
      simp at hshape
    · exact hupper_derivative i hupper_value
  have hnext_response_nonneg :
      0 ≤ response (gn21EndpointVectorPolicy endpoints) nextValue := by
    have hnext_derivative_nonpos :
        -response (gn21EndpointVectorPolicy endpoints) nextValue ≤ 0 := by
      apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
          .strictlyDecreasing extra Rhat hdomain hmax
          (gn21Lemma5GapLowerIndex i) hnext_value hnext_lt_bound
      · intro j hj
        exact hnext_bound.trans
          (hordered (by
            apply Fin.mk_le_mk.2
            change 2 * i.1 + 3 ≤ j.1
            have hj' : 2 * i.1 + 2 < j.1 := by
              simpa [gn21Lemma5GapLowerIndex] using hj
            omega))
      · intro _
        exact gn21Lemma5GapLowerIndex_ne_first i
      · intro hshape
        simp at hshape
      · exact hnext_lower_derivative i hnext_value
    linarith
  have hupper_value_pos : 0 < upperValue := by
    rw [hupper_value, ENNReal.ofReal_pos] at hupper_pos
    exact hupper_pos
  have hupper_value_lt_nextValue : upperValue < nextValue := by
    rw [hupper_value, hnext_value] at hupper_next
    exact ((ENNReal.ofReal_lt_ofReal_iff').mp hupper_next).1
  have hnext_value_pos : 0 < nextValue :=
    lt_trans hupper_value_pos hupper_value_lt_nextValue
  have hresponse_lt :
      response (gn21EndpointVectorPolicy endpoints) nextValue <
        response (gn21EndpointVectorPolicy endpoints) upperValue :=
    hresponse_decreasing hupper_value_pos hnext_value_pos
      hupper_value_lt_nextValue
  linarith

/-- Zero-upper-endpoint companion to the decreasing-response exclusion. -/
theorem decreasing_endpoint_maximum_not_strict_at_zero_gap
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyDecreasing extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyDecreasing extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_decreasing :
      StrictAntiOn (response (gn21EndpointVectorPolicy endpoints))
        (Set.Ici 0))
    (hnext_lower_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapLowerIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapLowerIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (i : Fin extra)
    (hgap_strict :
      endpoints (gn21Lemma5GapUpperIndex i) <
        endpoints (gn21Lemma5GapLowerIndex i))
    (hnext_interval_strict :
      endpoints (gn21Lemma5GapLowerIndex i) <
        endpoints (gn21UpperEndpointIndex (Fin.succ i)))
    (hupper_zero : endpoints (gn21Lemma5GapUpperIndex i) = 0)
    (hupper_right_derivative :
      ∃ derivativeValue : ℝ,
        HasDerivWithinAt
            (fun x =>
              Rhat (gn21EndpointVectorPolicy
                (gn21UpdateEndpoint endpoints
                  (gn21Lemma5GapUpperIndex i) x)))
            derivativeValue (Set.Ici 0) 0 ∧
          sameStrictSign derivativeValue
            (response (gn21EndpointVectorPolicy endpoints) 0)) : False := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  rcases exists_real_right_neighborhood_of_ennreal_lt hnext_interval_strict with
    ⟨nextValue, nextBound, hnext_value, hnext_lt_bound,
      hnext_bound⟩
  have hnext_response_nonneg :
      0 ≤ response (gn21EndpointVectorPolicy endpoints) nextValue := by
    have hnext_derivative_nonpos :
        -response (gn21EndpointVectorPolicy endpoints) nextValue ≤ 0 := by
      apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
          .strictlyDecreasing extra Rhat hdomain hmax
          (gn21Lemma5GapLowerIndex i) hnext_value hnext_lt_bound
      · intro j hj
        exact hnext_bound.trans
          (hordered (by
            apply Fin.mk_le_mk.2
            change 2 * i.1 + 3 ≤ j.1
            have hj' : 2 * i.1 + 2 < j.1 := by
              simpa [gn21Lemma5GapLowerIndex] using hj
            omega))
      · intro _
        exact gn21Lemma5GapLowerIndex_ne_first i
      · intro hshape
        simp at hshape
      · exact hnext_lower_derivative i hnext_value
    linarith
  have hnext_endpoint_pos :
      0 < endpoints (gn21Lemma5GapLowerIndex i) := by
    rw [← hupper_zero]
    exact hgap_strict
  rcases exists_pos_real_of_zero_lt_ennreal hnext_endpoint_pos with
    ⟨moveBound, hmoveBound_pos, hmoveBound_next⟩
  have hupper_feasible : ∀ x ∈ Set.Icc (0 : ℝ) moveBound,
      gn21UpdateEndpoint endpoints (gn21Lemma5GapUpperIndex i) x ∈
        gn21Lemma5EndpointDomain .strictlyDecreasing extra := by
    intro x hx
    apply gn21UpdateEndpoint_mem_lemma5EndpointDomain
        .strictlyDecreasing extra hdomain
        (gn21Lemma5GapUpperIndex i) x
    · intro j hj
      calc
        endpoints j ≤ endpoints (gn21Lemma5GapUpperIndex i) :=
          hordered (le_of_lt hj)
        _ = 0 := hupper_zero
        _ ≤ ENNReal.ofReal x := bot_le
    · intro j hj
      exact (ENNReal.ofReal_mono hx.2).trans
        (hmoveBound_next.trans
          (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt i hj)))
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_first i
    · intro hshape
      simp at hshape
  have hupper_response_nonpos :
      response (gn21EndpointVectorPolicy endpoints) 0 ≤ 0 := by
    exact endpoint_right_response_nonpos_of_lemma5EndpointDomain_maximum
      .strictlyDecreasing extra Rhat hdomain hmax
      (gn21Lemma5GapUpperIndex i) hupper_zero
      moveBound hmoveBound_pos hupper_feasible
      (response (gn21EndpointVectorPolicy endpoints) 0)
      hupper_right_derivative
  have hnext_value_pos : 0 < nextValue := by
    rw [hnext_value, ENNReal.ofReal_pos] at hnext_endpoint_pos
    exact hnext_endpoint_pos
  have hresponse_lt :
      response (gn21EndpointVectorPolicy endpoints) nextValue <
        response (gn21EndpointVectorPolicy endpoints) 0 :=
    hresponse_decreasing (by simp) (le_of_lt hnext_value_pos)
      hnext_value_pos
  linarith

/-- A reduced strictly-decreasing endpoint maximizer has one interval slot. -/
theorem decreasing_compressionReduced_extra_eq_zero
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyDecreasing extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyDecreasing extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hreduced :
      gn21Lemma5CompressionReduced .strictlyDecreasing extra endpoints)
    (hresponse_decreasing :
      StrictAntiOn (response (gn21EndpointVectorPolicy endpoints))
        (Set.Ici 0))
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hnext_lower_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapLowerIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapLowerIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (hupper_right_derivative :
      ∀ (i : Fin extra),
        endpoints (gn21Lemma5GapUpperIndex i) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21Lemma5GapUpperIndex i) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (response (gn21EndpointVectorPolicy endpoints) 0)) :
    extra = 0 := by
  cases extra with
  | zero => rfl
  | succ extra =>
      exfalso
      let i : Fin (extra + 1) := 0
      have hordered := gn21Lemma5EndpointDomain_ordered hdomain
      have hremovable :
          ¬ gn21Lemma5IrreducibleIntervalSlot .strictlyDecreasing
            (extra + 1) (Fin.succ i) := by
        simp [gn21Lemma5IrreducibleIntervalSlot]
      have hnext_interval_strict :
          endpoints (gn21Lemma5GapLowerIndex i) <
            endpoints (gn21UpperEndpointIndex (Fin.succ i)) := by
        simpa [gn21Lemma5GapLowerIndex, gn21LowerEndpointIndex] using
          gn21Lemma5CompressionReduced_interval_strict
            .strictlyDecreasing (extra + 1) hordered hreduced
            (Fin.succ i) hremovable
      have hgap_strict :
          endpoints (gn21Lemma5GapUpperIndex i) <
            endpoints (gn21Lemma5GapLowerIndex i) := hreduced.2 i
      rcases eq_zero_or_pos
          (endpoints (gn21Lemma5GapUpperIndex i)) with
        hupper_zero | hupper_pos
      · exact decreasing_endpoint_maximum_not_strict_at_zero_gap
          (extra + 1) Rhat response hdomain hmax hresponse_decreasing
          hnext_lower_derivative i hgap_strict hnext_interval_strict
          hupper_zero (hupper_right_derivative i hupper_zero)
      · exact decreasing_endpoint_maximum_not_strict_at_positive_gap
          (extra + 1) Rhat response hdomain hmax
          (hresponse_decreasing.mono Set.Ioi_subset_Ici_self)
          hupper_derivative hnext_lower_derivative i hgap_strict
          hnext_interval_strict hupper_pos

/--
A strictly quasi-concave response excludes two fully separated positive
intervals at an endpoint-domain maximizer.  Maximality makes both lower
responses nonnegative and the upper response before the gap nonpositive,
contradicting strict quasi-concavity between the two lower endpoints.
-/
theorem quasiConcave_endpoint_maximum_not_strict_at_positive_pair
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyQuasiConcave extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyQuasiConcave extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_quasiConcave :
      strictQuasiConcaveOnPositive
        (response (gn21EndpointVectorPolicy endpoints)))
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (slot : Fin (extra + 1)) {value : ℝ},
        endpoints (gn21LowerEndpointIndex slot) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21LowerEndpointIndex slot) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (i : Fin extra)
    (hleft_interval_strict :
      endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) <
        endpoints (gn21Lemma5GapUpperIndex i))
    (hgap_strict :
      endpoints (gn21Lemma5GapUpperIndex i) <
        endpoints (gn21Lemma5GapLowerIndex i))
    (hright_interval_strict :
      endpoints (gn21Lemma5GapLowerIndex i) <
        endpoints (gn21UpperEndpointIndex (Fin.succ i)))
    (hleft_lower_pos :
      0 < endpoints (gn21LowerEndpointIndex (Fin.castSucc i))) : False := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  have hleft_lower_upper := hleft_interval_strict
  have hleft_upper_right_lower := hgap_strict
  have hright_lower_upper := hright_interval_strict
  rcases exists_real_right_neighborhood_of_ennreal_lt hleft_lower_upper with
    ⟨leftLowerValue, leftLowerBound, hleft_lower_value,
      hleft_lower_lt_bound, hleft_lower_bound⟩
  rcases exists_real_right_neighborhood_of_ennreal_lt
      hleft_upper_right_lower with
    ⟨leftUpperValue, leftUpperBound, hleft_upper_value,
      hleft_upper_lt_bound, hleft_upper_bound⟩
  rcases exists_real_right_neighborhood_of_ennreal_lt hright_lower_upper with
    ⟨rightLowerValue, rightLowerBound, hright_lower_value,
      hright_lower_lt_bound, hright_lower_bound⟩
  have hleft_upper_response_nonpos :
      response (gn21EndpointVectorPolicy endpoints) leftUpperValue ≤ 0 := by
    apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
        .strictlyQuasiConcave extra Rhat hdomain hmax
        (gn21Lemma5GapUpperIndex i) hleft_upper_value
        hleft_upper_lt_bound
    · intro j hj
      exact hleft_upper_bound.trans
        (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt i hj))
    · intro hshape
      simp at hshape
    · intro hshape
      simp at hshape
    · exact hupper_derivative i hleft_upper_value
  have hleft_lower_response_nonneg :
      0 ≤ response (gn21EndpointVectorPolicy endpoints) leftLowerValue := by
    have hderivative_nonpos :
        -response (gn21EndpointVectorPolicy endpoints) leftLowerValue ≤ 0 := by
      apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
          .strictlyQuasiConcave extra Rhat hdomain hmax
          (gn21LowerEndpointIndex (Fin.castSucc i)) hleft_lower_value
          hleft_lower_lt_bound
      · intro j hj
        exact hleft_lower_bound.trans
          (hordered (by
            apply Fin.mk_le_mk.2
            change 2 * i.1 + 1 ≤ j.1
            have hj' : 2 * i.1 < j.1 := by
              simpa [gn21LowerEndpointIndex] using hj
            omega))
      · intro hshape
        simp at hshape
      · intro hshape
        simp at hshape
      · exact hlower_derivative (Fin.castSucc i) hleft_lower_value
    linarith
  have hright_lower_response_nonneg :
      0 ≤ response (gn21EndpointVectorPolicy endpoints) rightLowerValue := by
    have hderivative_nonpos :
        -response (gn21EndpointVectorPolicy endpoints) rightLowerValue ≤ 0 := by
      apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
          .strictlyQuasiConcave extra Rhat hdomain hmax
          (gn21Lemma5GapLowerIndex i) hright_lower_value
          hright_lower_lt_bound
      · intro j hj
        exact hright_lower_bound.trans
          (hordered (by
            apply Fin.mk_le_mk.2
            change 2 * i.1 + 3 ≤ j.1
            have hj' : 2 * i.1 + 2 < j.1 := by
              simpa [gn21Lemma5GapLowerIndex] using hj
            omega))
      · intro hshape
        simp at hshape
      · intro hshape
        simp at hshape
      · simpa [gn21Lemma5GapLowerIndex, gn21LowerEndpointIndex] using
          (hlower_derivative (Fin.succ i) hright_lower_value)
    linarith
  have hleft_lower_value_pos : 0 < leftLowerValue := by
    rw [hleft_lower_value, ENNReal.ofReal_pos] at hleft_lower_pos
    exact hleft_lower_pos
  have hleft_lower_lt_leftUpper : leftLowerValue < leftUpperValue := by
    rw [hleft_lower_value, hleft_upper_value] at hleft_lower_upper
    exact ((ENNReal.ofReal_lt_ofReal_iff').mp hleft_lower_upper).1
  have hleft_upper_lt_rightLower : leftUpperValue < rightLowerValue := by
    rw [hleft_upper_value, hright_lower_value] at hleft_upper_right_lower
    exact ((ENNReal.ofReal_lt_ofReal_iff').mp hleft_upper_right_lower).1
  have hleft_upper_response_pos :
      0 < response (gn21EndpointVectorPolicy endpoints) leftUpperValue :=
    lemma5_strictQuasiConcave_gap_endpoint_sign_of_lower_nonneg
      (response (gn21EndpointVectorPolicy endpoints))
      hresponse_quasiConcave hleft_lower_value_pos
      hleft_lower_lt_leftUpper hleft_upper_lt_rightLower
      hleft_lower_response_nonneg hright_lower_response_nonneg
  linarith

/-- Zero-left-endpoint companion to the quasi-concave pair exclusion. -/
theorem quasiConcave_endpoint_maximum_not_strict_at_zero_pair
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyQuasiConcave extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyQuasiConcave extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hzero_quasiConcave : ∀ {middle right : ℝ},
      0 < middle → middle < right →
        min (response (gn21EndpointVectorPolicy endpoints) 0)
            (response (gn21EndpointVectorPolicy endpoints) right) <
          response (gn21EndpointVectorPolicy endpoints) middle)
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (slot : Fin (extra + 1)) {value : ℝ},
        endpoints (gn21LowerEndpointIndex slot) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21LowerEndpointIndex slot) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (i : Fin extra)
    (hleft_interval_strict :
      endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) <
        endpoints (gn21Lemma5GapUpperIndex i))
    (hgap_strict :
      endpoints (gn21Lemma5GapUpperIndex i) <
        endpoints (gn21Lemma5GapLowerIndex i))
    (hright_interval_strict :
      endpoints (gn21Lemma5GapLowerIndex i) <
        endpoints (gn21UpperEndpointIndex (Fin.succ i)))
    (hleft_lower_zero :
      endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) = 0)
    (hleft_lower_right_derivative :
      ∃ derivativeValue : ℝ,
        HasDerivWithinAt
            (fun x =>
              Rhat (gn21EndpointVectorPolicy
                (gn21UpdateEndpoint endpoints
                  (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
            derivativeValue (Set.Ici 0) 0 ∧
          sameStrictSign derivativeValue
            (-response (gn21EndpointVectorPolicy endpoints) 0)) : False := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  rcases exists_real_right_neighborhood_of_ennreal_lt hgap_strict with
    ⟨leftUpperValue, leftUpperBound, hleft_upper_value,
      hleft_upper_lt_bound, hleft_upper_bound⟩
  rcases exists_real_right_neighborhood_of_ennreal_lt
      hright_interval_strict with
    ⟨rightLowerValue, rightLowerBound, hright_lower_value,
      hright_lower_lt_bound, hright_lower_bound⟩
  have hleft_upper_response_nonpos :
      response (gn21EndpointVectorPolicy endpoints) leftUpperValue ≤ 0 := by
    apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
        .strictlyQuasiConcave extra Rhat hdomain hmax
        (gn21Lemma5GapUpperIndex i) hleft_upper_value
        hleft_upper_lt_bound
    · intro j hj
      exact hleft_upper_bound.trans
        (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt i hj))
    · intro hshape
      simp at hshape
    · intro hshape
      simp at hshape
    · exact hupper_derivative i hleft_upper_value
  have hright_lower_response_nonneg :
      0 ≤ response (gn21EndpointVectorPolicy endpoints) rightLowerValue := by
    have hderivative_nonpos :
        -response (gn21EndpointVectorPolicy endpoints) rightLowerValue ≤ 0 := by
      apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
          .strictlyQuasiConcave extra Rhat hdomain hmax
          (gn21Lemma5GapLowerIndex i) hright_lower_value
          hright_lower_lt_bound
      · intro j hj
        exact hright_lower_bound.trans
          (hordered (by
            apply Fin.mk_le_mk.2
            change 2 * i.1 + 3 ≤ j.1
            have hj' : 2 * i.1 + 2 < j.1 := by
              simpa [gn21Lemma5GapLowerIndex] using hj
            omega))
      · intro hshape
        simp at hshape
      · intro hshape
        simp at hshape
      · simpa [gn21Lemma5GapLowerIndex, gn21LowerEndpointIndex] using
          (hlower_derivative (Fin.succ i) hright_lower_value)
    linarith
  have hleft_upper_endpoint_pos :
      0 < endpoints (gn21Lemma5GapUpperIndex i) := by
    rw [← hleft_lower_zero]
    exact hleft_interval_strict
  rcases exists_pos_real_of_zero_lt_ennreal hleft_upper_endpoint_pos with
    ⟨moveBound, hmoveBound_pos, hmoveBound_upper⟩
  have hleft_lower_feasible : ∀ x ∈ Set.Icc (0 : ℝ) moveBound,
      gn21UpdateEndpoint endpoints
          (gn21LowerEndpointIndex (Fin.castSucc i)) x ∈
        gn21Lemma5EndpointDomain .strictlyQuasiConcave extra := by
    intro x hx
    apply gn21UpdateEndpoint_mem_lemma5EndpointDomain
        .strictlyQuasiConcave extra hdomain
        (gn21LowerEndpointIndex (Fin.castSucc i)) x
    · intro j hj
      calc
        endpoints j ≤
            endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) :=
          hordered (le_of_lt hj)
        _ = 0 := hleft_lower_zero
        _ ≤ ENNReal.ofReal x := bot_le
    · intro j hj
      calc
        ENNReal.ofReal x ≤ ENNReal.ofReal moveBound :=
          ENNReal.ofReal_mono hx.2
        _ ≤ endpoints (gn21Lemma5GapUpperIndex i) := hmoveBound_upper
        _ ≤ endpoints j := hordered (by
          apply Fin.mk_le_mk.2
          change 2 * i.1 + 1 ≤ j.1
          have hj' : 2 * i.1 < j.1 := by
            simpa [gn21LowerEndpointIndex] using hj
          omega)
    · intro hshape
      simp at hshape
    · intro hshape
      simp at hshape
  have hleft_lower_derivative_nonpos :
      -response (gn21EndpointVectorPolicy endpoints) 0 ≤ 0 := by
    exact endpoint_right_response_nonpos_of_lemma5EndpointDomain_maximum
      .strictlyQuasiConcave extra Rhat hdomain hmax
      (gn21LowerEndpointIndex (Fin.castSucc i)) hleft_lower_zero
      moveBound hmoveBound_pos hleft_lower_feasible
      (-response (gn21EndpointVectorPolicy endpoints) 0)
      hleft_lower_right_derivative
  have hleft_lower_response_nonneg :
      0 ≤ response (gn21EndpointVectorPolicy endpoints) 0 := by
    linarith
  have hleft_upper_value_pos : 0 < leftUpperValue := by
    rw [hleft_lower_zero, hleft_upper_value, ENNReal.ofReal_pos] at hleft_interval_strict
    exact hleft_interval_strict
  have hleft_upper_lt_rightLower : leftUpperValue < rightLowerValue := by
    rw [hleft_upper_value, hright_lower_value] at hgap_strict
    exact ((ENNReal.ofReal_lt_ofReal_iff').mp hgap_strict).1
  have hmiddle_response_pos :
      0 < response (gn21EndpointVectorPolicy endpoints) leftUpperValue := by
    have hmin_nonneg : 0 ≤
        min (response (gn21EndpointVectorPolicy endpoints) 0)
          (response (gn21EndpointVectorPolicy endpoints) rightLowerValue) :=
      le_min hleft_lower_response_nonneg hright_lower_response_nonneg
    exact lt_of_le_of_lt hmin_nonneg
      (hzero_quasiConcave hleft_upper_value_pos hleft_upper_lt_rightLower)
  linarith

/-- A reduced strictly-quasi-concave endpoint maximizer has one interval slot. -/
theorem quasiConcave_compressionReduced_extra_eq_zero
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyQuasiConcave extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyQuasiConcave extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hreduced :
      gn21Lemma5CompressionReduced .strictlyQuasiConcave extra endpoints)
    (hresponse_quasiConcave :
      strictQuasiConcaveOnPositive
        (response (gn21EndpointVectorPolicy endpoints)))
    (hzero_quasiConcave : ∀ {middle right : ℝ},
      0 < middle → middle < right →
        min (response (gn21EndpointVectorPolicy endpoints) 0)
            (response (gn21EndpointVectorPolicy endpoints) right) <
          response (gn21EndpointVectorPolicy endpoints) middle)
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (slot : Fin (extra + 1)) {value : ℝ},
        endpoints (gn21LowerEndpointIndex slot) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21LowerEndpointIndex slot) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (hleft_lower_right_derivative :
      ∀ (i : Fin extra),
        endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (-response (gn21EndpointVectorPolicy endpoints) 0)) :
    extra = 0 := by
  cases extra with
  | zero => rfl
  | succ extra =>
      exfalso
      let i : Fin (extra + 1) := 0
      have hordered := gn21Lemma5EndpointDomain_ordered hdomain
      have hleft_removable :
          ¬ gn21Lemma5IrreducibleIntervalSlot .strictlyQuasiConcave
            (extra + 1) (Fin.castSucc i) := by
        simp [gn21Lemma5IrreducibleIntervalSlot]
      have hright_removable :
          ¬ gn21Lemma5IrreducibleIntervalSlot .strictlyQuasiConcave
            (extra + 1) (Fin.succ i) := by
        simp [gn21Lemma5IrreducibleIntervalSlot]
      have hleft_interval_strict :
          endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) <
            endpoints (gn21Lemma5GapUpperIndex i) := by
        simpa [gn21Lemma5GapUpperIndex] using
          gn21Lemma5CompressionReduced_interval_strict
            .strictlyQuasiConcave (extra + 1) hordered hreduced
            (Fin.castSucc i) hleft_removable
      have hright_interval_strict :
          endpoints (gn21Lemma5GapLowerIndex i) <
            endpoints (gn21UpperEndpointIndex (Fin.succ i)) := by
        simpa [gn21Lemma5GapLowerIndex, gn21LowerEndpointIndex] using
          gn21Lemma5CompressionReduced_interval_strict
            .strictlyQuasiConcave (extra + 1) hordered hreduced
            (Fin.succ i) hright_removable
      have hgap_strict :
          endpoints (gn21Lemma5GapUpperIndex i) <
            endpoints (gn21Lemma5GapLowerIndex i) := hreduced.2 i
      rcases eq_zero_or_pos
          (endpoints (gn21LowerEndpointIndex (Fin.castSucc i))) with
        hleft_lower_zero | hleft_lower_pos
      · exact quasiConcave_endpoint_maximum_not_strict_at_zero_pair
          (extra + 1) Rhat response hdomain hmax hzero_quasiConcave
          hupper_derivative hlower_derivative i hleft_interval_strict
          hgap_strict hright_interval_strict hleft_lower_zero
          (hleft_lower_right_derivative i hleft_lower_zero)
      · exact quasiConcave_endpoint_maximum_not_strict_at_positive_pair
          (extra + 1) Rhat response hdomain hmax hresponse_quasiConcave
          hupper_derivative hlower_derivative i hleft_interval_strict
          hgap_strict hright_interval_strict hleft_lower_pos

/--
A strictly quasi-convex response excludes three fully separated positive
intervals at an endpoint-domain maximizer.  The two outer endpoint conditions
make their responses nonpositive; strict quasi-convexity then makes the middle
lower response negative, while its own right-move maximum condition makes it
nonnegative.
-/
theorem quasiConvex_endpoint_maximum_not_strict_at_positive_triple
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyQuasiConvex extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyQuasiConvex extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_quasiConvex :
      strictQuasiConvexOnPositive
        (response (gn21EndpointVectorPolicy endpoints)))
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapLowerIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapLowerIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (i j : Fin extra) (hij : j.1 = i.1 + 1)
    (hleft_gap_strict :
      endpoints (gn21Lemma5GapUpperIndex i) <
        endpoints (gn21Lemma5GapLowerIndex i))
    (hmiddle_interval_strict :
      endpoints (gn21Lemma5GapLowerIndex i) <
        endpoints (gn21Lemma5GapUpperIndex j))
    (hright_gap_strict :
      endpoints (gn21Lemma5GapUpperIndex j) <
        endpoints (gn21Lemma5GapLowerIndex j))
    (hright_interval_strict :
      endpoints (gn21Lemma5GapLowerIndex j) <
        endpoints (gn21UpperEndpointIndex (Fin.succ j)))
    (hleft_upper_pos :
      0 < endpoints (gn21Lemma5GapUpperIndex i)) : False := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  have hleft_upper_middle_lower := hleft_gap_strict
  have hmiddle_lower_upper := hmiddle_interval_strict
  have hmiddle_upper_right_lower := hright_gap_strict
  have hright_lower_upper := hright_interval_strict
  rcases exists_real_right_neighborhood_of_ennreal_lt
      hleft_upper_middle_lower with
    ⟨leftUpperValue, leftUpperBound, hleft_upper_value,
      hleft_upper_lt_bound, hleft_upper_bound⟩
  rcases exists_real_right_neighborhood_of_ennreal_lt hmiddle_lower_upper with
    ⟨middleLowerValue, middleLowerBound, hmiddle_lower_value,
      hmiddle_lower_lt_bound, hmiddle_lower_bound⟩
  rcases exists_real_right_neighborhood_of_ennreal_lt
      hmiddle_upper_right_lower with
    ⟨middleUpperValue, middleUpperBound, hmiddle_upper_value,
      hmiddle_upper_lt_bound, hmiddle_upper_bound⟩
  rcases exists_real_right_neighborhood_of_ennreal_lt hright_lower_upper with
    ⟨rightLowerValue, rightLowerBound, hright_lower_value,
      hright_lower_lt_bound, hright_lower_bound⟩
  have hmiddle_upper_lt_rightLower : middleUpperValue < rightLowerValue := by
    rw [hmiddle_upper_value, hright_lower_value] at hmiddle_upper_right_lower
    exact ((ENNReal.ofReal_lt_ofReal_iff').mp
      hmiddle_upper_right_lower).1
  have hleft_response_nonpos :
      response (gn21EndpointVectorPolicy endpoints) leftUpperValue ≤ 0 := by
    apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
        .strictlyQuasiConvex extra Rhat hdomain hmax
        (gn21Lemma5GapUpperIndex i) hleft_upper_value
        hleft_upper_lt_bound
    · intro k hk
      exact hleft_upper_bound.trans
        (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt i hk))
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_first i
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_last i
    · exact hupper_derivative i hleft_upper_value
  have hmiddle_response_nonneg :
      0 ≤ response (gn21EndpointVectorPolicy endpoints) middleLowerValue := by
    have hderivative_nonpos :
        -response (gn21EndpointVectorPolicy endpoints) middleLowerValue ≤ 0 := by
      apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
          .strictlyQuasiConvex extra Rhat hdomain hmax
          (gn21Lemma5GapLowerIndex i) hmiddle_lower_value
          hmiddle_lower_lt_bound
      · intro k hk
        exact hmiddle_lower_bound.trans
          (hordered (by
            apply Fin.mk_le_mk.2
            change 2 * j.1 + 1 ≤ k.1
            have hk' : 2 * i.1 + 2 < k.1 := by
              simpa [gn21Lemma5GapLowerIndex] using hk
            omega))
      · intro _
        exact gn21Lemma5GapLowerIndex_ne_first i
      · intro _ hlast
        have hval := congrArg Fin.val hlast
        simp [gn21Lemma5GapLowerIndex,
          gn21Lemma5LastEndpointIndex] at hval
        omega
      · exact hlower_derivative i hmiddle_lower_value
    linarith
  have hright_response_nonpos :
      response (gn21EndpointVectorPolicy endpoints) rightLowerValue ≤ 0 := by
    have hderivative_nonneg :
        0 ≤ -response (gn21EndpointVectorPolicy endpoints) rightLowerValue := by
      apply endpoint_response_nonneg_of_lemma5EndpointDomain_maximum
          .strictlyQuasiConvex extra Rhat hdomain hmax
          (gn21Lemma5GapLowerIndex j) hright_lower_value
          hmiddle_upper_lt_rightLower
      · intro k hk
        calc
          endpoints k ≤ endpoints (gn21Lemma5GapUpperIndex j) :=
            hordered (by
              apply Fin.mk_le_mk.2
              change k.1 ≤ 2 * j.1 + 1
              have hk' : k.1 < 2 * j.1 + 2 := by
                simpa [gn21Lemma5GapLowerIndex] using hk
              omega)
          _ = ENNReal.ofReal middleUpperValue := hmiddle_upper_value
      · intro _
        exact gn21Lemma5GapLowerIndex_ne_first j
      · intro _ hlast
        have hval := congrArg Fin.val hlast
        simp [gn21Lemma5GapLowerIndex,
          gn21Lemma5LastEndpointIndex] at hval
        omega
      · exact hlower_derivative j hright_lower_value
    linarith
  have hleft_upper_value_pos : 0 < leftUpperValue := by
    rw [hleft_upper_value, ENNReal.ofReal_pos] at hleft_upper_pos
    exact hleft_upper_pos
  have hleft_upper_lt_middleLower : leftUpperValue < middleLowerValue := by
    rw [hleft_upper_value, hmiddle_lower_value] at hleft_upper_middle_lower
    exact ((ENNReal.ofReal_lt_ofReal_iff').mp
      hleft_upper_middle_lower).1
  have hmiddle_lower_lt_middleUpper : middleLowerValue < middleUpperValue := by
    rw [hmiddle_lower_value, hmiddle_upper_value] at hmiddle_lower_upper
    exact ((ENNReal.ofReal_lt_ofReal_iff').mp hmiddle_lower_upper).1
  have hmiddle_signs :=
    lemma5_strictQuasiConvex_middle_endpoint_signs_of_outer_nonpos
      (response (gn21EndpointVectorPolicy endpoints))
      hresponse_quasiConvex hleft_upper_value_pos
      hleft_upper_lt_middleLower hmiddle_lower_lt_middleUpper
      hmiddle_upper_lt_rightLower hleft_response_nonpos
      hright_response_nonpos
  linarith [hmiddle_signs.1]

/--
Quasi-convex triple exclusion using a finite nonpositive-response witness to
the right.  This formulation also covers a collapsed right tail at infinity,
without assigning a derivative to `∞`.
-/
theorem quasiConvex_endpoint_maximum_not_triple_of_right_witness
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyQuasiConvex extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyQuasiConvex extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_quasiConvex :
      strictQuasiConvexOnPositive
        (response (gn21EndpointVectorPolicy endpoints)))
    (hzero_quasiConvex : ∀ {middleLower middleUpper right : ℝ},
      0 < middleLower → middleLower < middleUpper →
        middleUpper < right →
          response (gn21EndpointVectorPolicy endpoints) middleLower <
            max (response (gn21EndpointVectorPolicy endpoints) 0)
              (response (gn21EndpointVectorPolicy endpoints) right))
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapLowerIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapLowerIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (i j : Fin extra) (hij : j.1 = i.1 + 1)
    (hleft_gap_strict :
      endpoints (gn21Lemma5GapUpperIndex i) <
        endpoints (gn21Lemma5GapLowerIndex i))
    (hmiddle_interval_strict :
      endpoints (gn21Lemma5GapLowerIndex i) <
        endpoints (gn21Lemma5GapUpperIndex j))
    (hright_gap_strict :
      endpoints (gn21Lemma5GapUpperIndex j) <
        endpoints (gn21Lemma5GapLowerIndex j))
    (rightValue : ℝ)
    (hright_of_middle :
      endpoints (gn21Lemma5GapUpperIndex j) <
        ENNReal.ofReal rightValue)
    (hright_response_nonpos :
      response (gn21EndpointVectorPolicy endpoints) rightValue ≤ 0)
    (hleft_upper_right_derivative :
      endpoints (gn21Lemma5GapUpperIndex i) = 0 →
        ∃ derivativeValue : ℝ,
          HasDerivWithinAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue (Set.Ici 0) 0 ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) 0)) : False := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  rcases exists_real_right_neighborhood_of_ennreal_lt
      hmiddle_interval_strict with
    ⟨middleLowerValue, middleLowerBound, hmiddle_lower_value,
      hmiddle_lower_lt_bound, hmiddle_lower_bound⟩
  rcases exists_real_right_neighborhood_of_ennreal_lt hright_gap_strict with
    ⟨middleUpperValue, middleUpperBound, hmiddle_upper_value,
      hmiddle_upper_lt_bound, hmiddle_upper_bound⟩
  have hmiddle_response_nonneg :
      0 ≤ response (gn21EndpointVectorPolicy endpoints) middleLowerValue := by
    have hderivative_nonpos :
        -response (gn21EndpointVectorPolicy endpoints) middleLowerValue ≤ 0 := by
      apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
          .strictlyQuasiConvex extra Rhat hdomain hmax
          (gn21Lemma5GapLowerIndex i) hmiddle_lower_value
          hmiddle_lower_lt_bound
      · intro k hk
        exact hmiddle_lower_bound.trans
          (hordered (by
            apply Fin.mk_le_mk.2
            change 2 * j.1 + 1 ≤ k.1
            have hk' : 2 * i.1 + 2 < k.1 := by
              simpa [gn21Lemma5GapLowerIndex] using hk
            omega))
      · intro _
        exact gn21Lemma5GapLowerIndex_ne_first i
      · intro _ hlast
        have hval := congrArg Fin.val hlast
        simp [gn21Lemma5GapLowerIndex,
          gn21Lemma5LastEndpointIndex] at hval
        omega
      · exact hlower_derivative i hmiddle_lower_value
    linarith
  have hmiddle_lower_value_pos : 0 < middleLowerValue := by
    have hmiddle_lower_endpoint_pos :
        0 < endpoints (gn21Lemma5GapLowerIndex i) :=
      lt_of_le_of_lt bot_le hleft_gap_strict
    rw [hmiddle_lower_value, ENNReal.ofReal_pos] at hmiddle_lower_endpoint_pos
    exact hmiddle_lower_endpoint_pos
  have hmiddle_lower_lt_middleUpper :
      middleLowerValue < middleUpperValue := by
    rw [hmiddle_lower_value, hmiddle_upper_value] at hmiddle_interval_strict
    exact ((ENNReal.ofReal_lt_ofReal_iff').mp hmiddle_interval_strict).1
  have hmiddle_upper_lt_right : middleUpperValue < rightValue := by
    rw [hmiddle_upper_value] at hright_of_middle
    exact ((ENNReal.ofReal_lt_ofReal_iff').mp hright_of_middle).1
  rcases eq_zero_or_pos
      (endpoints (gn21Lemma5GapUpperIndex i)) with
    hleft_zero | hleft_pos
  · have hmiddle_lower_endpoint_pos :
        0 < endpoints (gn21Lemma5GapLowerIndex i) := by
      rw [← hleft_zero]
      exact hleft_gap_strict
    rcases exists_pos_real_of_zero_lt_ennreal hmiddle_lower_endpoint_pos with
      ⟨moveBound, hmoveBound_pos, hmoveBound_middle⟩
    have hleft_feasible : ∀ x ∈ Set.Icc (0 : ℝ) moveBound,
        gn21UpdateEndpoint endpoints (gn21Lemma5GapUpperIndex i) x ∈
          gn21Lemma5EndpointDomain .strictlyQuasiConvex extra := by
      intro x hx
      apply gn21UpdateEndpoint_mem_lemma5EndpointDomain
          .strictlyQuasiConvex extra hdomain
          (gn21Lemma5GapUpperIndex i) x
      · intro k hk
        calc
          endpoints k ≤ endpoints (gn21Lemma5GapUpperIndex i) :=
            hordered (le_of_lt hk)
          _ = 0 := hleft_zero
          _ ≤ ENNReal.ofReal x := bot_le
      · intro k hk
        exact (ENNReal.ofReal_mono hx.2).trans
          (hmoveBound_middle.trans
            (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt i hk)))
      · intro _
        exact gn21Lemma5GapUpperIndex_ne_first i
      · intro _
        exact gn21Lemma5GapUpperIndex_ne_last i
    have hleft_response_nonpos :
        response (gn21EndpointVectorPolicy endpoints) 0 ≤ 0 := by
      exact endpoint_right_response_nonpos_of_lemma5EndpointDomain_maximum
        .strictlyQuasiConvex extra Rhat hdomain hmax
        (gn21Lemma5GapUpperIndex i) hleft_zero
        moveBound hmoveBound_pos hleft_feasible
        (response (gn21EndpointVectorPolicy endpoints) 0)
        (hleft_upper_right_derivative hleft_zero)
    have hmiddle_response_neg :
        response (gn21EndpointVectorPolicy endpoints) middleLowerValue < 0 := by
      exact lt_of_lt_of_le
        (hzero_quasiConvex hmiddle_lower_value_pos
          hmiddle_lower_lt_middleUpper hmiddle_upper_lt_right)
        (max_le hleft_response_nonpos hright_response_nonpos)
    linarith
  · rcases exists_real_right_neighborhood_of_ennreal_lt
        hleft_gap_strict with
      ⟨leftUpperValue, leftUpperBound, hleft_upper_value,
        hleft_upper_lt_bound, hleft_upper_bound⟩
    have hleft_response_nonpos :
        response (gn21EndpointVectorPolicy endpoints) leftUpperValue ≤ 0 := by
      apply endpoint_response_nonpos_of_lemma5EndpointDomain_maximum
          .strictlyQuasiConvex extra Rhat hdomain hmax
          (gn21Lemma5GapUpperIndex i) hleft_upper_value
          hleft_upper_lt_bound
      · intro k hk
        exact hleft_upper_bound.trans
          (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt i hk))
      · intro _
        exact gn21Lemma5GapUpperIndex_ne_first i
      · intro _
        exact gn21Lemma5GapUpperIndex_ne_last i
      · exact hupper_derivative i hleft_upper_value
    have hleft_upper_value_pos : 0 < leftUpperValue := by
      rw [hleft_upper_value, ENNReal.ofReal_pos] at hleft_pos
      exact hleft_pos
    have hleft_upper_lt_middleLower :
        leftUpperValue < middleLowerValue := by
      rw [hleft_upper_value, hmiddle_lower_value] at hleft_gap_strict
      exact ((ENNReal.ofReal_lt_ofReal_iff').mp hleft_gap_strict).1
    have hmiddle_signs :=
      lemma5_strictQuasiConvex_middle_endpoint_signs_of_outer_nonpos
        (response (gn21EndpointVectorPolicy endpoints))
        hresponse_quasiConvex hleft_upper_value_pos
        hleft_upper_lt_middleLower hmiddle_lower_lt_middleUpper
        hmiddle_upper_lt_right hleft_response_nonpos
        hright_response_nonpos
    linarith [hmiddle_signs.1]

/-- A reduced strictly-quasi-convex endpoint maximizer has at most two slots. -/
theorem quasiConvex_compressionReduced_extra_le_one
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyQuasiConvex extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyQuasiConvex extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hreduced :
      gn21Lemma5CompressionReduced .strictlyQuasiConvex extra endpoints)
    (hresponse_quasiConvex :
      strictQuasiConvexOnPositive
        (response (gn21EndpointVectorPolicy endpoints)))
    (hzero_quasiConvex : ∀ {middleLower middleUpper right : ℝ},
      0 < middleLower → middleLower < middleUpper →
        middleUpper < right →
          response (gn21EndpointVectorPolicy endpoints) middleLower <
            max (response (gn21EndpointVectorPolicy endpoints) 0)
              (response (gn21EndpointVectorPolicy endpoints) right))
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapLowerIndex i) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapLowerIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (hleft_upper_right_derivative :
      ∀ (i : Fin extra),
        endpoints (gn21Lemma5GapUpperIndex i) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21Lemma5GapUpperIndex i) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (response (gn21EndpointVectorPolicy endpoints) 0))
    (hright_top_witness : ∀ (j : Fin extra),
      endpoints (gn21Lemma5GapLowerIndex j) = ∞ →
        ∃ rightValue : ℝ,
          endpoints (gn21Lemma5GapUpperIndex j) <
              ENNReal.ofReal rightValue ∧
            response (gn21EndpointVectorPolicy endpoints) rightValue ≤ 0) :
    extra ≤ 1 := by
  cases extra with
  | zero => omega
  | succ extra =>
      cases extra with
      | zero => omega
      | succ extra =>
          exfalso
          let i : Fin (extra + 2) := 0
          let j : Fin (extra + 2) := ⟨1, by omega⟩
          have hij : j.1 = i.1 + 1 := by rfl
          have hordered := gn21Lemma5EndpointDomain_ordered hdomain
          have hmiddle_removable :
              ¬ gn21Lemma5IrreducibleIntervalSlot .strictlyQuasiConvex
                (extra + 2) (Fin.succ i) := by
            intro hirreducible
            rcases hirreducible with hzero | hfirst | hlast
            · omega
            · exact Fin.succ_ne_zero i hfirst.2
            · have hval := congrArg Fin.val hlast.2
              simp [i] at hval
          have hmiddle_interval_strict :
              endpoints (gn21Lemma5GapLowerIndex i) <
                endpoints (gn21Lemma5GapUpperIndex j) := by
            simpa [gn21Lemma5GapLowerIndex, gn21Lemma5GapUpperIndex,
              gn21LowerEndpointIndex, gn21UpperEndpointIndex, hij] using
              gn21Lemma5CompressionReduced_interval_strict
                .strictlyQuasiConvex (extra + 2) hordered hreduced
                (Fin.succ i) hmiddle_removable
          have hleft_gap_strict :
              endpoints (gn21Lemma5GapUpperIndex i) <
                endpoints (gn21Lemma5GapLowerIndex i) := hreduced.2 i
          have hright_gap_strict :
              endpoints (gn21Lemma5GapUpperIndex j) <
                endpoints (gn21Lemma5GapLowerIndex j) := hreduced.2 j
          obtain ⟨rightValue, hright_of_middle,
              hright_response_nonpos⟩ :
              ∃ rightValue : ℝ,
                endpoints (gn21Lemma5GapUpperIndex j) <
                    ENNReal.ofReal rightValue ∧
                  response (gn21EndpointVectorPolicy endpoints) rightValue ≤ 0 := by
            by_cases hright_top :
                endpoints (gn21Lemma5GapLowerIndex j) = ∞
            · exact hright_top_witness j hright_top
            · rcases exists_real_left_neighborhood_of_ennreal_lt
                  hright_gap_strict hright_top with
                ⟨lowerBound, rightValue, hmiddle_upper_bound,
                  hlower_right, hright_value⟩
              have hmiddle_upper_lt_right :
                  endpoints (gn21Lemma5GapUpperIndex j) <
                    ENNReal.ofReal rightValue := by
                rw [← hright_value]
                exact hright_gap_strict
              have hright_response_nonpos :
                  response (gn21EndpointVectorPolicy endpoints) rightValue ≤ 0 := by
                have hderivative_nonneg :
                    0 ≤ -response
                      (gn21EndpointVectorPolicy endpoints) rightValue := by
                  apply endpoint_response_nonneg_of_lemma5EndpointDomain_maximum
                      .strictlyQuasiConvex (extra + 2) Rhat hdomain hmax
                      (gn21Lemma5GapLowerIndex j) hright_value hlower_right
                  · intro k hk
                    exact (hordered (by
                      apply Fin.mk_le_mk.2
                      change k.1 ≤ 2 * j.1 + 1
                      have hk' : k.1 < 2 * j.1 + 2 := by
                        simpa [gn21Lemma5GapLowerIndex] using hk
                      omega)).trans hmiddle_upper_bound
                  · intro _
                    exact gn21Lemma5GapLowerIndex_ne_first j
                  · intro _ hlast
                    have hval := congrArg Fin.val hlast
                    simp [gn21Lemma5GapLowerIndex,
                      gn21Lemma5LastEndpointIndex] at hval
                    omega
                  · exact hlower_derivative j hright_value
                linarith
              exact ⟨rightValue, hmiddle_upper_lt_right,
                hright_response_nonpos⟩
          exact quasiConvex_endpoint_maximum_not_triple_of_right_witness
            (extra + 2) Rhat response hdomain hmax hresponse_quasiConvex
            hzero_quasiConvex hupper_derivative hlower_derivative
            i j hij hleft_gap_strict hmiddle_interval_strict
            hright_gap_strict rightValue hright_of_middle
            hright_response_nonpos
            (hleft_upper_right_derivative i)

/-! ## Compact canonical endpoint families -/

/-- A one-slot endpoint vector represents one extended open interval. -/
theorem gn21EndpointVectorPolicy_one
    (endpoints : GN21EndpointVector 1) :
    gn21EndpointVectorPolicy endpoints =
      gn21ExtendedMiddlePolicy (endpoints 0) (endpoints 1) := by
  ext τ
  simp [gn21EndpointVectorPolicy, gn21LowerEndpointIndex,
    gn21UpperEndpointIndex]

/-- A two-slot endpoint vector represents the union of its two extended intervals. -/
theorem gn21EndpointVectorPolicy_two
    (endpoints : GN21EndpointVector 2) :
    gn21EndpointVectorPolicy endpoints =
      gn21ExtendedMiddlePolicy (endpoints 0) (endpoints 1) ∪
        gn21ExtendedMiddlePolicy (endpoints 2) (endpoints 3) := by
  ext τ
  simp [gn21EndpointVectorPolicy, gn21LowerEndpointIndex,
    gn21UpperEndpointIndex]

/-- The quasi-convex source form needs two interval slots; every other form needs one. -/
def gn21Lemma5CanonicalExtra : Lemma5DerivativeShape → Nat
  | .strictlyQuasiConvex => 1
  | _ => 0

/-- Compact endpoint domain containing exactly the syntactic source family for a shape. -/
def gn21Lemma5CanonicalEndpointDomain (shape : Lemma5DerivativeShape) :=
  gn21Lemma5EndpointDomain shape (gn21Lemma5CanonicalExtra shape)

theorem isCompact_gn21Lemma5CanonicalEndpointDomain
    (shape : Lemma5DerivativeShape) :
    IsCompact (gn21Lemma5CanonicalEndpointDomain shape) :=
  isCompact_gn21Lemma5EndpointDomain shape
    (gn21Lemma5CanonicalExtra shape)

theorem gn21Lemma5CanonicalEndpointDomain_nonempty
    (shape : Lemma5DerivativeShape) :
    (gn21Lemma5CanonicalEndpointDomain shape).Nonempty :=
  gn21Lemma5EndpointDomain_nonempty shape
    (gn21Lemma5CanonicalExtra shape)

/--
Members of the compact canonical endpoint domain have exactly the endpoint-
complete source form.  The increasing family has one additional condition:
its lower endpoint must be finite, because the printed increasing branch does
not include the empty-policy cutoff at infinity.
-/
theorem lemma5SourcePolicyForm_of_mem_canonicalEndpointDomain
    (shape : Lemma5DerivativeShape)
    (endpoints :
      GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra shape))
    (hdomain : endpoints ∈ gn21Lemma5CanonicalEndpointDomain shape)
    (hincreasing_finite :
      shape = .strictlyIncreasing →
        endpoints
          (gn21Lemma5FirstEndpointIndex
            (gn21Lemma5CanonicalExtra shape)) ≠ ∞) :
    lemma5SourcePolicyForm shape
      (gn21EndpointVectorPolicy endpoints) := by
  cases shape with
  | positive =>
      change GN21EndpointVector 1 at endpoints
      change endpoints ∈ gn21Lemma5EndpointDomain .positive 0 at hdomain
      rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
      change endpoints 0 = 0 at hfirst
      change endpoints 1 = ∞ at hlast
      change gn21EndpointVectorPolicy (n := 1) endpoints = acceptAllPolicy
      rw [gn21EndpointVectorPolicy_one]
      rw [hfirst, hlast]
      exact gn21ExtendedMiddlePolicy_zero_top
  | strictlyIncreasing =>
      change GN21EndpointVector 1 at endpoints
      change endpoints ∈
        gn21Lemma5EndpointDomain .strictlyIncreasing 0 at hdomain
      rcases hdomain with ⟨hordered, hlast⟩
      change endpoints 1 = ∞ at hlast
      let cutoff : NNReal := (endpoints 0).toNNReal
      refine ⟨cutoff, ?_⟩
      change gn21EndpointVectorPolicy (n := 1) endpoints =
        gn21RightExtendedCutoffPolicy (cutoff : ℝ≥0∞)
      rw [gn21EndpointVectorPolicy_one]
      have hfinite : endpoints 0 ≠ ∞ := by
        simpa [gn21Lemma5CanonicalExtra, gn21Lemma5FirstEndpointIndex] using
          hincreasing_finite rfl
      have hcutoff : (cutoff : ℝ≥0∞) = endpoints 0 := by
        exact ENNReal.coe_toNNReal hfinite
      rw [hlast, hcutoff]
      exact gn21ExtendedMiddlePolicy_top_right _
  | strictlyDecreasing =>
      change GN21EndpointVector 1 at endpoints
      change endpoints ∈
        gn21Lemma5EndpointDomain .strictlyDecreasing 0 at hdomain
      rcases hdomain with ⟨hordered, hfirst⟩
      change endpoints 0 = 0 at hfirst
      refine ⟨endpoints 1, ?_⟩
      change gn21EndpointVectorPolicy (n := 1) endpoints =
        gn21LeftExtendedCutoffPolicy (endpoints 1)
      rw [gn21EndpointVectorPolicy_one]
      rw [hfirst]
      exact gn21ExtendedMiddlePolicy_zero _
  | strictlyQuasiConvex =>
      change GN21EndpointVector 2 at endpoints
      change endpoints ∈
        gn21Lemma5EndpointDomain .strictlyQuasiConvex 1 at hdomain
      rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
      change endpoints 0 = 0 at hfirst
      change endpoints 3 = ∞ at hlast
      refine
        ⟨endpoints 1, endpoints 2, ?_⟩
      change gn21EndpointVectorPolicy (n := 2) endpoints =
        gn21ExtendedTwoTailPolicy (endpoints 1) (endpoints 2)
      rw [gn21EndpointVectorPolicy_two]
      rw [hfirst, hlast]
      rw [gn21ExtendedMiddlePolicy_zero,
        gn21ExtendedMiddlePolicy_top_right]
      rfl
  | strictlyQuasiConcave =>
      change GN21EndpointVector 1 at endpoints
      refine ⟨endpoints 0, endpoints 1, ?_⟩
      change gn21EndpointVectorPolicy (n := 1) endpoints =
        gn21ExtendedMiddlePolicy (endpoints 0) (endpoints 1)
      exact gn21EndpointVectorPolicy_one endpoints

/-- Every endpoint-complete source form is represented in its compact canonical family. -/
theorem exists_canonicalEndpointVector_of_lemma5SourcePolicyForm
    {shape : Lemma5DerivativeShape} {policy : TripPolicy}
    (hform : lemma5SourcePolicyForm shape policy) :
    ∃ endpoints ∈ gn21Lemma5CanonicalEndpointDomain shape,
      gn21EndpointVectorPolicy endpoints = policy := by
  cases shape with
  | positive =>
      change policy = acceptAllPolicy at hform
      let endpoints : GN21Lemma5EndpointVector 0 := ![0, ∞]
      have hordered : endpoints ∈ gn21OrderedEndpointVectors 1 := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [endpoints]
      refine ⟨endpoints, ?_, ?_⟩
      · change endpoints ∈ gn21Lemma5EndpointDomain .positive 0
        refine ⟨⟨hordered, ?_⟩, ?_⟩
        · change endpoints 0 = 0
          simp [endpoints]
        · change endpoints 1 = ∞
          simp [endpoints]
      · change gn21EndpointVectorPolicy (n := 1) endpoints = policy
        rw [hform, gn21EndpointVectorPolicy_one]
        simp [endpoints]
  | strictlyIncreasing =>
      rcases hform with ⟨cutoff, rfl⟩
      let endpoints : GN21Lemma5EndpointVector 0 :=
        ![(cutoff : ℝ≥0∞), ∞]
      have hordered : endpoints ∈ gn21OrderedEndpointVectors 1 := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [endpoints]
      refine ⟨endpoints, ?_, ?_⟩
      · change endpoints ∈
          gn21Lemma5EndpointDomain .strictlyIncreasing 0
        refine ⟨hordered, ?_⟩
        change endpoints 1 = ∞
        simp [endpoints]
      · change gn21EndpointVectorPolicy (n := 1) endpoints =
          gn21RightExtendedCutoffPolicy (cutoff : ℝ≥0∞)
        rw [gn21EndpointVectorPolicy_one]
        simp [endpoints]
  | strictlyDecreasing =>
      rcases hform with ⟨cutoff, rfl⟩
      let endpoints : GN21Lemma5EndpointVector 0 := ![0, cutoff]
      have hordered : endpoints ∈ gn21OrderedEndpointVectors 1 := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [endpoints]
      refine ⟨endpoints, ?_, ?_⟩
      · change endpoints ∈
          gn21Lemma5EndpointDomain .strictlyDecreasing 0
        refine ⟨hordered, ?_⟩
        change endpoints 0 = 0
        simp [endpoints]
      · change gn21EndpointVectorPolicy (n := 1) endpoints =
          gn21LeftExtendedCutoffPolicy cutoff
        rw [gn21EndpointVectorPolicy_one]
        simp [endpoints]
  | strictlyQuasiConvex =>
      rcases hform with ⟨lower, upper, rfl⟩
      by_cases hlower_upper : lower ≤ upper
      · let endpoints : GN21Lemma5EndpointVector 1 :=
          ![0, lower, upper, ∞]
        have hordered : endpoints ∈ gn21OrderedEndpointVectors 2 := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all [endpoints]
        refine ⟨endpoints, ?_, ?_⟩
        · change endpoints ∈
            gn21Lemma5EndpointDomain .strictlyQuasiConvex 1
          refine ⟨⟨hordered, ?_⟩, ?_⟩
          · change endpoints 0 = 0
            simp [endpoints]
          · change endpoints 3 = ∞
            simp [endpoints]
        · change gn21EndpointVectorPolicy (n := 2) endpoints =
            gn21ExtendedTwoTailPolicy lower upper
          rw [gn21EndpointVectorPolicy_two]
          simp [endpoints, gn21ExtendedTwoTailPolicy]
      · have hupper_lower : upper < lower := lt_of_not_ge hlower_upper
        let endpoints : GN21Lemma5EndpointVector 1 := ![0, ∞, ∞, ∞]
        have hordered : endpoints ∈ gn21OrderedEndpointVectors 2 := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all [endpoints]
        refine ⟨endpoints, ?_, ?_⟩
        · change endpoints ∈
            gn21Lemma5EndpointDomain .strictlyQuasiConvex 1
          refine ⟨⟨hordered, ?_⟩, ?_⟩
          · change endpoints 0 = 0
            simp [endpoints]
          · change endpoints 3 = ∞
            simp [endpoints]
        · calc
            gn21EndpointVectorPolicy (n := 2) endpoints = acceptAllPolicy := by
              rw [gn21EndpointVectorPolicy_two]
              simp [endpoints]
            _ = gn21ExtendedTwoTailPolicy lower upper :=
              (gn21ExtendedTwoTailPolicy_eq_acceptAll_of_lt
                hupper_lower).symm
  | strictlyQuasiConcave =>
      rcases hform with ⟨lower, upper, rfl⟩
      by_cases hlower_upper : lower ≤ upper
      · let endpoints : GN21Lemma5EndpointVector 0 := ![lower, upper]
        have hordered : endpoints ∈ gn21OrderedEndpointVectors 1 := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all [endpoints]
        refine ⟨endpoints, ?_, ?_⟩
        · change endpoints ∈
            gn21Lemma5EndpointDomain .strictlyQuasiConcave 0
          exact hordered
        change gn21EndpointVectorPolicy (n := 1) endpoints =
          gn21ExtendedMiddlePolicy lower upper
        rw [gn21EndpointVectorPolicy_one]
        simp [endpoints]
      · have hupper_lower : upper ≤ lower := le_of_not_ge hlower_upper
        let endpoints : GN21Lemma5EndpointVector 0 := ![0, 0]
        have hordered : endpoints ∈ gn21OrderedEndpointVectors 1 := by
          intro i j hij
          fin_cases i <;> fin_cases j <;> simp_all [endpoints]
        refine ⟨endpoints, ?_, ?_⟩
        · change endpoints ∈
            gn21Lemma5EndpointDomain .strictlyQuasiConcave 0
          exact hordered
        change gn21EndpointVectorPolicy (n := 1) endpoints =
          gn21ExtendedMiddlePolicy lower upper
        rw [gn21EndpointVectorPolicy_one]
        rw [show endpoints 0 = 0 by simp [endpoints],
          show endpoints 1 = 0 by simp [endpoints],
          gn21ExtendedMiddlePolicy_self,
          gn21ExtendedMiddlePolicy_eq_empty_of_le hupper_lower]

/-- A canonical endpoint maximum dominates every exact source-form policy. -/
theorem source_policy_reward_le_of_canonicalEndpointDomain_maximum
    (shape : Lemma5DerivativeShape) (Rhat : SingleStateReward)
    {canonical :
      GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra shape)}
    (hmax :
      ∀ candidate ∈ gn21Lemma5CanonicalEndpointDomain shape,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy canonical))
    {policy : TripPolicy}
    (hform : lemma5SourcePolicyForm shape policy) :
    Rhat policy ≤ Rhat (gn21EndpointVectorPolicy canonical) := by
  rcases exists_canonicalEndpointVector_of_lemma5SourcePolicyForm hform with
    ⟨candidate, hcandidate, hcandidate_policy⟩
  rw [← hcandidate_policy]
  exact hmax candidate hcandidate

/--
If exact source forms approach a policy's reward from below at every
sufficiently small tolerance, their canonical maximum weakly dominates that
policy.
-/
theorem reward_le_of_source_form_approximants
    (shape : Lemma5DerivativeShape) (Rhat : SingleStateReward)
    (sigma canonicalPolicy : TripPolicy)
    {margin rewardGap : ℝ}
    (hmargin : 0 < margin) (hrewardGap : 0 < rewardGap)
    (hcanonical :
      ∀ policy : TripPolicy, lemma5SourcePolicyForm shape policy →
        Rhat policy ≤ Rhat canonicalPolicy)
    (happroximants :
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < margin →
        epsilon < rewardGap →
          ∃ policy : TripPolicy,
            lemma5SourcePolicyForm shape policy ∧
              Rhat sigma - epsilon < Rhat policy) :
    Rhat sigma ≤ Rhat canonicalPolicy := by
  by_contra hnot
  let canonicalGap := Rhat sigma - Rhat canonicalPolicy
  have hcanonicalGap_pos : 0 < canonicalGap :=
    sub_pos.mpr (lt_of_not_ge hnot)
  let epsilon := min margin (min rewardGap canonicalGap) / 2
  have hminimum_pos :
      0 < min margin (min rewardGap canonicalGap) :=
    lt_min hmargin (lt_min hrewardGap hcanonicalGap_pos)
  have hepsilon_pos : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hminimum_le_margin :
      min margin (min rewardGap canonicalGap) ≤ margin := min_le_left _ _
  have hminimum_le_rewardGap :
      min margin (min rewardGap canonicalGap) ≤ rewardGap :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hminimum_le_canonicalGap :
      min margin (min rewardGap canonicalGap) ≤ canonicalGap :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hepsilon_margin : epsilon < margin := by
    dsimp [epsilon]
    linarith
  have hepsilon_rewardGap : epsilon < rewardGap := by
    dsimp [epsilon]
    linarith
  have hepsilon_canonicalGap : epsilon < canonicalGap := by
    dsimp [epsilon]
    linarith
  rcases happroximants epsilon hepsilon_pos hepsilon_margin
      hepsilon_rewardGap with
    ⟨policy, hform, hpolicy_lower⟩
  have hpolicy_upper := hcanonical policy hform
  linarith

/-- Continuous reward attains a maximum on the compact canonical source family. -/
theorem exists_gn21Lemma5CanonicalEndpointDomain_reward_maximum
    (shape : Lemma5DerivativeShape) (Rhat : SingleStateReward)
    (hcontinuous :
      ContinuousOn
        (fun endpoints :
          GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra shape) =>
            Rhat (gn21EndpointVectorPolicy endpoints))
        (gn21Lemma5CanonicalEndpointDomain shape)) :
    ∃ endpoints ∈ gn21Lemma5CanonicalEndpointDomain shape,
      ∀ candidate ∈ gn21Lemma5CanonicalEndpointDomain shape,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints) :=
  exists_gn21Lemma5EndpointDomain_reward_maximum
    shape (gn21Lemma5CanonicalExtra shape) Rhat hcontinuous

/--
A reward-above-empty member of the increasing canonical family forces its
maximizer to have a finite lower cutoff.  This is the precise compactification
step behind the source's `Rhat(sigma0) > Rhat(empty)` argument.
-/
theorem gn21_increasing_canonical_maximum_first_ne_top
    (Rhat : SingleStateReward)
    {endpoints : GN21Lemma5EndpointVector 0}
    (hdomain : endpoints ∈
      gn21Lemma5CanonicalEndpointDomain .strictlyIncreasing)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5CanonicalEndpointDomain .strictlyIncreasing,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hexceeds_empty :
      ∃ candidate ∈
          gn21Lemma5CanonicalEndpointDomain .strictlyIncreasing,
        Rhat ∅ < Rhat (gn21EndpointVectorPolicy candidate)) :
    endpoints (gn21Lemma5FirstEndpointIndex 0) ≠ ∞ := by
  intro htop
  rcases hexceeds_empty with ⟨candidate, hcandidate, hcandidate_gt⟩
  have hmax_candidate := hmax candidate hcandidate
  have hpolicy_empty :
      gn21EndpointVectorPolicy endpoints = (∅ : TripPolicy) := by
    rw [gn21EndpointVectorPolicy_one]
    change endpoints 0 = ∞ at htop
    rw [htop]
    exact gn21ExtendedMiddlePolicy_top _
  rw [hpolicy_empty] at hmax_candidate
  exact (not_lt_of_ge hmax_candidate) hcandidate_gt

/--
Continuous reward attains a maximum in the exact source family.  The only
noncompact-looking source branch, strictly increasing cutoffs in `R+`, uses
the visible reward-above-empty premise to exclude the adjoined infinity point.
-/
theorem exists_lemma5SourcePolicyForm_canonical_reward_maximum
    (shape : Lemma5DerivativeShape) (Rhat : SingleStateReward)
    (hcontinuous :
      ContinuousOn
        (fun endpoints :
          GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra shape) =>
            Rhat (gn21EndpointVectorPolicy endpoints))
        (gn21Lemma5CanonicalEndpointDomain shape))
    (hincreasing_exceeds_empty :
      shape = .strictlyIncreasing →
        ∃ candidate ∈ gn21Lemma5CanonicalEndpointDomain shape,
          Rhat ∅ < Rhat (gn21EndpointVectorPolicy candidate)) :
    ∃ endpoints ∈ gn21Lemma5CanonicalEndpointDomain shape,
      lemma5SourcePolicyForm shape
          (gn21EndpointVectorPolicy endpoints) ∧
        ∀ candidate ∈ gn21Lemma5CanonicalEndpointDomain shape,
          Rhat (gn21EndpointVectorPolicy candidate) ≤
            Rhat (gn21EndpointVectorPolicy endpoints) := by
  rcases exists_gn21Lemma5CanonicalEndpointDomain_reward_maximum
      shape Rhat hcontinuous with
    ⟨endpoints, hdomain, hmax⟩
  have hincreasing_finite :
      shape = .strictlyIncreasing →
        endpoints
          (gn21Lemma5FirstEndpointIndex
            (gn21Lemma5CanonicalExtra shape)) ≠ ∞ := by
    intro hshape
    subst shape
    exact gn21_increasing_canonical_maximum_first_ne_top
      Rhat hdomain hmax (hincreasing_exceeds_empty rfl)
  exact
    ⟨endpoints, hdomain,
      lemma5SourcePolicyForm_of_mem_canonicalEndpointDomain
        shape endpoints hdomain hincreasing_finite,
      hmax⟩

/-! ## Finite-family source-form assembly -/

/-- Every positive-response finite-family maximizer is accept-all modulo null endpoints. -/
theorem exists_positive_source_form_of_endpoint_maximum
    (mu : Measure TripLength) [NoAtoms mu]
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .positive extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hRhat_ae : ∀ {sigma tau : TripPolicy},
      policyAlmostEverywhereEq mu sigma tau → Rhat sigma = Rhat tau)
    (hresponse_positive :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        ∀ u : TripLength, 0 < u →
          0 < response (gn21EndpointVectorPolicy candidate) u)
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hpath_continuous :
      ∀ (i : Fin extra) (upper : ℝ), 0 < upper →
        ContinuousOn
          (fun x =>
            Rhat (gn21EndpointVectorPolicy
              (gn21UpdateEndpoint endpoints
                (gn21Lemma5GapUpperIndex i) x)))
          (Set.Icc 0 upper))
    (hpath_derivative :
      ∀ (i : Fin extra) (upper : ℝ) (x : ℝ),
        x ∈ Set.Ioo 0 upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun y =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) y)))
              derivativeValue x ∧
            sameStrictSign derivativeValue
              (response
                (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)) x)) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .positive policy ∧
        Rhat policy = Rhat (gn21EndpointVectorPolicy endpoints) := by
  rcases positive_endpoint_maximum_source_form_ae
      mu extra Rhat response hdomain hmax hresponse_positive
      hupper_derivative hpath_continuous hpath_derivative with
    ⟨policy, hform, hae⟩
  exact ⟨policy, hform, (hRhat_ae hae).symm⟩

/--
Every strictly-increasing finite endpoint-family maximizer has an equal-reward
source-form representative.  The source inequality above the empty policy
excludes the compactification point with lower cutoff `infinity`.
-/
theorem exists_strictlyIncreasing_source_form_of_endpoint_maximum
    (mu : Measure TripLength) [NoAtoms mu]
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyIncreasing extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyIncreasing extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hRhat_ae : ∀ {sigma tau : TripPolicy},
      policyAlmostEverywhereEq mu sigma tau → Rhat sigma = Rhat tau)
    (hempty_lt :
      Rhat ∅ < Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_increasing :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra),
        Rhat (gn21EndpointVectorPolicy reduced) =
            Rhat (gn21EndpointVectorPolicy endpoints) →
          StrictMonoOn (response (gn21EndpointVectorPolicy reduced))
            (Set.Ici 0))
    (hupper_derivative :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra)
        (i : Fin reducedExtra) {value : ℝ},
        reduced (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint reduced
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy reduced) value))
    (hlower_derivative :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra)
        (i : Fin reducedExtra) {value : ℝ},
        reduced (gn21LowerEndpointIndex (Fin.castSucc i)) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint reduced
                    (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy reduced) value))
    (hlower_right_derivative :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra)
        (i : Fin reducedExtra),
        reduced (gn21LowerEndpointIndex (Fin.castSucc i)) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint reduced
                      (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (-response (gn21EndpointVectorPolicy reduced) 0)) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .strictlyIncreasing policy ∧
        Rhat policy = Rhat (gn21EndpointVectorPolicy endpoints) := by
  rcases exists_gn21Lemma5CompressionReduced_maximum
      mu .strictlyIncreasing Rhat hRhat_ae extra hdomain hmax with
    ⟨reducedExtra, _hreducedExtra, reduced, hreduced_domain,
      hreduced_max, hreduced_reward, hreduced⟩
  have hreducedExtra_zero : reducedExtra = 0 :=
    increasing_compressionReduced_extra_eq_zero
      reducedExtra Rhat response hreduced_domain hreduced_max hreduced
      (hresponse_increasing reducedExtra reduced hreduced_reward)
      (hupper_derivative reducedExtra reduced)
      (hlower_derivative reducedExtra reduced)
      (hlower_right_derivative reducedExtra reduced)
  subst reducedExtra
  have hfinite :
      reduced (gn21Lemma5FirstEndpointIndex 0) ≠ ∞ := by
    apply gn21_increasing_canonical_maximum_first_ne_top
        Rhat hreduced_domain hreduced_max
    refine ⟨reduced, hreduced_domain, ?_⟩
    calc
      Rhat ∅ < Rhat (gn21EndpointVectorPolicy endpoints) := hempty_lt
      _ = Rhat (gn21EndpointVectorPolicy reduced) := hreduced_reward.symm
  refine ⟨gn21EndpointVectorPolicy reduced, ?_, hreduced_reward⟩
  exact lemma5SourcePolicyForm_of_mem_canonicalEndpointDomain
    .strictlyIncreasing reduced hreduced_domain (by
      intro _hshape
      exact hfinite)

/-- Every strictly-decreasing finite-family maximizer has an equal-reward source form. -/
theorem exists_strictlyDecreasing_source_form_of_endpoint_maximum
    (mu : Measure TripLength) [NoAtoms mu]
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyDecreasing extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyDecreasing extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hRhat_ae : ∀ {sigma tau : TripPolicy},
      policyAlmostEverywhereEq mu sigma tau → Rhat sigma = Rhat tau)
    (hresponse_decreasing :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra),
        Rhat (gn21EndpointVectorPolicy reduced) =
            Rhat (gn21EndpointVectorPolicy endpoints) →
          StrictAntiOn (response (gn21EndpointVectorPolicy reduced))
            (Set.Ici 0))
    (hupper_derivative :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra)
        (i : Fin reducedExtra) {value : ℝ},
        reduced (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint reduced
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy reduced) value))
    (hnext_lower_derivative :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra)
        (i : Fin reducedExtra) {value : ℝ},
        reduced (gn21Lemma5GapLowerIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint reduced
                    (gn21Lemma5GapLowerIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy reduced) value))
    (hupper_right_derivative :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra)
        (i : Fin reducedExtra),
        reduced (gn21Lemma5GapUpperIndex i) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint reduced
                      (gn21Lemma5GapUpperIndex i) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (response (gn21EndpointVectorPolicy reduced) 0)) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .strictlyDecreasing policy ∧
        Rhat policy = Rhat (gn21EndpointVectorPolicy endpoints) := by
  rcases exists_gn21Lemma5CompressionReduced_maximum
      mu .strictlyDecreasing Rhat hRhat_ae extra hdomain hmax with
    ⟨reducedExtra, _hreducedExtra, reduced, hreduced_domain,
      hreduced_max, hreduced_reward, hreduced⟩
  have hreducedExtra_zero : reducedExtra = 0 :=
    decreasing_compressionReduced_extra_eq_zero
      reducedExtra Rhat response hreduced_domain hreduced_max hreduced
      (hresponse_decreasing reducedExtra reduced hreduced_reward)
      (hupper_derivative reducedExtra reduced)
      (hnext_lower_derivative reducedExtra reduced)
      (hupper_right_derivative reducedExtra reduced)
  subst reducedExtra
  refine ⟨gn21EndpointVectorPolicy reduced, ?_, hreduced_reward⟩
  exact lemma5SourcePolicyForm_of_mem_canonicalEndpointDomain
    .strictlyDecreasing reduced hreduced_domain (by simp)

/-- Every strictly-quasi-concave finite-family maximizer has an equal-reward source form. -/
theorem exists_strictlyQuasiConcave_source_form_of_endpoint_maximum
    (mu : Measure TripLength) [NoAtoms mu]
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyQuasiConcave extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyQuasiConcave extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hRhat_ae : ∀ {sigma tau : TripPolicy},
      policyAlmostEverywhereEq mu sigma tau → Rhat sigma = Rhat tau)
    (hresponse_quasiConcave :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra),
        Rhat (gn21EndpointVectorPolicy reduced) =
            Rhat (gn21EndpointVectorPolicy endpoints) →
          strictQuasiConcaveOnPositive
            (response (gn21EndpointVectorPolicy reduced)))
    (hzero_quasiConcave :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra),
        Rhat (gn21EndpointVectorPolicy reduced) =
            Rhat (gn21EndpointVectorPolicy endpoints) →
          ∀ {middle right : ℝ}, 0 < middle → middle < right →
            min (response (gn21EndpointVectorPolicy reduced) 0)
                (response (gn21EndpointVectorPolicy reduced) right) <
              response (gn21EndpointVectorPolicy reduced) middle)
    (hupper_derivative :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra)
        (i : Fin reducedExtra) {value : ℝ},
        reduced (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint reduced
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy reduced) value))
    (hlower_derivative :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra)
        (slot : Fin (reducedExtra + 1)) {value : ℝ},
        reduced (gn21LowerEndpointIndex slot) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint reduced
                    (gn21LowerEndpointIndex slot) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy reduced) value))
    (hleft_lower_right_derivative :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra)
        (i : Fin reducedExtra),
        reduced (gn21LowerEndpointIndex (Fin.castSucc i)) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint reduced
                      (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (-response (gn21EndpointVectorPolicy reduced) 0)) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .strictlyQuasiConcave policy ∧
        Rhat policy = Rhat (gn21EndpointVectorPolicy endpoints) := by
  rcases exists_gn21Lemma5CompressionReduced_maximum
      mu .strictlyQuasiConcave Rhat hRhat_ae extra hdomain hmax with
    ⟨reducedExtra, _hreducedExtra, reduced, hreduced_domain,
      hreduced_max, hreduced_reward, hreduced⟩
  have hreducedExtra_zero : reducedExtra = 0 :=
    quasiConcave_compressionReduced_extra_eq_zero
      reducedExtra Rhat response hreduced_domain hreduced_max hreduced
      (hresponse_quasiConcave reducedExtra reduced hreduced_reward)
      (hzero_quasiConcave reducedExtra reduced hreduced_reward)
      (hupper_derivative reducedExtra reduced)
      (hlower_derivative reducedExtra reduced)
      (hleft_lower_right_derivative reducedExtra reduced)
  subst reducedExtra
  refine ⟨gn21EndpointVectorPolicy reduced, ?_, hreduced_reward⟩
  exact lemma5SourcePolicyForm_of_mem_canonicalEndpointDomain
    .strictlyQuasiConcave reduced hreduced_domain (by simp)

/-- Every strictly-quasi-convex finite-family maximizer has an equal-reward source form. -/
theorem exists_strictlyQuasiConvex_source_form_of_endpoint_maximum
    (mu : Measure TripLength) [NoAtoms mu]
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .strictlyQuasiConvex extra)
    (hmax :
      ∀ candidate ∈
          gn21Lemma5EndpointDomain .strictlyQuasiConvex extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hRhat_ae : ∀ {sigma tau : TripPolicy},
      policyAlmostEverywhereEq mu sigma tau → Rhat sigma = Rhat tau)
    (hresponse_quasiConvex :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra),
        Rhat (gn21EndpointVectorPolicy reduced) =
            Rhat (gn21EndpointVectorPolicy endpoints) →
          strictQuasiConvexOnPositive
            (response (gn21EndpointVectorPolicy reduced)))
    (hzero_quasiConvex :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra),
        Rhat (gn21EndpointVectorPolicy reduced) =
            Rhat (gn21EndpointVectorPolicy endpoints) →
          ∀ {middleLower middleUpper right : ℝ},
            0 < middleLower → middleLower < middleUpper →
              middleUpper < right →
                response (gn21EndpointVectorPolicy reduced) middleLower <
                  max (response (gn21EndpointVectorPolicy reduced) 0)
                    (response (gn21EndpointVectorPolicy reduced) right))
    (hupper_derivative :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra)
        (i : Fin reducedExtra) {value : ℝ},
        reduced (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint reduced
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy reduced) value))
    (hlower_derivative :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra)
        (i : Fin reducedExtra) {value : ℝ},
        reduced (gn21Lemma5GapLowerIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint reduced
                    (gn21Lemma5GapLowerIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy reduced) value))
    (hleft_upper_right_derivative :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra)
        (i : Fin reducedExtra),
        reduced (gn21Lemma5GapUpperIndex i) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint reduced
                      (gn21Lemma5GapUpperIndex i) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (response (gn21EndpointVectorPolicy reduced) 0))
    (hright_top_witness :
      ∀ (reducedExtra : Nat)
        (reduced : GN21Lemma5EndpointVector reducedExtra),
        Rhat (gn21EndpointVectorPolicy reduced) =
            Rhat (gn21EndpointVectorPolicy endpoints) →
          ∀ (j : Fin reducedExtra),
            reduced (gn21Lemma5GapLowerIndex j) = ∞ →
              ∃ rightValue : ℝ,
                reduced (gn21Lemma5GapUpperIndex j) <
                    ENNReal.ofReal rightValue ∧
                  response (gn21EndpointVectorPolicy reduced) rightValue ≤ 0) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .strictlyQuasiConvex policy ∧
        Rhat policy = Rhat (gn21EndpointVectorPolicy endpoints) := by
  rcases exists_gn21Lemma5CompressionReduced_maximum
      mu .strictlyQuasiConvex Rhat hRhat_ae extra hdomain hmax with
    ⟨reducedExtra, _hreducedExtra, reduced, hreduced_domain,
      hreduced_max, hreduced_reward, hreduced⟩
  have hreducedExtra_le : reducedExtra ≤ 1 :=
    quasiConvex_compressionReduced_extra_le_one
      reducedExtra Rhat response hreduced_domain hreduced_max hreduced
      (hresponse_quasiConvex reducedExtra reduced hreduced_reward)
      (hzero_quasiConvex reducedExtra reduced hreduced_reward)
      (hupper_derivative reducedExtra reduced)
      (hlower_derivative reducedExtra reduced)
      (hleft_upper_right_derivative reducedExtra reduced)
      (hright_top_witness reducedExtra reduced hreduced_reward)
  have hreducedExtra_cases : reducedExtra = 0 ∨ reducedExtra = 1 := by
    omega
  rcases hreducedExtra_cases with hreducedExtra_zero | hreducedExtra_one
  · subst reducedExtra
    let canonical := gn21PadCollapsedLast 0 reduced
    have hcanonical_domain : canonical ∈
        gn21Lemma5CanonicalEndpointDomain .strictlyQuasiConvex := by
      exact gn21PadCollapsedLast_mem_lemma5EndpointDomain
        .strictlyQuasiConvex 0 hreduced_domain
    refine ⟨gn21EndpointVectorPolicy canonical, ?_, ?_⟩
    · exact lemma5SourcePolicyForm_of_mem_canonicalEndpointDomain
        .strictlyQuasiConvex canonical hcanonical_domain (by simp)
    · rw [show gn21EndpointVectorPolicy canonical =
          gn21EndpointVectorPolicy reduced from
        gn21EndpointVectorPolicy_padCollapsedLast 0 reduced]
      exact hreduced_reward
  · subst reducedExtra
    refine ⟨gn21EndpointVectorPolicy reduced, ?_, hreduced_reward⟩
    exact lemma5SourcePolicyForm_of_mem_canonicalEndpointDomain
      .strictlyQuasiConvex reduced hreduced_domain (by simp)

/-! ## Positive response in a near-optimal reward band -/

/--
At a zero upper endpoint, reward continuity keeps a sufficiently short
endpoint path inside the near-optimal band.  Positivity on that band then
gives a strict local improvement, without requiring a response sign at zero.
-/
theorem positive_endpoint_maximum_gap_eq_of_upper_zero_above_threshold
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    (threshold : ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .positive extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hthreshold : threshold < Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_positive :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        threshold ≤ Rhat (gn21EndpointVectorPolicy candidate) →
          ∀ u : TripLength, 0 < u →
            0 < response (gn21EndpointVectorPolicy candidate) u)
    (hpath_continuous :
      ∀ (i : Fin extra) (upper : ℝ), 0 < upper →
        ContinuousOn
          (fun x =>
            Rhat (gn21EndpointVectorPolicy
              (gn21UpdateEndpoint endpoints
                (gn21Lemma5GapUpperIndex i) x)))
          (Set.Icc 0 upper))
    (hpath_derivative :
      ∀ (i : Fin extra) (upper : ℝ) (x : ℝ),
        x ∈ Set.Ioo 0 upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun y =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) y)))
              derivativeValue x ∧
            sameStrictSign derivativeValue
              (response
                (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)) x))
    (i : Fin extra)
    (hupper_zero : endpoints (gn21Lemma5GapUpperIndex i) = 0) :
    endpoints (gn21Lemma5GapUpperIndex i) =
      endpoints (gn21Lemma5GapLowerIndex i) := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  have hle :
      endpoints (gn21Lemma5GapUpperIndex i) ≤
        endpoints (gn21Lemma5GapLowerIndex i) :=
    hordered (le_of_lt (gn21Lemma5GapUpperIndex_lt_lowerIndex i))
  apply le_antisymm hle
  by_contra hnot
  have hlower_pos : 0 < endpoints (gn21Lemma5GapLowerIndex i) := by
    rw [hupper_zero] at hnot
    exact lt_of_not_ge hnot
  rcases exists_pos_real_of_zero_lt_ennreal hlower_pos with
    ⟨fullUpper, hfullUpper_pos, hfullUpper_bound⟩
  let path : ℝ → ℝ := fun x =>
    Rhat (gn21EndpointVectorPolicy
      (gn21UpdateEndpoint endpoints (gn21Lemma5GapUpperIndex i) x))
  have hcandidate_mem :
      ∀ x ∈ Set.Icc (0 : ℝ) fullUpper,
        gn21UpdateEndpoint endpoints (gn21Lemma5GapUpperIndex i) x ∈
          gn21Lemma5EndpointDomain .positive extra := by
    intro x hx
    apply gn21UpdateEndpoint_mem_lemma5EndpointDomain
        .positive extra hdomain (gn21Lemma5GapUpperIndex i) x
    · intro j hj
      calc
        endpoints j ≤ endpoints (gn21Lemma5GapUpperIndex i) :=
          hordered (le_of_lt hj)
        _ = 0 := hupper_zero
        _ ≤ ENNReal.ofReal x := bot_le
    · intro j hj
      exact (ENNReal.ofReal_mono hx.2).trans
        (hfullUpper_bound.trans
          (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt i hj)))
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_first i
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_last i
  have hstart :
      gn21UpdateEndpoint endpoints (gn21Lemma5GapUpperIndex i) 0 =
        endpoints := by
    unfold gn21UpdateEndpoint
    rw [ENNReal.ofReal_zero, ← hupper_zero]
    exact Function.update_eq_self _ _
  have hpath_zero : path 0 = Rhat (gn21EndpointVectorPolicy endpoints) := by
    simp [path, hstart]
  have hthreshold_path_zero : threshold < path 0 := by
    simpa [hpath_zero] using hthreshold
  have hcontinuous_at_zero :
      ContinuousWithinAt path (Set.Icc (0 : ℝ) fullUpper) 0 := by
    exact (hpath_continuous i fullUpper hfullUpper_pos)
      0 ⟨le_rfl, le_of_lt hfullUpper_pos⟩
  rw [Metric.continuousWithinAt_iff] at hcontinuous_at_zero
  let slack := path 0 - threshold
  have hslack_pos : 0 < slack := by
    dsimp [slack]
    linarith
  rcases hcontinuous_at_zero slack hslack_pos with
    ⟨delta, hdelta_pos, hdelta⟩
  let upper := min (fullUpper / 2) (delta / 2)
  have hupper_pos : 0 < upper := by
    dsimp [upper]
    exact lt_min (half_pos hfullUpper_pos) (half_pos hdelta_pos)
  have hupper_lt_full : upper < fullUpper := by
    have := min_le_left (fullUpper / 2) (delta / 2)
    dsimp [upper]
    linarith
  have hupper_lt_delta : upper < delta := by
    have := min_le_right (fullUpper / 2) (delta / 2)
    dsimp [upper]
    linarith
  have hpath_near :
      ∀ x ∈ Set.Icc (0 : ℝ) upper, threshold < path x := by
    intro x hx
    have hx_full : x ∈ Set.Icc (0 : ℝ) fullUpper :=
      ⟨hx.1, hx.2.trans (le_of_lt hupper_lt_full)⟩
    have hdist_x : dist x 0 < delta := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
      exact hx.2.trans_lt hupper_lt_delta
    have hclose := hdelta hx_full hdist_x
    have hclose_abs : |path x - path 0| < slack := by
      simpa [Real.dist_eq] using hclose
    have hlower := (abs_lt.1 hclose_abs).1
    dsimp [slack] at hlower
    linarith
  have hpath_lt : path 0 < path upper := by
    apply endpoint_path_lt_of_exists_hasDerivAt_pos_on_Icc hupper_pos
    · exact hpath_continuous i upper hupper_pos
    · intro x hx
      rcases hpath_derivative i upper x hx with
        ⟨derivativeValue, hderivative, hsame_sign⟩
      refine ⟨derivativeValue, hderivative, ?_⟩
      apply sameStrictSign_pos_left hsame_sign
      have hx_full : x ∈ Set.Icc (0 : ℝ) fullUpper :=
        ⟨le_of_lt hx.1, (le_of_lt hx.2).trans (le_of_lt hupper_lt_full)⟩
      exact hresponse_positive
        (gn21UpdateEndpoint endpoints (gn21Lemma5GapUpperIndex i) x)
        (hcandidate_mem x hx_full)
        (le_of_lt (hpath_near x ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
        x hx.1
  have hupper_full : upper ∈ Set.Icc (0 : ℝ) fullUpper :=
    ⟨le_of_lt hupper_pos, le_of_lt hupper_lt_full⟩
  have hbound := hmax
    (gn21UpdateEndpoint endpoints (gn21Lemma5GapUpperIndex i) upper)
    (hcandidate_mem upper hupper_full)
  have hstrict :
      Rhat (gn21EndpointVectorPolicy endpoints) <
        Rhat (gn21EndpointVectorPolicy
          (gn21UpdateEndpoint endpoints
            (gn21Lemma5GapUpperIndex i) upper)) := by
    simpa [path, hstart] using hpath_lt
  exact (not_lt_of_ge hbound) hstrict

/-- A positive response on the current reward band closes every maximizing gap. -/
theorem positive_endpoint_maximum_all_gaps_eq_above_threshold
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    (threshold : ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .positive extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hthreshold : threshold < Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_positive :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        threshold ≤ Rhat (gn21EndpointVectorPolicy candidate) →
          ∀ u : TripLength, 0 < u →
            0 < response (gn21EndpointVectorPolicy candidate) u)
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hpath_continuous :
      ∀ (i : Fin extra) (upper : ℝ), 0 < upper →
        ContinuousOn
          (fun x =>
            Rhat (gn21EndpointVectorPolicy
              (gn21UpdateEndpoint endpoints
                (gn21Lemma5GapUpperIndex i) x)))
          (Set.Icc 0 upper))
    (hpath_derivative :
      ∀ (i : Fin extra) (upper : ℝ) (x : ℝ),
        x ∈ Set.Ioo 0 upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun y =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) y)))
              derivativeValue x ∧
            sameStrictSign derivativeValue
              (response
                (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)) x)) :
    ∀ i : Fin extra,
      endpoints (gn21Lemma5GapUpperIndex i) =
        endpoints (gn21Lemma5GapLowerIndex i) := by
  intro i
  rcases eq_zero_or_pos
      (endpoints (gn21Lemma5GapUpperIndex i)) with hzero | hpos
  · exact positive_endpoint_maximum_gap_eq_of_upper_zero_above_threshold
      extra Rhat response threshold hdomain hmax hthreshold
      hresponse_positive hpath_continuous hpath_derivative i hzero
  · exact positive_endpoint_maximum_gap_eq_of_upper_pos
      extra Rhat response hdomain hmax
      (hresponse_positive endpoints hdomain (le_of_lt hthreshold))
      hupper_derivative i hpos

/-- Positive finite-family maxima have an equal-reward accept-all representative. -/
theorem exists_positive_source_form_of_endpoint_maximum_above_threshold
    (mu : Measure TripLength) [NoAtoms mu]
    (extra : Nat) (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    (threshold : ℝ)
    {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈
      gn21Lemma5EndpointDomain .positive extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        Rhat (gn21EndpointVectorPolicy candidate) ≤
          Rhat (gn21EndpointVectorPolicy endpoints))
    (hRhat_ae : ∀ {sigma tau : TripPolicy},
      policyAlmostEverywhereEq mu sigma tau → Rhat sigma = Rhat tau)
    (hthreshold : threshold < Rhat (gn21EndpointVectorPolicy endpoints))
    (hresponse_positive :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        threshold ≤ Rhat (gn21EndpointVectorPolicy candidate) →
          ∀ u : TripLength, 0 < u →
            0 < response (gn21EndpointVectorPolicy candidate) u)
    (hupper_derivative :
      ∀ (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hpath_continuous :
      ∀ (i : Fin extra) (upper : ℝ), 0 < upper →
        ContinuousOn
          (fun x =>
            Rhat (gn21EndpointVectorPolicy
              (gn21UpdateEndpoint endpoints
                (gn21Lemma5GapUpperIndex i) x)))
          (Set.Icc 0 upper))
    (hpath_derivative :
      ∀ (i : Fin extra) (upper : ℝ) (x : ℝ),
        x ∈ Set.Ioo 0 upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun y =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) y)))
              derivativeValue x ∧
            sameStrictSign derivativeValue
              (response
                (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)) x)) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .positive policy ∧
        Rhat policy = Rhat (gn21EndpointVectorPolicy endpoints) := by
  rcases hdomain with ⟨⟨hordered, hfirst⟩, hlast⟩
  have hgaps := positive_endpoint_maximum_all_gaps_eq_above_threshold
    extra Rhat response threshold ⟨⟨hordered, hfirst⟩, hlast⟩ hmax
    hthreshold hresponse_positive hupper_derivative
    hpath_continuous hpath_derivative
  have hae := policyAlmostEverywhereEq_endpointVectorPolicy_of_all_gaps_eq
    mu extra endpoints hordered hgaps
  change endpoints (gn21Lemma5FirstEndpointIndex extra) = 0 at hfirst
  change endpoints (gn21Lemma5LastEndpointIndex extra) = ∞ at hlast
  rw [hfirst, hlast] at hae
  refine ⟨acceptAllPolicy, rfl, ?_⟩
  exact (hRhat_ae (by simpa using hae)).symm

/-! ## Arbitrary-open source policy dominance -/

/-- The positive-response row of the printed Lemma 5, through weak dominance. -/
theorem exists_positive_source_form_reward_ge_open
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma : Rhat ∅ < Rhat sigma)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain .positive extra))
    (hresponse_positive :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          ∀ u : TripLength, 0 < u → 0 < response tau u)
    (hupper_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hpath_continuous :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra),
        endpoints ∈ gn21Lemma5EndpointDomain .positive extra →
          ∀ (i : Fin extra) (upper : ℝ), 0 < upper →
            ContinuousOn
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              (Set.Icc 0 upper))
    (hpath_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) (upper : ℝ) (x : ℝ),
        x ∈ Set.Ioo 0 upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun y =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) y)))
              derivativeValue x ∧
            sameStrictSign derivativeValue
              (response
                (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)) x)) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .positive policy ∧
        Rhat sigma ≤ Rhat policy := by
  have hrewardGap : 0 < Rhat sigma - Rhat ∅ :=
    sub_pos.mpr hempty_lt_sigma
  have happroximants :
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < margin →
        epsilon < Rhat sigma - Rhat ∅ →
          ∃ policy : TripPolicy,
            lemma5SourcePolicyForm .positive policy ∧
              Rhat sigma - epsilon < Rhat policy := by
    intro epsilon hepsilon_pos hepsilon_margin hepsilon_gap
    rcases exists_gn21Lemma5EndpointDomain_maximum_above_source_sub
        mu .positive Rhat hsigma_open hsigma_subset hcontinuous
        hendpoint_continuous hepsilon_pos hepsilon_gap with
      ⟨extra, endpoints, hdomain, hmax, hsource_lower⟩
    have hnear_strict :
        Rhat sigma - margin <
          Rhat (gn21EndpointVectorPolicy endpoints) := by
      linarith
    have hRhat_ae : ∀ {left right : TripPolicy},
        policyAlmostEverywhereEq mu left right → Rhat left = Rhat right := by
      intro left right hae
      exact reward_eq_of_symmDiffContinuousAt_of_policyAlmostEverywhereEq
        mu Rhat (hcontinuous left) hae
    rcases exists_positive_source_form_of_endpoint_maximum_above_threshold
        mu extra Rhat response (Rhat sigma - margin)
        hdomain hmax hRhat_ae hnear_strict
        (by
          intro candidate hcandidate hcandidate_near
          exact hresponse_positive
            (gn21EndpointVectorPolicy candidate) hcandidate_near)
        (hupper_derivative extra endpoints)
        (hpath_continuous extra endpoints hdomain)
        (hpath_derivative extra endpoints) with
      ⟨policy, hform, hreward⟩
    refine ⟨policy, hform, ?_⟩
    calc
      Rhat sigma - epsilon <
          Rhat (gn21EndpointVectorPolicy endpoints) := hsource_lower
      _ = Rhat policy := hreward.symm
  have hsigma_le_acceptAll : Rhat sigma ≤ Rhat acceptAllPolicy := by
    exact reward_le_of_source_form_approximants
      .positive Rhat sigma acceptAllPolicy hmargin hrewardGap
      (by
        intro policy hform
        change policy = acceptAllPolicy at hform
        rw [hform])
      happroximants
  exact ⟨acceptAllPolicy, rfl, hsigma_le_acceptAll⟩

/-- The positive-response row with the source strict-unless-a.e.-accept-all
conclusion. -/
theorem exists_positive_source_form_reward_ge_and_gt_unless_ae_open
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma : Rhat ∅ < Rhat sigma)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain .positive extra))
    (hresponse_positive :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          ∀ u : TripLength, 0 < u → 0 < response tau u)
    (hupper_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hpath_continuous :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra),
        endpoints ∈ gn21Lemma5EndpointDomain .positive extra →
          ∀ (i : Fin extra) (upper : ℝ), 0 < upper →
            ContinuousOn
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              (Set.Icc 0 upper))
    (hpath_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) (upper : ℝ) (x : ℝ),
        x ∈ Set.Ioo 0 upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun y =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) y)))
              derivativeValue x ∧
            sameStrictSign derivativeValue
              (response
                (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)) x))
    (hopen_interval_upper_derivative :
      GN21Lemma5ComponentUpperDerivativeCondition Rhat response)
    (hopen_tail_lower_derivative :
      GN21Lemma5ComponentTailLowerDerivativeCondition Rhat response) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .positive policy ∧
        Rhat sigma ≤ Rhat policy ∧
        (¬ lemma5SourcePolicyFormAlmostEverywhere mu .positive sigma →
          Rhat sigma < Rhat policy) := by
  by_cases hnot_ae :
      ¬ lemma5SourcePolicyFormAlmostEverywhere mu .positive sigma
  · have hsigma_nonempty : sigma.Nonempty := by
      by_contra hsigma_empty
      have hsigma_eq_empty : sigma = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hsigma_empty
      rw [hsigma_eq_empty] at hempty_lt_sigma
      exact (lt_irrefl (Rhat ∅)) hempty_lt_sigma
    have hnot_form : ¬ lemma5SourcePolicyForm .positive sigma := by
      intro hform
      exact hnot_ae
        (lemma5SourcePolicyFormAlmostEverywhere_of_form mu hform)
    have hshape_sigma :
        ∀ u : TripLength, 0 < u → 0 < response sigma u :=
      hresponse_positive sigma (by linarith)
    rcases exists_positive_open_strict_improvement_of_not_form
        Rhat response hsigma_open hsigma_subset hsigma_nonempty hnot_form
        hshape_sigma hopen_interval_upper_derivative
        hopen_tail_lower_derivative with
      ⟨improved, himproved_open, himproved_subset, himproved_reward⟩
    let improvedMargin : ℝ :=
      margin + (Rhat improved - Rhat sigma)
    have himprovedMargin_pos : 0 < improvedMargin := by
      dsimp [improvedMargin]
      linarith
    have hresponse_improved :
        ∀ tau : TripPolicy,
          Rhat improved - improvedMargin ≤ Rhat tau →
            ∀ u : TripLength, 0 < u → 0 < response tau u := by
      intro tau htau
      apply hresponse_positive tau
      dsimp [improvedMargin] at htau
      linarith
    rcases exists_positive_source_form_reward_ge_open
        mu Rhat response himproved_open himproved_subset
        (hempty_lt_sigma.trans himproved_reward)
        himprovedMargin_pos hcontinuous hendpoint_continuous
        hresponse_improved hupper_derivative hpath_continuous
        hpath_derivative with
      ⟨policy, hpolicy_form, himproved_le⟩
    exact ⟨policy, hpolicy_form,
      (le_of_lt himproved_reward).trans himproved_le,
      fun _ => himproved_reward.trans_le himproved_le⟩
  · rcases exists_positive_source_form_reward_ge_open
        mu Rhat response hsigma_open hsigma_subset hempty_lt_sigma hmargin
        hcontinuous hendpoint_continuous hresponse_positive
        hupper_derivative hpath_continuous hpath_derivative with
      ⟨policy, hpolicy_form, hreward⟩
    exact ⟨policy, hpolicy_form, hreward, fun h => False.elim (hnot_ae h)⟩

/--
The strictly-increasing row of the printed Lemma 5, through the weak
no-worse conclusion.  Endpoint derivative values and their response-sign
relations remain explicit premises.
-/
theorem exists_strictlyIncreasing_source_form_reward_ge_open
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma : Rhat ∅ < Rhat sigma)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain .strictlyIncreasing extra))
    (hresponse_increasing :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          StrictMonoOn (response tau) (Set.Ici 0))
    (hupper_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_right_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra),
        endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (-response (gn21EndpointVectorPolicy endpoints) 0)) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .strictlyIncreasing policy ∧
        Rhat sigma ≤ Rhat policy := by
  rcases exists_gn21Lemma5EndpointDomain_reward_maximum
      .strictlyIncreasing 0 Rhat (hendpoint_continuous 0) with
    ⟨canonical, hcanonical_domain, hcanonical_max⟩
  have hcanonical_source_max :
      ∀ policy : TripPolicy,
        lemma5SourcePolicyForm .strictlyIncreasing policy →
          Rhat policy ≤ Rhat (gn21EndpointVectorPolicy canonical) := by
    intro policy hform
    exact source_policy_reward_le_of_canonicalEndpointDomain_maximum
      .strictlyIncreasing Rhat hcanonical_max hform
  have hrewardGap : 0 < Rhat sigma - Rhat ∅ :=
    sub_pos.mpr hempty_lt_sigma
  have happroximants :
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < margin →
        epsilon < Rhat sigma - Rhat ∅ →
          ∃ policy : TripPolicy,
            lemma5SourcePolicyForm .strictlyIncreasing policy ∧
              Rhat sigma - epsilon < Rhat policy := by
    intro epsilon hepsilon_pos hepsilon_margin hepsilon_gap
    rcases exists_gn21Lemma5EndpointDomain_maximum_above_source_sub
        mu .strictlyIncreasing Rhat hsigma_open hsigma_subset hcontinuous
        hendpoint_continuous hepsilon_pos hepsilon_gap with
      ⟨extra, endpoints, hdomain, hmax, hsource_lower⟩
    have hnear :
        Rhat sigma - margin ≤
          Rhat (gn21EndpointVectorPolicy endpoints) := by
      linarith
    have hRhat_ae : ∀ {left right : TripPolicy},
        policyAlmostEverywhereEq mu left right → Rhat left = Rhat right := by
      intro left right hae
      exact reward_eq_of_symmDiffContinuousAt_of_policyAlmostEverywhereEq
        mu Rhat (hcontinuous left) hae
    have hempty_lt_endpoints :
        Rhat ∅ < Rhat (gn21EndpointVectorPolicy endpoints) := by
      linarith
    rcases exists_strictlyIncreasing_source_form_of_endpoint_maximum
        mu extra Rhat response hdomain hmax hRhat_ae hempty_lt_endpoints
        (by
          intro reducedExtra reduced hreduced_reward
          apply hresponse_increasing
          rw [hreduced_reward]
          exact hnear)
        hupper_derivative hlower_derivative hlower_right_derivative with
      ⟨policy, hform, hreward⟩
    refine ⟨policy, hform, ?_⟩
    calc
      Rhat sigma - epsilon <
          Rhat (gn21EndpointVectorPolicy endpoints) := hsource_lower
      _ = Rhat policy := hreward.symm
  have hsigma_le_canonical :
      Rhat sigma ≤ Rhat (gn21EndpointVectorPolicy canonical) := by
    exact reward_le_of_source_form_approximants
      .strictlyIncreasing Rhat sigma
      (gn21EndpointVectorPolicy canonical) hmargin hrewardGap
      hcanonical_source_max happroximants
  have hcanonical_gt_empty :
      Rhat ∅ < Rhat (gn21EndpointVectorPolicy canonical) :=
    hempty_lt_sigma.trans_le hsigma_le_canonical
  have hcanonical_finite :
      canonical (gn21Lemma5FirstEndpointIndex 0) ≠ ∞ := by
    intro htop
    have hpolicy_empty :
        gn21EndpointVectorPolicy canonical = (∅ : TripPolicy) := by
      change GN21EndpointVector 1 at canonical
      change canonical 0 = ∞ at htop
      rw [gn21EndpointVectorPolicy_one, htop]
      exact gn21ExtendedMiddlePolicy_top _
    rw [hpolicy_empty] at hcanonical_gt_empty
    exact (lt_irrefl (Rhat ∅)) hcanonical_gt_empty
  refine ⟨gn21EndpointVectorPolicy canonical, ?_, hsigma_le_canonical⟩
  exact lemma5SourcePolicyForm_of_mem_canonicalEndpointDomain
    .strictlyIncreasing canonical hcanonical_domain (by
      intro _hshape
      exact hcanonical_finite)

/--
The strictly-increasing Lemma 5 row with the printed strict-unless clause.
The additional arbitrary-context endpoint hypotheses are derivative facts,
not packaged improvement conclusions.  They expose exactly what is needed to
run the source's local variation on a connected component of the original
open policy.
-/
theorem exists_strictlyIncreasing_source_form_reward_ge_and_gt_unless_ae_open
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma : Rhat ∅ < Rhat sigma)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain .strictlyIncreasing extra))
    (hresponse_increasing :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          StrictMonoOn (response tau) (Set.Ici 0))
    (hupper_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) =
            ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_right_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra),
        endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (-response (gn21EndpointVectorPolicy endpoints) 0))
    (hopen_upper_derivative :
      GN21Lemma5ComponentUpperDerivativeCondition Rhat response)
    (hopen_lower_derivative :
      GN21Lemma5ComponentLowerDerivativeCondition Rhat response)
    (hopen_lower_right_derivative :
      GN21Lemma5ComponentLowerRightDerivativeCondition Rhat response) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .strictlyIncreasing policy ∧
        Rhat sigma ≤ Rhat policy ∧
        (¬ lemma5SourcePolicyFormAlmostEverywhere
            mu .strictlyIncreasing sigma →
          Rhat sigma < Rhat policy) := by
  by_cases hnot_ae :
      ¬ lemma5SourcePolicyFormAlmostEverywhere
        mu .strictlyIncreasing sigma
  · have hsigma_nonempty : sigma.Nonempty := by
      by_contra hsigma_empty
      have hsigma_eq_empty : sigma = ∅ := Set.not_nonempty_iff_eq_empty.mp hsigma_empty
      rw [hsigma_eq_empty] at hempty_lt_sigma
      exact (lt_irrefl (Rhat ∅)) hempty_lt_sigma
    have hnot_form :
        ¬ lemma5SourcePolicyForm .strictlyIncreasing sigma := by
      intro hform
      exact hnot_ae
        (lemma5SourcePolicyFormAlmostEverywhere_of_form mu hform)
    have hshape_sigma :
        StrictMonoOn (response sigma) (Set.Ici 0) :=
      hresponse_increasing sigma (by linarith)
    rcases exists_strictlyIncreasing_open_strict_improvement_of_not_form
        Rhat response hsigma_open hsigma_subset hsigma_nonempty hnot_form
        hshape_sigma hopen_upper_derivative hopen_lower_derivative
        hopen_lower_right_derivative with
      ⟨improved, himproved_open, himproved_subset, himproved_reward⟩
    let improvedMargin : ℝ :=
      margin + (Rhat improved - Rhat sigma)
    have himprovedMargin_pos : 0 < improvedMargin := by
      dsimp [improvedMargin]
      linarith
    have hresponse_improved :
        ∀ tau : TripPolicy,
          Rhat improved - improvedMargin ≤ Rhat tau →
            StrictMonoOn (response tau) (Set.Ici 0) := by
      intro tau htau
      apply hresponse_increasing tau
      dsimp [improvedMargin] at htau
      linarith
    rcases exists_strictlyIncreasing_source_form_reward_ge_open
        mu Rhat response himproved_open himproved_subset
        (hempty_lt_sigma.trans himproved_reward)
        himprovedMargin_pos hcontinuous hendpoint_continuous
        hresponse_improved hupper_derivative hlower_derivative
        hlower_right_derivative with
      ⟨policy, hpolicy_form, himproved_le⟩
    exact ⟨policy, hpolicy_form,
      (le_of_lt himproved_reward).trans himproved_le,
      fun _ => himproved_reward.trans_le himproved_le⟩
  · rcases exists_strictlyIncreasing_source_form_reward_ge_open
        mu Rhat response hsigma_open hsigma_subset hempty_lt_sigma hmargin
        hcontinuous hendpoint_continuous hresponse_increasing
        hupper_derivative hlower_derivative hlower_right_derivative with
      ⟨policy, hpolicy_form, hreward⟩
    exact ⟨policy, hpolicy_form, hreward, fun h => False.elim (hnot_ae h)⟩

/-- The strictly-decreasing row of the printed Lemma 5, through weak dominance. -/
theorem exists_strictlyDecreasing_source_form_reward_ge_open
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma : Rhat ∅ < Rhat sigma)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain .strictlyDecreasing extra))
    (hresponse_decreasing :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          StrictAntiOn (response tau) (Set.Ici 0))
    (hupper_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hnext_lower_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapLowerIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapLowerIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (hupper_right_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra),
        endpoints (gn21Lemma5GapUpperIndex i) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21Lemma5GapUpperIndex i) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (response (gn21EndpointVectorPolicy endpoints) 0)) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .strictlyDecreasing policy ∧
        Rhat sigma ≤ Rhat policy := by
  rcases exists_gn21Lemma5EndpointDomain_reward_maximum
      .strictlyDecreasing 0 Rhat (hendpoint_continuous 0) with
    ⟨canonical, hcanonical_domain, hcanonical_max⟩
  have hcanonical_source_max :
      ∀ policy : TripPolicy,
        lemma5SourcePolicyForm .strictlyDecreasing policy →
          Rhat policy ≤ Rhat (gn21EndpointVectorPolicy canonical) := by
    intro policy hform
    exact source_policy_reward_le_of_canonicalEndpointDomain_maximum
      .strictlyDecreasing Rhat hcanonical_max hform
  have hrewardGap : 0 < Rhat sigma - Rhat ∅ :=
    sub_pos.mpr hempty_lt_sigma
  have happroximants :
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < margin →
        epsilon < Rhat sigma - Rhat ∅ →
          ∃ policy : TripPolicy,
            lemma5SourcePolicyForm .strictlyDecreasing policy ∧
              Rhat sigma - epsilon < Rhat policy := by
    intro epsilon hepsilon_pos hepsilon_margin hepsilon_gap
    rcases exists_gn21Lemma5EndpointDomain_maximum_above_source_sub
        mu .strictlyDecreasing Rhat hsigma_open hsigma_subset hcontinuous
        hendpoint_continuous hepsilon_pos hepsilon_gap with
      ⟨extra, endpoints, hdomain, hmax, hsource_lower⟩
    have hnear :
        Rhat sigma - margin ≤
          Rhat (gn21EndpointVectorPolicy endpoints) := by
      linarith
    have hRhat_ae : ∀ {left right : TripPolicy},
        policyAlmostEverywhereEq mu left right → Rhat left = Rhat right := by
      intro left right hae
      exact reward_eq_of_symmDiffContinuousAt_of_policyAlmostEverywhereEq
        mu Rhat (hcontinuous left) hae
    rcases exists_strictlyDecreasing_source_form_of_endpoint_maximum
        mu extra Rhat response hdomain hmax hRhat_ae
        (by
          intro reducedExtra reduced hreduced_reward
          apply hresponse_decreasing
          rw [hreduced_reward]
          exact hnear)
        hupper_derivative hnext_lower_derivative hupper_right_derivative with
      ⟨policy, hform, hreward⟩
    refine ⟨policy, hform, ?_⟩
    calc
      Rhat sigma - epsilon <
          Rhat (gn21EndpointVectorPolicy endpoints) := hsource_lower
      _ = Rhat policy := hreward.symm
  have hsigma_le_canonical :
      Rhat sigma ≤ Rhat (gn21EndpointVectorPolicy canonical) := by
    exact reward_le_of_source_form_approximants
      .strictlyDecreasing Rhat sigma
      (gn21EndpointVectorPolicy canonical) hmargin hrewardGap
      hcanonical_source_max happroximants
  refine ⟨gn21EndpointVectorPolicy canonical, ?_, hsigma_le_canonical⟩
  exact lemma5SourcePolicyForm_of_mem_canonicalEndpointDomain
    .strictlyDecreasing canonical hcanonical_domain (by simp)

/-- The strictly-decreasing row with strict improvement unless the source
policy already has the left-cutoff form almost everywhere. -/
theorem exists_strictlyDecreasing_source_form_reward_ge_and_gt_unless_ae_open
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma : Rhat ∅ < Rhat sigma)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain .strictlyDecreasing extra))
    (hresponse_decreasing :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          StrictAntiOn (response tau) (Set.Ici 0))
    (hupper_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hnext_lower_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapLowerIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapLowerIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (hupper_right_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra),
        endpoints (gn21Lemma5GapUpperIndex i) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21Lemma5GapUpperIndex i) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (response (gn21EndpointVectorPolicy endpoints) 0))
    (hopen_interval_upper_derivative :
      GN21Lemma5ComponentUpperDerivativeCondition Rhat response)
    (hopen_interval_lower_derivative :
      GN21Lemma5ComponentLowerDerivativeCondition Rhat response)
    (hopen_tail_lower_derivative :
      GN21Lemma5ComponentTailLowerDerivativeCondition Rhat response)
    (hopen_split_lower_derivative :
      ∀ (policy : TripPolicy) (pivot : ℝ),
        IsOpen policy → policy ⊆ acceptAllPolicy →
          pivot ∈ policy →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun cutoff =>
                Rhat (gn21InteriorSplitLowerPolicy policy pivot cutoff))
              derivativeValue pivot ∧
            sameStrictSign derivativeValue (-response policy pivot)) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .strictlyDecreasing policy ∧
        Rhat sigma ≤ Rhat policy ∧
        (¬ lemma5SourcePolicyFormAlmostEverywhere
            mu .strictlyDecreasing sigma →
          Rhat sigma < Rhat policy) := by
  by_cases hnot_ae :
      ¬ lemma5SourcePolicyFormAlmostEverywhere
        mu .strictlyDecreasing sigma
  · have hsigma_nonempty : sigma.Nonempty := by
      by_contra hsigma_empty
      have hsigma_eq_empty : sigma = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hsigma_empty
      rw [hsigma_eq_empty] at hempty_lt_sigma
      exact (lt_irrefl (Rhat ∅)) hempty_lt_sigma
    have hnot_form :
        ¬ lemma5SourcePolicyForm .strictlyDecreasing sigma := by
      intro hform
      exact hnot_ae
        (lemma5SourcePolicyFormAlmostEverywhere_of_form mu hform)
    have hRhat_ae :
        ∀ {left right : TripPolicy},
          policyAlmostEverywhereEq mu left right → Rhat left = Rhat right := by
      intro left right hae
      exact reward_eq_of_symmDiffContinuousAt_of_policyAlmostEverywhereEq
        mu Rhat (hcontinuous left) hae
    have hshape_sigma :
        StrictAntiOn (response sigma) (Set.Ici 0) :=
      hresponse_decreasing sigma (by linarith)
    rcases exists_strictlyDecreasing_open_strict_improvement_of_not_form
        mu Rhat response hsigma_open hsigma_subset hsigma_nonempty hnot_form
        hRhat_ae hshape_sigma hopen_interval_upper_derivative
        hopen_interval_lower_derivative hopen_tail_lower_derivative
        hopen_split_lower_derivative with
      ⟨improved, himproved_open, himproved_subset, himproved_reward⟩
    let improvedMargin : ℝ :=
      margin + (Rhat improved - Rhat sigma)
    have himprovedMargin_pos : 0 < improvedMargin := by
      dsimp [improvedMargin]
      linarith
    have hresponse_improved :
        ∀ tau : TripPolicy,
          Rhat improved - improvedMargin ≤ Rhat tau →
            StrictAntiOn (response tau) (Set.Ici 0) := by
      intro tau htau
      apply hresponse_decreasing tau
      dsimp [improvedMargin] at htau
      linarith
    rcases exists_strictlyDecreasing_source_form_reward_ge_open
        mu Rhat response himproved_open himproved_subset
        (hempty_lt_sigma.trans himproved_reward)
        himprovedMargin_pos hcontinuous hendpoint_continuous
        hresponse_improved hupper_derivative hnext_lower_derivative
        hupper_right_derivative with
      ⟨policy, hpolicy_form, himproved_le⟩
    exact ⟨policy, hpolicy_form,
      (le_of_lt himproved_reward).trans himproved_le,
      fun _ => himproved_reward.trans_le himproved_le⟩
  · rcases exists_strictlyDecreasing_source_form_reward_ge_open
        mu Rhat response hsigma_open hsigma_subset hempty_lt_sigma hmargin
        hcontinuous hendpoint_continuous hresponse_decreasing
        hupper_derivative hnext_lower_derivative hupper_right_derivative with
      ⟨policy, hpolicy_form, hreward⟩
    exact ⟨policy, hpolicy_form, hreward, fun h => False.elim (hnot_ae h)⟩

/-- The strictly-quasi-concave row of the printed Lemma 5, through weak dominance. -/
theorem exists_strictlyQuasiConcave_source_form_reward_ge_open
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma : Rhat ∅ < Rhat sigma)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain .strictlyQuasiConcave extra))
    (hresponse_quasiConcave :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          strictQuasiConcaveOnPositive (response tau))
    (hzero_quasiConcave :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          ∀ {middle right : ℝ}, 0 < middle → middle < right →
            min (response tau 0) (response tau right) <
              response tau middle)
    (hupper_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (slot : Fin (extra + 1)) {value : ℝ},
        endpoints (gn21LowerEndpointIndex slot) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21LowerEndpointIndex slot) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (hleft_lower_right_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra),
        endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (-response (gn21EndpointVectorPolicy endpoints) 0)) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .strictlyQuasiConcave policy ∧
        Rhat sigma ≤ Rhat policy := by
  rcases exists_gn21Lemma5EndpointDomain_reward_maximum
      .strictlyQuasiConcave 0 Rhat (hendpoint_continuous 0) with
    ⟨canonical, hcanonical_domain, hcanonical_max⟩
  have hcanonical_source_max :
      ∀ policy : TripPolicy,
        lemma5SourcePolicyForm .strictlyQuasiConcave policy →
          Rhat policy ≤ Rhat (gn21EndpointVectorPolicy canonical) := by
    intro policy hform
    exact source_policy_reward_le_of_canonicalEndpointDomain_maximum
      .strictlyQuasiConcave Rhat hcanonical_max hform
  have hrewardGap : 0 < Rhat sigma - Rhat ∅ :=
    sub_pos.mpr hempty_lt_sigma
  have happroximants :
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < margin →
        epsilon < Rhat sigma - Rhat ∅ →
          ∃ policy : TripPolicy,
            lemma5SourcePolicyForm .strictlyQuasiConcave policy ∧
              Rhat sigma - epsilon < Rhat policy := by
    intro epsilon hepsilon_pos hepsilon_margin hepsilon_gap
    rcases exists_gn21Lemma5EndpointDomain_maximum_above_source_sub
        mu .strictlyQuasiConcave Rhat hsigma_open hsigma_subset hcontinuous
        hendpoint_continuous hepsilon_pos hepsilon_gap with
      ⟨extra, endpoints, hdomain, hmax, hsource_lower⟩
    have hnear :
        Rhat sigma - margin ≤
          Rhat (gn21EndpointVectorPolicy endpoints) := by
      linarith
    have hRhat_ae : ∀ {left right : TripPolicy},
        policyAlmostEverywhereEq mu left right → Rhat left = Rhat right := by
      intro left right hae
      exact reward_eq_of_symmDiffContinuousAt_of_policyAlmostEverywhereEq
        mu Rhat (hcontinuous left) hae
    rcases exists_strictlyQuasiConcave_source_form_of_endpoint_maximum
        mu extra Rhat response hdomain hmax hRhat_ae
        (by
          intro reducedExtra reduced hreduced_reward
          apply hresponse_quasiConcave
          rw [hreduced_reward]
          exact hnear)
        (by
          intro reducedExtra reduced hreduced_reward
          apply hzero_quasiConcave
          rw [hreduced_reward]
          exact hnear)
        hupper_derivative hlower_derivative
        hleft_lower_right_derivative with
      ⟨policy, hform, hreward⟩
    refine ⟨policy, hform, ?_⟩
    calc
      Rhat sigma - epsilon <
          Rhat (gn21EndpointVectorPolicy endpoints) := hsource_lower
      _ = Rhat policy := hreward.symm
  have hsigma_le_canonical :
      Rhat sigma ≤ Rhat (gn21EndpointVectorPolicy canonical) := by
    exact reward_le_of_source_form_approximants
      .strictlyQuasiConcave Rhat sigma
      (gn21EndpointVectorPolicy canonical) hmargin hrewardGap
      hcanonical_source_max happroximants
  refine ⟨gn21EndpointVectorPolicy canonical, ?_, hsigma_le_canonical⟩
  exact lemma5SourcePolicyForm_of_mem_canonicalEndpointDomain
    .strictlyQuasiConcave canonical hcanonical_domain (by simp)

/-- The strictly-quasi-concave row with its strict-unless-single-interval-a.e.
clause. -/
theorem exists_strictlyQuasiConcave_source_form_reward_ge_and_gt_unless_ae_open
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma : Rhat ∅ < Rhat sigma)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain .strictlyQuasiConcave extra))
    (hresponse_quasiConcave :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          strictQuasiConcaveOnPositive (response tau))
    (hzero_quasiConcave :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          ∀ {middle right : ℝ}, 0 < middle → middle < right →
            min (response tau 0) (response tau right) <
              response tau middle)
    (hupper_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (slot : Fin (extra + 1)) {value : ℝ},
        endpoints (gn21LowerEndpointIndex slot) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21LowerEndpointIndex slot) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (hleft_lower_right_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra),
        endpoints (gn21LowerEndpointIndex (Fin.castSucc i)) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21LowerEndpointIndex (Fin.castSucc i)) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (-response (gn21EndpointVectorPolicy endpoints) 0))
    (hopen_interval_upper_derivative :
      GN21Lemma5ComponentUpperDerivativeCondition Rhat response)
    (hopen_split_lower_derivative :
      ∀ (policy : TripPolicy) (pivot : ℝ),
        IsOpen policy → policy ⊆ acceptAllPolicy →
          pivot ∈ policy →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun cutoff =>
                Rhat (gn21InteriorSplitLowerPolicy policy pivot cutoff))
              derivativeValue pivot ∧
            sameStrictSign derivativeValue (-response policy pivot)) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .strictlyQuasiConcave policy ∧
        Rhat sigma ≤ Rhat policy ∧
        (¬ lemma5SourcePolicyFormAlmostEverywhere
            mu .strictlyQuasiConcave sigma →
          Rhat sigma < Rhat policy) := by
  by_cases hnot_ae :
      ¬ lemma5SourcePolicyFormAlmostEverywhere
        mu .strictlyQuasiConcave sigma
  · have hsigma_nonempty : sigma.Nonempty := by
      by_contra hsigma_empty
      have hsigma_eq_empty : sigma = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hsigma_empty
      rw [hsigma_eq_empty] at hempty_lt_sigma
      exact (lt_irrefl (Rhat ∅)) hempty_lt_sigma
    have hnot_form :
        ¬ lemma5SourcePolicyForm .strictlyQuasiConcave sigma := by
      intro hform
      exact hnot_ae
        (lemma5SourcePolicyFormAlmostEverywhere_of_form mu hform)
    have hRhat_ae :
        ∀ {left right : TripPolicy},
          policyAlmostEverywhereEq mu left right → Rhat left = Rhat right := by
      intro left right hae
      exact reward_eq_of_symmDiffContinuousAt_of_policyAlmostEverywhereEq
        mu Rhat (hcontinuous left) hae
    have hshape_sigma :
        strictQuasiConcaveOnPositive (response sigma) :=
      hresponse_quasiConcave sigma (by linarith)
    rcases exists_strictlyQuasiConcave_open_strict_improvement_of_not_form
        mu Rhat response hsigma_open hsigma_subset hsigma_nonempty hnot_form
        hRhat_ae hshape_sigma hopen_interval_upper_derivative
        hopen_split_lower_derivative with
      ⟨improved, himproved_open, himproved_subset, himproved_reward⟩
    let improvedMargin : ℝ :=
      margin + (Rhat improved - Rhat sigma)
    have himprovedMargin_pos : 0 < improvedMargin := by
      dsimp [improvedMargin]
      linarith
    have hresponse_improved :
        ∀ tau : TripPolicy,
          Rhat improved - improvedMargin ≤ Rhat tau →
            strictQuasiConcaveOnPositive (response tau) := by
      intro tau htau
      apply hresponse_quasiConcave tau
      dsimp [improvedMargin] at htau
      linarith
    have hzero_improved :
        ∀ tau : TripPolicy,
          Rhat improved - improvedMargin ≤ Rhat tau →
            ∀ {middle right : ℝ}, 0 < middle → middle < right →
              min (response tau 0) (response tau right) <
                response tau middle := by
      intro tau htau
      apply hzero_quasiConcave tau
      dsimp [improvedMargin] at htau
      linarith
    rcases exists_strictlyQuasiConcave_source_form_reward_ge_open
        mu Rhat response himproved_open himproved_subset
        (hempty_lt_sigma.trans himproved_reward)
        himprovedMargin_pos hcontinuous hendpoint_continuous
        hresponse_improved hzero_improved hupper_derivative
        hlower_derivative hleft_lower_right_derivative with
      ⟨policy, hpolicy_form, himproved_le⟩
    exact ⟨policy, hpolicy_form,
      (le_of_lt himproved_reward).trans himproved_le,
      fun _ => himproved_reward.trans_le himproved_le⟩
  · rcases exists_strictlyQuasiConcave_source_form_reward_ge_open
        mu Rhat response hsigma_open hsigma_subset hempty_lt_sigma hmargin
        hcontinuous hendpoint_continuous hresponse_quasiConcave
        hzero_quasiConcave hupper_derivative hlower_derivative
        hleft_lower_right_derivative with
      ⟨policy, hpolicy_form, hreward⟩
    exact ⟨policy, hpolicy_form, hreward, fun h => False.elim (hnot_ae h)⟩

/-- The strictly-quasi-convex row of the printed Lemma 5, through weak dominance. -/
theorem exists_strictlyQuasiConvex_source_form_reward_ge_open
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma : Rhat ∅ < Rhat sigma)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain .strictlyQuasiConvex extra))
    (hresponse_quasiConvex :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          strictQuasiConvexOnPositive (response tau))
    (hzero_quasiConvex :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          ∀ {middleLower middleUpper right : ℝ},
            0 < middleLower → middleLower < middleUpper →
              middleUpper < right →
                response tau middleLower <
                  max (response tau 0) (response tau right))
    (hupper_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapLowerIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapLowerIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (hleft_upper_right_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra),
        endpoints (gn21Lemma5GapUpperIndex i) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21Lemma5GapUpperIndex i) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (response (gn21EndpointVectorPolicy endpoints) 0))
    (hright_top_witness :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra),
        Rhat sigma - margin ≤
            Rhat (gn21EndpointVectorPolicy endpoints) →
          ∀ (j : Fin extra),
            endpoints (gn21Lemma5GapLowerIndex j) = ∞ →
              ∃ rightValue : ℝ,
                endpoints (gn21Lemma5GapUpperIndex j) <
                    ENNReal.ofReal rightValue ∧
                  response (gn21EndpointVectorPolicy endpoints) rightValue ≤ 0) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .strictlyQuasiConvex policy ∧
        Rhat sigma ≤ Rhat policy := by
  rcases exists_gn21Lemma5EndpointDomain_reward_maximum
      .strictlyQuasiConvex 1 Rhat (hendpoint_continuous 1) with
    ⟨canonical, hcanonical_domain, hcanonical_max⟩
  have hcanonical_source_max :
      ∀ policy : TripPolicy,
        lemma5SourcePolicyForm .strictlyQuasiConvex policy →
          Rhat policy ≤ Rhat (gn21EndpointVectorPolicy canonical) := by
    intro policy hform
    exact source_policy_reward_le_of_canonicalEndpointDomain_maximum
      .strictlyQuasiConvex Rhat hcanonical_max hform
  have hrewardGap : 0 < Rhat sigma - Rhat ∅ :=
    sub_pos.mpr hempty_lt_sigma
  have happroximants :
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < margin →
        epsilon < Rhat sigma - Rhat ∅ →
          ∃ policy : TripPolicy,
            lemma5SourcePolicyForm .strictlyQuasiConvex policy ∧
              Rhat sigma - epsilon < Rhat policy := by
    intro epsilon hepsilon_pos hepsilon_margin hepsilon_gap
    rcases exists_gn21Lemma5EndpointDomain_maximum_above_source_sub
        mu .strictlyQuasiConvex Rhat hsigma_open hsigma_subset hcontinuous
        hendpoint_continuous hepsilon_pos hepsilon_gap with
      ⟨extra, endpoints, hdomain, hmax, hsource_lower⟩
    have hnear :
        Rhat sigma - margin ≤
          Rhat (gn21EndpointVectorPolicy endpoints) := by
      linarith
    have hRhat_ae : ∀ {left right : TripPolicy},
        policyAlmostEverywhereEq mu left right → Rhat left = Rhat right := by
      intro left right hae
      exact reward_eq_of_symmDiffContinuousAt_of_policyAlmostEverywhereEq
        mu Rhat (hcontinuous left) hae
    rcases exists_strictlyQuasiConvex_source_form_of_endpoint_maximum
        mu extra Rhat response hdomain hmax hRhat_ae
        (by
          intro reducedExtra reduced hreduced_reward
          apply hresponse_quasiConvex
          rw [hreduced_reward]
          exact hnear)
        (by
          intro reducedExtra reduced hreduced_reward
          apply hzero_quasiConvex
          rw [hreduced_reward]
          exact hnear)
        hupper_derivative hlower_derivative
        hleft_upper_right_derivative
        (by
          intro reducedExtra reduced hreduced_reward
          apply hright_top_witness
          rw [hreduced_reward]
          exact hnear) with
      ⟨policy, hform, hreward⟩
    refine ⟨policy, hform, ?_⟩
    calc
      Rhat sigma - epsilon <
          Rhat (gn21EndpointVectorPolicy endpoints) := hsource_lower
      _ = Rhat policy := hreward.symm
  have hsigma_le_canonical :
      Rhat sigma ≤ Rhat (gn21EndpointVectorPolicy canonical) := by
    exact reward_le_of_source_form_approximants
      .strictlyQuasiConvex Rhat sigma
      (gn21EndpointVectorPolicy canonical) hmargin hrewardGap
      hcanonical_source_max happroximants
  refine ⟨gn21EndpointVectorPolicy canonical, ?_, hsigma_le_canonical⟩
  exact lemma5SourcePolicyForm_of_mem_canonicalEndpointDomain
    .strictlyQuasiConvex canonical hcanonical_domain (by simp)

/-- The strictly-quasi-convex row with its strict-unless-two-tail-a.e. clause. -/
theorem exists_strictlyQuasiConvex_source_form_reward_ge_and_gt_unless_ae_open
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma : Rhat ∅ < Rhat sigma)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain .strictlyQuasiConvex extra))
    (hresponse_quasiConvex :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          strictQuasiConvexOnPositive (response tau))
    (hzero_quasiConvex :
      ∀ tau : TripPolicy,
        Rhat sigma - margin ≤ Rhat tau →
          ∀ {middleLower middleUpper right : ℝ},
            0 < middleLower → middleLower < middleUpper →
              middleUpper < right →
                response tau middleLower <
                  max (response tau 0) (response tau right))
    (hupper_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapLowerIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapLowerIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (hleft_upper_right_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra),
        endpoints (gn21Lemma5GapUpperIndex i) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21Lemma5GapUpperIndex i) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (response (gn21EndpointVectorPolicy endpoints) 0))
    (hright_top_witness :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra),
        Rhat sigma - margin ≤
            Rhat (gn21EndpointVectorPolicy endpoints) →
          ∀ (j : Fin extra),
            endpoints (gn21Lemma5GapLowerIndex j) = ∞ →
              ∃ rightValue : ℝ,
                endpoints (gn21Lemma5GapUpperIndex j) <
                    ENNReal.ofReal rightValue ∧
                  response (gn21EndpointVectorPolicy endpoints) rightValue ≤ 0)
    (hopen_interval_upper_derivative :
      GN21Lemma5ComponentUpperDerivativeCondition Rhat response)
    (hopen_interval_lower_derivative :
      GN21Lemma5ComponentLowerDerivativeCondition Rhat response)
    (hopen_split_lower_derivative :
      ∀ (policy : TripPolicy) (pivot : ℝ),
        IsOpen policy → policy ⊆ acceptAllPolicy →
          pivot ∈ policy →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun cutoff =>
                Rhat (gn21InteriorSplitLowerPolicy policy pivot cutoff))
              derivativeValue pivot ∧
            sameStrictSign derivativeValue (-response policy pivot)) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm .strictlyQuasiConvex policy ∧
        Rhat sigma ≤ Rhat policy ∧
        (¬ lemma5SourcePolicyFormAlmostEverywhere
            mu .strictlyQuasiConvex sigma →
          Rhat sigma < Rhat policy) := by
  by_cases hnot_ae :
      ¬ lemma5SourcePolicyFormAlmostEverywhere
        mu .strictlyQuasiConvex sigma
  · have hsigma_nonempty : sigma.Nonempty := by
      by_contra hsigma_empty
      have hsigma_eq_empty : sigma = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hsigma_empty
      rw [hsigma_eq_empty] at hempty_lt_sigma
      exact (lt_irrefl (Rhat ∅)) hempty_lt_sigma
    have hnot_form :
        ¬ lemma5SourcePolicyForm .strictlyQuasiConvex sigma := by
      intro hform
      exact hnot_ae
        (lemma5SourcePolicyFormAlmostEverywhere_of_form mu hform)
    have hRhat_ae :
        ∀ {left right : TripPolicy},
          policyAlmostEverywhereEq mu left right → Rhat left = Rhat right := by
      intro left right hae
      exact reward_eq_of_symmDiffContinuousAt_of_policyAlmostEverywhereEq
        mu Rhat (hcontinuous left) hae
    have hshape_sigma :
        strictQuasiConvexOnPositive (response sigma) :=
      hresponse_quasiConvex sigma (by linarith)
    rcases exists_strictlyQuasiConvex_open_strict_improvement_of_not_form
        mu Rhat response hsigma_open hsigma_subset hsigma_nonempty hnot_form
        hRhat_ae hshape_sigma hopen_interval_upper_derivative
        hopen_interval_lower_derivative hopen_split_lower_derivative with
      ⟨improved, himproved_open, himproved_subset, himproved_reward⟩
    let improvedMargin : ℝ :=
      margin + (Rhat improved - Rhat sigma)
    have himprovedMargin_pos : 0 < improvedMargin := by
      dsimp [improvedMargin]
      linarith
    have hresponse_improved :
        ∀ tau : TripPolicy,
          Rhat improved - improvedMargin ≤ Rhat tau →
            strictQuasiConvexOnPositive (response tau) := by
      intro tau htau
      apply hresponse_quasiConvex tau
      dsimp [improvedMargin] at htau
      linarith
    have hzero_improved :
        ∀ tau : TripPolicy,
          Rhat improved - improvedMargin ≤ Rhat tau →
            ∀ {middleLower middleUpper right : ℝ},
              0 < middleLower → middleLower < middleUpper →
                middleUpper < right →
                  response tau middleLower <
                    max (response tau 0) (response tau right) := by
      intro tau htau
      apply hzero_quasiConvex tau
      dsimp [improvedMargin] at htau
      linarith
    have hright_top_improved :
        ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra),
          Rhat improved - improvedMargin ≤
              Rhat (gn21EndpointVectorPolicy endpoints) →
            ∀ (j : Fin extra),
              endpoints (gn21Lemma5GapLowerIndex j) = ∞ →
                ∃ rightValue : ℝ,
                  endpoints (gn21Lemma5GapUpperIndex j) <
                      ENNReal.ofReal rightValue ∧
                    response
                      (gn21EndpointVectorPolicy endpoints) rightValue ≤ 0 := by
      intro extra endpoints hendpoints
      apply hright_top_witness extra endpoints
      dsimp [improvedMargin] at hendpoints
      linarith
    rcases exists_strictlyQuasiConvex_source_form_reward_ge_open
        mu Rhat response himproved_open himproved_subset
        (hempty_lt_sigma.trans himproved_reward)
        himprovedMargin_pos hcontinuous hendpoint_continuous
        hresponse_improved hzero_improved hupper_derivative
        hlower_derivative hleft_upper_right_derivative
        hright_top_improved with
      ⟨policy, hpolicy_form, himproved_le⟩
    exact ⟨policy, hpolicy_form,
      (le_of_lt himproved_reward).trans himproved_le,
      fun _ => himproved_reward.trans_le himproved_le⟩
  · rcases exists_strictlyQuasiConvex_source_form_reward_ge_open
        mu Rhat response hsigma_open hsigma_subset hempty_lt_sigma hmargin
        hcontinuous hendpoint_continuous hresponse_quasiConvex
        hzero_quasiConvex hupper_derivative hlower_derivative
        hleft_upper_right_derivative hright_top_witness with
      ⟨policy, hpolicy_form, hreward⟩
    exact ⟨policy, hpolicy_form, hreward, fun h => False.elim (hnot_ae h)⟩

/--
Direct source-facing form of Lemma 5 (`source.txt:3343-3404`, with the five
policy forms in the table at `source.txt:3370-3386`).  No optimizer or policy
form conclusion is supplied as a premise.

The endpoint hypotheses deliberately state the derivative/response sign
relation at every endpoint used by the variational proof.  The printed proof
only establishes that relation where the trip-length density is positive; it
does not justify moving an endpoint through a zero-density region.  Thus this
is the audited corrected statement: an application must derive these visible
sign premises from model primitives (for example from full support), or prove
the corresponding zero-density invariance separately.
-/
theorem paper_lemma5_source_policy_replacement_open
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    (shape : Lemma5DerivativeShape)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma : Rhat ∅ < Rhat sigma)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain shape extra))
    (hresponse_positive :
      shape = .positive →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            ∀ u : TripLength, 0 < u → 0 < response tau u)
    (hresponse_increasing :
      shape = .strictlyIncreasing →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            StrictMonoOn (response tau) (Set.Ici 0))
    (hresponse_decreasing :
      shape = .strictlyDecreasing →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            StrictAntiOn (response tau) (Set.Ici 0))
    (hresponse_quasiConvex :
      shape = .strictlyQuasiConvex →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            strictQuasiConvexOnPositive (response tau))
    (hzero_quasiConvex :
      shape = .strictlyQuasiConvex →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            ∀ {middleLower middleUpper right : ℝ},
              0 < middleLower → middleLower < middleUpper →
                middleUpper < right →
                  response tau middleLower <
                    max (response tau 0) (response tau right))
    (hresponse_quasiConcave :
      shape = .strictlyQuasiConcave →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            strictQuasiConcaveOnPositive (response tau))
    (hzero_quasiConcave :
      shape = .strictlyQuasiConcave →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            ∀ {middle right : ℝ}, 0 < middle → middle < right →
              min (response tau 0) (response tau right) <
                response tau middle)
    (hupper_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) {value : ℝ},
        endpoints (gn21Lemma5GapUpperIndex i) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (response (gn21EndpointVectorPolicy endpoints) value))
    (hlower_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (slot : Fin (extra + 1)) {value : ℝ},
        endpoints (gn21LowerEndpointIndex slot) = ENNReal.ofReal value →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21LowerEndpointIndex slot) x)))
              derivativeValue value ∧
            sameStrictSign derivativeValue
              (-response (gn21EndpointVectorPolicy endpoints) value))
    (hupper_right_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra),
        endpoints (gn21Lemma5GapUpperIndex i) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21Lemma5GapUpperIndex i) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (response (gn21EndpointVectorPolicy endpoints) 0))
    (hlower_right_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (slot : Fin (extra + 1)),
        endpoints (gn21LowerEndpointIndex slot) = 0 →
          ∃ derivativeValue : ℝ,
            HasDerivWithinAt
                (fun x =>
                  Rhat (gn21EndpointVectorPolicy
                    (gn21UpdateEndpoint endpoints
                      (gn21LowerEndpointIndex slot) x)))
                derivativeValue (Set.Ici 0) 0 ∧
              sameStrictSign derivativeValue
                (-response (gn21EndpointVectorPolicy endpoints) 0))
    (hpositive_path_continuous :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra),
        endpoints ∈ gn21Lemma5EndpointDomain .positive extra →
          ∀ (i : Fin extra) (upper : ℝ), 0 < upper →
            ContinuousOn
              (fun x =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)))
              (Set.Icc 0 upper))
    (hpositive_path_derivative :
      ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra)
        (i : Fin extra) (upper : ℝ) (x : ℝ),
        x ∈ Set.Ioo 0 upper →
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun y =>
                Rhat (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) y)))
              derivativeValue x ∧
            sameStrictSign derivativeValue
              (response
                (gn21EndpointVectorPolicy
                  (gn21UpdateEndpoint endpoints
                    (gn21Lemma5GapUpperIndex i) x)) x))
    (hright_top_witness :
      shape = .strictlyQuasiConvex →
        ∀ (extra : Nat) (endpoints : GN21Lemma5EndpointVector extra),
          Rhat sigma - margin ≤
              Rhat (gn21EndpointVectorPolicy endpoints) →
            ∀ (j : Fin extra),
              endpoints (gn21Lemma5GapLowerIndex j) = ∞ →
                ∃ rightValue : ℝ,
                  endpoints (gn21Lemma5GapUpperIndex j) <
                      ENNReal.ofReal rightValue ∧
                    response
                      (gn21EndpointVectorPolicy endpoints) rightValue ≤ 0)
    (hopen_interval_upper_derivative :
      GN21Lemma5ComponentUpperDerivativeCondition Rhat response)
    (hopen_interval_lower_derivative :
      GN21Lemma5ComponentLowerDerivativeCondition Rhat response)
    (hopen_interval_lower_right_derivative :
      GN21Lemma5ComponentLowerRightDerivativeCondition Rhat response)
    (hopen_tail_lower_derivative :
      GN21Lemma5ComponentTailLowerDerivativeCondition Rhat response)
    (hopen_split_lower_derivative :
      ∀ (policy : TripPolicy) (pivot : ℝ),
        IsOpen policy → policy ⊆ acceptAllPolicy →
          pivot ∈ policy →
            ∃ derivativeValue : ℝ,
              HasDerivAt
                (fun cutoff =>
                  Rhat (gn21InteriorSplitLowerPolicy policy pivot cutoff))
                derivativeValue pivot ∧
              sameStrictSign derivativeValue (-response policy pivot)) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm shape policy ∧
        Rhat sigma ≤ Rhat policy ∧
        (¬ lemma5SourcePolicyFormAlmostEverywhere mu shape sigma →
          Rhat sigma < Rhat policy) := by
  cases shape with
  | positive =>
      exact exists_positive_source_form_reward_ge_and_gt_unless_ae_open
        mu Rhat response hsigma_open hsigma_subset hempty_lt_sigma hmargin
        hcontinuous hendpoint_continuous (hresponse_positive rfl)
        hupper_derivative hpositive_path_continuous
        hpositive_path_derivative hopen_interval_upper_derivative
        hopen_tail_lower_derivative
  | strictlyIncreasing =>
      exact exists_strictlyIncreasing_source_form_reward_ge_and_gt_unless_ae_open
        mu Rhat response hsigma_open hsigma_subset hempty_lt_sigma hmargin
        hcontinuous hendpoint_continuous (hresponse_increasing rfl)
        hupper_derivative
        (fun extra endpoints i _ hvalue =>
          hlower_derivative extra endpoints (Fin.castSucc i) hvalue)
        (fun extra endpoints i hvalue =>
          hlower_right_derivative extra endpoints (Fin.castSucc i) hvalue)
        hopen_interval_upper_derivative hopen_interval_lower_derivative
        hopen_interval_lower_right_derivative
  | strictlyDecreasing =>
      exact exists_strictlyDecreasing_source_form_reward_ge_and_gt_unless_ae_open
        mu Rhat response hsigma_open hsigma_subset hempty_lt_sigma hmargin
        hcontinuous hendpoint_continuous (hresponse_decreasing rfl)
        hupper_derivative
        (fun extra endpoints i value hvalue => by
          simpa only [gn21Lemma5GapLowerIndex_eq_lower_succ] using
            hlower_derivative extra endpoints i.succ hvalue)
        hupper_right_derivative hopen_interval_upper_derivative
        hopen_interval_lower_derivative hopen_tail_lower_derivative
        hopen_split_lower_derivative
  | strictlyQuasiConvex =>
      exact exists_strictlyQuasiConvex_source_form_reward_ge_and_gt_unless_ae_open
        mu Rhat response hsigma_open hsigma_subset hempty_lt_sigma hmargin
        hcontinuous hendpoint_continuous (hresponse_quasiConvex rfl)
        (hzero_quasiConvex rfl) hupper_derivative
        (fun extra endpoints i value hvalue => by
          simpa only [gn21Lemma5GapLowerIndex_eq_lower_succ] using
            hlower_derivative extra endpoints i.succ hvalue)
        hupper_right_derivative (hright_top_witness rfl)
        hopen_interval_upper_derivative hopen_interval_lower_derivative
        hopen_split_lower_derivative
  | strictlyQuasiConcave =>
      exact exists_strictlyQuasiConcave_source_form_reward_ge_and_gt_unless_ae_open
        mu Rhat response hsigma_open hsigma_subset hempty_lt_sigma hmargin
        hcontinuous hendpoint_continuous (hresponse_quasiConcave rfl)
        (hzero_quasiConcave rfl) hupper_derivative hlower_derivative
        (fun extra endpoints i hvalue =>
          hlower_right_derivative extra endpoints (Fin.castSucc i) hvalue)
        hopen_interval_upper_derivative hopen_split_lower_derivative

/-! ## Theorem 4 assembly without optimizer premises -/

/-- Two-state policy assembled from its non-surge and surge components. -/
def gn21TwoStatePolicy (nonsurge surge : TripPolicy) : Fin 2 → TripPolicy :=
  ![nonsurge, surge]

@[simp] theorem gn21TwoStatePolicy_zero (nonsurge surge : TripPolicy) :
    gn21TwoStatePolicy nonsurge surge 0 = nonsurge := by
  rfl

@[simp] theorem gn21TwoStatePolicy_one (nonsurge surge : TripPolicy) :
    gn21TwoStatePolicy nonsurge surge 1 = surge := by
  rfl

/-- Product of the two compact canonical endpoint families used in Theorem 4. -/
abbrev GN21Lemma5CanonicalPairEndpointVector
    (shape : Fin 2 → Lemma5DerivativeShape) :=
  GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 0)) ×
    GN21Lemma5EndpointVector (gn21Lemma5CanonicalExtra (shape 1))

/-- Canonical endpoint-pair domain for two selected Lemma 5 rows. -/
def gn21Lemma5CanonicalPairEndpointDomain
    (shape : Fin 2 → Lemma5DerivativeShape) :
    Set (GN21Lemma5CanonicalPairEndpointVector shape) :=
  gn21Lemma5CanonicalEndpointDomain (shape 0) ×ˢ
    gn21Lemma5CanonicalEndpointDomain (shape 1)

/-- Dynamic policy represented by a pair of canonical endpoint vectors. -/
def gn21Lemma5CanonicalPairPolicy
    (shape : Fin 2 → Lemma5DerivativeShape)
    (endpoints : GN21Lemma5CanonicalPairEndpointVector shape) :
    Fin 2 → TripPolicy :=
  gn21TwoStatePolicy
    (gn21EndpointVectorPolicy endpoints.1)
    (gn21EndpointVectorPolicy endpoints.2)

theorem isCompact_gn21Lemma5CanonicalPairEndpointDomain
    (shape : Fin 2 → Lemma5DerivativeShape) :
    IsCompact (gn21Lemma5CanonicalPairEndpointDomain shape) := by
  exact
    (isCompact_gn21Lemma5CanonicalEndpointDomain (shape 0)).prod
      (isCompact_gn21Lemma5CanonicalEndpointDomain (shape 1))

theorem gn21Lemma5CanonicalPairEndpointDomain_nonempty
    (shape : Fin 2 → Lemma5DerivativeShape) :
    (gn21Lemma5CanonicalPairEndpointDomain shape).Nonempty := by
  exact
    (gn21Lemma5CanonicalEndpointDomain_nonempty (shape 0)).prod
      (gn21Lemma5CanonicalEndpointDomain_nonempty (shape 1))

theorem gn21Lemma5CanonicalPairPolicy_feasibleOpen
    (shape : Fin 2 → Lemma5DerivativeShape)
    (endpoints : GN21Lemma5CanonicalPairEndpointVector shape) :
    dynamicFeasibleOpenPolicy
      (gn21Lemma5CanonicalPairPolicy shape endpoints) := by
  intro i
  fin_cases i
  · exact ⟨gn21EndpointVectorPolicy_subset_acceptAll _,
      gn21EndpointVectorPolicy_open _⟩
  · exact ⟨gn21EndpointVectorPolicy_subset_acceptAll _,
      gn21EndpointVectorPolicy_open _⟩

/--
Extend the source Lemma 5 conclusion to a starting policy whose reward may be
no larger than the empty-policy reward.  The additional nontrivial seed is the
missing baseline condition needed for that case; it is not a supplied policy
form or optimizer.
-/
theorem exists_source_form_reward_ge_and_gt_unless_ae_open_of_nontrivial
    (mu : Measure TripLength)
    (Rhat : SingleStateReward)
    (shape : Lemma5DerivativeShape)
    (hnontrivial :
      ∃ seed : TripPolicy,
        IsOpen seed ∧ seed ⊆ acceptAllPolicy ∧
          Rhat ∅ < Rhat seed)
    (hlemma5 :
      ∀ {source : TripPolicy},
        IsOpen source → source ⊆ acceptAllPolicy →
          Rhat ∅ < Rhat source →
            ∃ policy : TripPolicy,
              lemma5SourcePolicyForm shape policy ∧
                Rhat source ≤ Rhat policy ∧
                (¬ lemma5SourcePolicyFormAlmostEverywhere mu shape source →
                  Rhat source < Rhat policy))
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy) :
    ∃ policy : TripPolicy,
      lemma5SourcePolicyForm shape policy ∧
        Rhat sigma ≤ Rhat policy ∧
        (¬ lemma5SourcePolicyFormAlmostEverywhere mu shape sigma →
          Rhat sigma < Rhat policy) := by
  by_cases hempty_lt_sigma : Rhat ∅ < Rhat sigma
  · exact hlemma5 hsigma_open hsigma_subset hempty_lt_sigma
  · rcases hnontrivial with
      ⟨seed, hseed_open, hseed_subset, hempty_lt_seed⟩
    rcases hlemma5 hseed_open hseed_subset hempty_lt_seed with
      ⟨policy, hform, hseed_le, _hstrict⟩
    have hsigma_lt : Rhat sigma < Rhat policy :=
      (le_of_not_gt hempty_lt_sigma).trans_lt
        (hempty_lt_seed.trans_le hseed_le)
    exact ⟨policy, hform, le_of_lt hsigma_lt, fun _ => hsigma_lt⟩

/--
Sequentially apply a total one-state Lemma 5 replacement in state 0 and then
state 1.  This is an internal assembly lemma: the final source theorem supplies
`hlemma5` by the direct variational theorem above.
-/
theorem exists_two_state_source_form_replacement_of_statewise_lemma5
    (mu : Fin 2 → Measure TripLength)
    (R : DynamicReward)
    (shape : Fin 2 → Lemma5DerivativeShape)
    (hnontrivial :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ i : Fin 2,
            ∃ seed : TripPolicy,
              IsOpen seed ∧ seed ⊆ acceptAllPolicy ∧
                R (Function.update rho i ∅) <
                  R (Function.update rho i seed))
    (hlemma5 :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) {source : TripPolicy},
            IsOpen source → source ⊆ acceptAllPolicy →
              R (Function.update rho i ∅) <
                  R (Function.update rho i source) →
                ∃ policy : TripPolicy,
                  lemma5SourcePolicyForm (shape i) policy ∧
                    R (Function.update rho i source) ≤
                      R (Function.update rho i policy) ∧
                    (¬ lemma5SourcePolicyFormAlmostEverywhere
                        (mu i) (shape i) source →
                      R (Function.update rho i source) <
                        R (Function.update rho i policy)))
    (rho : Fin 2 → TripPolicy)
    (hrho : dynamicFeasibleOpenPolicy rho) :
    ∃ tau : Fin 2 → TripPolicy,
      dynamicFeasibleOpenPolicy tau ∧
        lemma5SourcePolicyForm (shape 0) (tau 0) ∧
        lemma5SourcePolicyForm (shape 1) (tau 1) ∧
        R rho ≤ R tau ∧
        ((¬ lemma5SourcePolicyFormAlmostEverywhere
              (mu 0) (shape 0) (rho 0)) ∨
            (¬ lemma5SourcePolicyFormAlmostEverywhere
              (mu 1) (shape 1) (rho 1)) →
          R rho < R tau) := by
  let Rhat0 : SingleStateReward :=
    fun policy => R (Function.update rho 0 policy)
  have hnontrivial0 :
      ∃ seed : TripPolicy,
        IsOpen seed ∧ seed ⊆ acceptAllPolicy ∧
          Rhat0 ∅ < Rhat0 seed := by
    simpa [Rhat0] using hnontrivial rho hrho 0
  have hlemma50 :
      ∀ {source : TripPolicy},
        IsOpen source → source ⊆ acceptAllPolicy →
          Rhat0 ∅ < Rhat0 source →
            ∃ policy : TripPolicy,
              lemma5SourcePolicyForm (shape 0) policy ∧
                Rhat0 source ≤ Rhat0 policy ∧
                (¬ lemma5SourcePolicyFormAlmostEverywhere
                    (mu 0) (shape 0) source →
                  Rhat0 source < Rhat0 policy) := by
    intro source hsource_open hsource_subset hsource_reward
    simpa [Rhat0] using
      hlemma5 rho hrho 0 hsource_open hsource_subset hsource_reward
  rcases exists_source_form_reward_ge_and_gt_unless_ae_open_of_nontrivial
      (mu 0) Rhat0 (shape 0) hnontrivial0 hlemma50
      (hrho 0).2 (hrho 0).1 with
    ⟨policy0, hform0, hreward0, hstrict0⟩
  let rho0 : Fin 2 → TripPolicy := Function.update rho 0 policy0
  have hrho0 : dynamicFeasibleOpenPolicy rho0 := by
    intro i
    fin_cases i
    · simpa [rho0] using
        ⟨lemma5SourcePolicyForm_subset_acceptAll hform0,
          lemma5SourcePolicyForm_open hform0⟩
    · simpa [rho0] using hrho 1
  let Rhat1 : SingleStateReward :=
    fun policy => R (Function.update rho0 1 policy)
  have hnontrivial1 :
      ∃ seed : TripPolicy,
        IsOpen seed ∧ seed ⊆ acceptAllPolicy ∧
          Rhat1 ∅ < Rhat1 seed := by
    simpa [Rhat1] using hnontrivial rho0 hrho0 1
  have hlemma51 :
      ∀ {source : TripPolicy},
        IsOpen source → source ⊆ acceptAllPolicy →
          Rhat1 ∅ < Rhat1 source →
            ∃ policy : TripPolicy,
              lemma5SourcePolicyForm (shape 1) policy ∧
                Rhat1 source ≤ Rhat1 policy ∧
                (¬ lemma5SourcePolicyFormAlmostEverywhere
                    (mu 1) (shape 1) source →
                  Rhat1 source < Rhat1 policy) := by
    intro source hsource_open hsource_subset hsource_reward
    simpa [Rhat1] using
      hlemma5 rho0 hrho0 1 hsource_open hsource_subset hsource_reward
  rcases exists_source_form_reward_ge_and_gt_unless_ae_open_of_nontrivial
      (mu 1) Rhat1 (shape 1) hnontrivial1 hlemma51
      (hrho0 1).2 (hrho0 1).1 with
    ⟨policy1, hform1, hreward1, hstrict1⟩
  let tau : Fin 2 → TripPolicy := Function.update rho0 1 policy1
  have htau : dynamicFeasibleOpenPolicy tau := by
    intro i
    fin_cases i
    · simpa [tau] using hrho0 0
    · simpa [tau] using
        ⟨lemma5SourcePolicyForm_subset_acceptAll hform1,
          lemma5SourcePolicyForm_open hform1⟩
  have hrho_le_rho0 : R rho ≤ R rho0 := by
    simpa [Rhat0, rho0, Function.update_eq_self] using hreward0
  have hrho0_le_tau : R rho0 ≤ R tau := by
    simpa [Rhat1, tau, Function.update_eq_self] using hreward1
  refine ⟨tau, htau, ?_, ?_, hrho_le_rho0.trans hrho0_le_tau, ?_⟩
  · simpa [tau, rho0] using hform0
  · simpa [tau] using hform1
  · intro hnot
    rcases hnot with hnot0 | hnot1
    · have hlt0 : R rho < R rho0 := by
        simpa [Rhat0, rho0, Function.update_eq_self] using hstrict0 hnot0
      exact hlt0.trans_le hrho0_le_tau
    · have hnot1' :
          ¬ lemma5SourcePolicyFormAlmostEverywhere
            (mu 1) (shape 1) (rho0 1) := by
        simpa [rho0] using hnot1
      have hlt1 : R rho0 < R tau := by
        simpa [Rhat1, tau, Function.update_eq_self] using hstrict1 hnot1'
      exact hrho_le_rho0.trans_lt hlt1

/--
Compact pair maximization plus strict statewise replacement derives both
optimizer existence and the all-optima a.e. policy-form clause.  The theorem
does not assume an optimizer or a bracket around one.
-/
theorem exists_dynamicOpenOptimal_and_all_optima_source_forms_of_replacements
    (mu : Fin 2 → Measure TripLength)
    (R : DynamicReward)
    (shape : Fin 2 → Lemma5DerivativeShape)
    (hpair_continuous :
      ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          R (gn21Lemma5CanonicalPairPolicy shape endpoints))
        (gn21Lemma5CanonicalPairEndpointDomain shape))
    (hreplace :
      ∀ rho : Fin 2 → TripPolicy,
        dynamicFeasibleOpenPolicy rho →
          ∃ tau : Fin 2 → TripPolicy,
            dynamicFeasibleOpenPolicy tau ∧
              lemma5SourcePolicyForm (shape 0) (tau 0) ∧
              lemma5SourcePolicyForm (shape 1) (tau 1) ∧
              R rho ≤ R tau ∧
              ((¬ lemma5SourcePolicyFormAlmostEverywhere
                    (mu 0) (shape 0) (rho 0)) ∨
                  (¬ lemma5SourcePolicyFormAlmostEverywhere
                    (mu 1) (shape 1) (rho 1)) →
                R rho < R tau)) :
    (∃ rho : Fin 2 → TripPolicy,
      dynamicOpenOptimal R rho ∧
        lemma5SourcePolicyForm (shape 0) (rho 0) ∧
        lemma5SourcePolicyForm (shape 1) (rho 1)) ∧
      ∀ rho : Fin 2 → TripPolicy,
        dynamicOpenOptimal R rho →
          lemma5SourcePolicyFormAlmostEverywhere
              (mu 0) (shape 0) (rho 0) ∧
            lemma5SourcePolicyFormAlmostEverywhere
              (mu 1) (shape 1) (rho 1) := by
  rcases
      (isCompact_gn21Lemma5CanonicalPairEndpointDomain shape).exists_isMaxOn
        (gn21Lemma5CanonicalPairEndpointDomain_nonempty shape)
        hpair_continuous with
    ⟨rawEndpoints, hraw_domain, hraw_max⟩
  rw [isMaxOn_iff] at hraw_max
  let rawPolicy := gn21Lemma5CanonicalPairPolicy shape rawEndpoints
  have hraw_feasible : dynamicFeasibleOpenPolicy rawPolicy :=
    gn21Lemma5CanonicalPairPolicy_feasibleOpen shape rawEndpoints
  rcases hreplace rawPolicy hraw_feasible with
    ⟨rhoStar, hrhoStar_feasible, hform0, hform1,
      hraw_le_star, _hraw_strict⟩
  rcases exists_canonicalEndpointVector_of_lemma5SourcePolicyForm hform0 with
    ⟨endpoints0, hendpoints0, hpolicy0⟩
  rcases exists_canonicalEndpointVector_of_lemma5SourcePolicyForm hform1 with
    ⟨endpoints1, hendpoints1, hpolicy1⟩
  let starEndpoints : GN21Lemma5CanonicalPairEndpointVector shape :=
    (endpoints0, endpoints1)
  have hstar_domain :
      starEndpoints ∈ gn21Lemma5CanonicalPairEndpointDomain shape :=
    ⟨hendpoints0, hendpoints1⟩
  have hstar_policy :
      gn21Lemma5CanonicalPairPolicy shape starEndpoints = rhoStar := by
    funext i
    fin_cases i
    · simpa [starEndpoints, gn21Lemma5CanonicalPairPolicy] using hpolicy0
    · simpa [starEndpoints, gn21Lemma5CanonicalPairPolicy] using hpolicy1
  have hstar_le_raw : R rhoStar ≤ R rawPolicy := by
    simpa [rawPolicy, hstar_policy] using hraw_max starEndpoints hstar_domain
  have hstar_eq_raw : R rhoStar = R rawPolicy :=
    le_antisymm hstar_le_raw hraw_le_star
  have hrhoStar_optimal : dynamicOpenOptimal R rhoStar := by
    refine ⟨hrhoStar_feasible, ?_⟩
    intro rho hrho
    rcases hreplace rho hrho with
      ⟨tau, _htau_feasible, htau_form0, htau_form1,
        hrho_le_tau, _htau_strict⟩
    rcases exists_canonicalEndpointVector_of_lemma5SourcePolicyForm
        htau_form0 with ⟨tauEndpoints0, htauEndpoints0, htauPolicy0⟩
    rcases exists_canonicalEndpointVector_of_lemma5SourcePolicyForm
        htau_form1 with ⟨tauEndpoints1, htauEndpoints1, htauPolicy1⟩
    let tauEndpoints : GN21Lemma5CanonicalPairEndpointVector shape :=
      (tauEndpoints0, tauEndpoints1)
    have htau_domain :
        tauEndpoints ∈ gn21Lemma5CanonicalPairEndpointDomain shape :=
      ⟨htauEndpoints0, htauEndpoints1⟩
    have htau_policy :
        gn21Lemma5CanonicalPairPolicy shape tauEndpoints = tau := by
      funext i
      fin_cases i
      · simpa [tauEndpoints, gn21Lemma5CanonicalPairPolicy] using htauPolicy0
      · simpa [tauEndpoints, gn21Lemma5CanonicalPairPolicy] using htauPolicy1
    have htau_le_raw : R tau ≤ R rawPolicy := by
      simpa [rawPolicy, htau_policy] using hraw_max tauEndpoints htau_domain
    rw [hstar_eq_raw]
    exact hrho_le_tau.trans htau_le_raw
  refine ⟨⟨rhoStar, hrhoStar_optimal, hform0, hform1⟩, ?_⟩
  intro rho hrho
  by_cases hform0_ae :
      lemma5SourcePolicyFormAlmostEverywhere
        (mu 0) (shape 0) (rho 0)
  · by_cases hform1_ae :
        lemma5SourcePolicyFormAlmostEverywhere
          (mu 1) (shape 1) (rho 1)
    · exact ⟨hform0_ae, hform1_ae⟩
    · rcases hreplace rho hrho.1 with
        ⟨tau, htau_feasible, _htau_form0, _htau_form1,
          _hrho_le_tau, hstrict⟩
      have hrho_lt_tau : R rho < R tau := hstrict (Or.inr hform1_ae)
      exact False.elim ((not_lt_of_ge (hrho.2 tau htau_feasible)) hrho_lt_tau)
  · rcases hreplace rho hrho.1 with
      ⟨tau, htau_feasible, _htau_form0, _htau_form1,
        _hrho_le_tau, hstrict⟩
    have hrho_lt_tau : R rho < R tau := hstrict (Or.inl hform0_ae)
    exact False.elim ((not_lt_of_ge (hrho.2 tau htau_feasible)) hrho_lt_tau)

/--
Audited Theorem 4 statement (`source.txt:3859-3943`) on the source open-policy
domain.  The two displayed price-case disjunctions preserve all six printed
case-to-form correspondences; the conclusion uses the endpoint-complete Lemma
5 forms, so infinite endpoints occur exactly in the rows where the source
allows them.

Two gaps in the printed proof are explicit premises here.  First, Step A does
not derive a reward-gap/response-shape condition uniformly over every policy
visited by the subsequent variations.  The `hresponse_*` premises state that
uniform requirement directly.  Second, Theorem 4 applies Lemma 5 to arbitrary
open policies although Lemma 5 assumes reward strictly above the empty policy;
`hnontrivial` supplies a better open seed for the complementary case.  The
remaining endpoint premises are derivative facts, not optimizer, bracket, or
policy-form conclusions.  From them Lean derives optimizer attainment and the
all-optima clause.
-/
theorem paper_theorem4_source_structural_policy_forms_open_corrected
    (mu : Fin 2 → Measure TripLength)
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    [(mu 0).InnerRegularCompactLTTop] [(mu 1).InnerRegularCompactLTTop]
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (R : DynamicReward)
    (hreward_model :
      R = gn21AggregateDynamicRewardFunctional
        mu arrival switch12 switch21 w)
    (shape : Fin 2 → Lemma5DerivativeShape)
    (response : Fin 2 → (Fin 2 → TripPolicy) → TripLength → ℝ)
    (margin : Fin 2 → (Fin 2 → TripPolicy) → TripPolicy → ℝ)
    (hnonsurge_price_case :
      (∃ m a : ℝ,
        0 ≤ a ∧ w 0 = affinePricing m a ∧
          shape 0 = .strictlyDecreasing) ∨
      (∃ m a : ℝ,
        0 < a ∧ w 0 = affinePricing m (-a) ∧
          shape 0 = .strictlyQuasiConcave) ∨
      ((∀ rho : Fin 2 → TripPolicy,
          dynamicFeasibleOpenPolicy rho →
            ∀ u : TripLength, 0 < u → 0 < response 0 rho u) ∧
        shape 0 = .positive))
    (hsurge_price_case :
      (∃ m a : ℝ,
        0 ≤ a ∧ w 1 = affinePricing m (-a) ∧
          shape 1 = .strictlyIncreasing) ∨
      (∃ m a : ℝ,
        0 < a ∧ w 1 = affinePricing m a ∧
          shape 1 = .strictlyQuasiConvex) ∨
      ((∀ rho : Fin 2 → TripPolicy,
          dynamicFeasibleOpenPolicy rho →
            ∀ u : TripLength, 0 < u → 0 < response 1 rho u) ∧
        shape 1 = .positive))
    (hpair_continuous :
      ContinuousOn
        (fun endpoints : GN21Lemma5CanonicalPairEndpointVector shape =>
          R (gn21Lemma5CanonicalPairPolicy shape endpoints))
        (gn21Lemma5CanonicalPairEndpointDomain shape))
    (hnontrivial :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ i : Fin 2,
            ∃ seed : TripPolicy,
              IsOpen seed ∧ seed ⊆ acceptAllPolicy ∧
                R (Function.update rho i ∅) <
                  R (Function.update rho i seed))
    (hmargin_pos :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            IsOpen source → source ⊆ acceptAllPolicy →
              R (Function.update rho i ∅) <
                  R (Function.update rho i source) →
                0 < margin i rho source)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy => R (Function.update rho i policy)) tau)
    (hendpoint_continuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat),
            ContinuousOn
              (fun endpoints : GN21Lemma5EndpointVector extra =>
                R (Function.update rho i
                  (gn21EndpointVectorPolicy endpoints)))
              (gn21Lemma5EndpointDomain (shape i) extra))
    (hresponse_positive :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .positive →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  ∀ u : TripLength, 0 < u →
                    0 < response i (Function.update rho i tau) u)
    (hresponse_increasing :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyIncreasing →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  StrictMonoOn
                    (response i (Function.update rho i tau)) (Set.Ici 0))
    (hresponse_decreasing :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyDecreasing →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  StrictAntiOn
                    (response i (Function.update rho i tau)) (Set.Ici 0))
    (hresponse_quasiConvex :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConvex →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  strictQuasiConvexOnPositive
                    (response i (Function.update rho i tau)))
    (hzero_quasiConvex :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConvex →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  ∀ {middleLower middleUpper right : ℝ},
                    0 < middleLower → middleLower < middleUpper →
                      middleUpper < right →
                        response i (Function.update rho i tau) middleLower <
                          max
                            (response i (Function.update rho i tau) 0)
                            (response i (Function.update rho i tau) right))
    (hresponse_quasiConcave :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConcave →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  strictQuasiConcaveOnPositive
                    (response i (Function.update rho i tau)))
    (hzero_quasiConcave :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConcave →
              ∀ tau : TripPolicy,
                R (Function.update rho i source) - margin i rho source ≤
                    R (Function.update rho i tau) →
                  ∀ {middle right : ℝ},
                    0 < middle → middle < right →
                      min
                          (response i (Function.update rho i tau) 0)
                          (response i (Function.update rho i tau) right) <
                        response i (Function.update rho i tau) middle)
    (hupper_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat)
            (endpoints : GN21Lemma5EndpointVector extra)
            (gap : Fin extra) {value : ℝ},
              endpoints (gn21Lemma5GapUpperIndex gap) =
                  ENNReal.ofReal value →
                ∃ derivativeValue : ℝ,
                  HasDerivAt
                    (fun x =>
                      R (Function.update rho i
                        (gn21EndpointVectorPolicy
                          (gn21UpdateEndpoint endpoints
                            (gn21Lemma5GapUpperIndex gap) x))))
                    derivativeValue value ∧
                  sameStrictSign derivativeValue
                    (response i
                      (Function.update rho i
                        (gn21EndpointVectorPolicy endpoints)) value))
    (hlower_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat)
            (endpoints : GN21Lemma5EndpointVector extra)
            (slot : Fin (extra + 1)) {value : ℝ},
              endpoints (gn21LowerEndpointIndex slot) =
                  ENNReal.ofReal value →
                ∃ derivativeValue : ℝ,
                  HasDerivAt
                    (fun x =>
                      R (Function.update rho i
                        (gn21EndpointVectorPolicy
                          (gn21UpdateEndpoint endpoints
                            (gn21LowerEndpointIndex slot) x))))
                    derivativeValue value ∧
                  sameStrictSign derivativeValue
                    (-response i
                      (Function.update rho i
                        (gn21EndpointVectorPolicy endpoints)) value))
    (hupper_right_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat)
            (endpoints : GN21Lemma5EndpointVector extra)
            (gap : Fin extra),
              endpoints (gn21Lemma5GapUpperIndex gap) = 0 →
                ∃ derivativeValue : ℝ,
                  HasDerivWithinAt
                      (fun x =>
                        R (Function.update rho i
                          (gn21EndpointVectorPolicy
                            (gn21UpdateEndpoint endpoints
                              (gn21Lemma5GapUpperIndex gap) x))))
                      derivativeValue (Set.Ici 0) 0 ∧
                    sameStrictSign derivativeValue
                      (response i
                        (Function.update rho i
                          (gn21EndpointVectorPolicy endpoints)) 0))
    (hlower_right_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat)
            (endpoints : GN21Lemma5EndpointVector extra)
            (slot : Fin (extra + 1)),
              endpoints (gn21LowerEndpointIndex slot) = 0 →
                ∃ derivativeValue : ℝ,
                  HasDerivWithinAt
                      (fun x =>
                        R (Function.update rho i
                          (gn21EndpointVectorPolicy
                            (gn21UpdateEndpoint endpoints
                              (gn21LowerEndpointIndex slot) x))))
                      derivativeValue (Set.Ici 0) 0 ∧
                    sameStrictSign derivativeValue
                      (-response i
                        (Function.update rho i
                          (gn21EndpointVectorPolicy endpoints)) 0))
    (hpositive_path_continuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat)
            (endpoints : GN21Lemma5EndpointVector extra),
              endpoints ∈ gn21Lemma5EndpointDomain .positive extra →
                ∀ (gap : Fin extra) (upper : ℝ), 0 < upper →
                  ContinuousOn
                    (fun x =>
                      R (Function.update rho i
                        (gn21EndpointVectorPolicy
                          (gn21UpdateEndpoint endpoints
                            (gn21Lemma5GapUpperIndex gap) x))))
                    (Set.Icc 0 upper))
    (hpositive_path_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (extra : Nat)
            (endpoints : GN21Lemma5EndpointVector extra)
            (gap : Fin extra) (upper x : ℝ),
              x ∈ Set.Ioo 0 upper →
                ∃ derivativeValue : ℝ,
                  HasDerivAt
                    (fun y =>
                      R (Function.update rho i
                        (gn21EndpointVectorPolicy
                          (gn21UpdateEndpoint endpoints
                            (gn21Lemma5GapUpperIndex gap) y))))
                    derivativeValue x ∧
                  sameStrictSign derivativeValue
                    (response i
                      (Function.update rho i
                        (gn21EndpointVectorPolicy
                          (gn21UpdateEndpoint endpoints
                            (gn21Lemma5GapUpperIndex gap) x))) x))
    (hright_top_witness :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (source : TripPolicy),
            shape i = .strictlyQuasiConvex →
              ∀ (extra : Nat)
                (endpoints : GN21Lemma5EndpointVector extra),
                  R (Function.update rho i source) - margin i rho source ≤
                      R (Function.update rho i
                        (gn21EndpointVectorPolicy endpoints)) →
                    ∀ gap : Fin extra,
                      endpoints (gn21Lemma5GapLowerIndex gap) = ∞ →
                        ∃ rightValue : ℝ,
                          endpoints (gn21Lemma5GapUpperIndex gap) <
                              ENNReal.ofReal rightValue ∧
                            response i
                              (Function.update rho i
                                (gn21EndpointVectorPolicy endpoints))
                              rightValue ≤ 0)
    (hopen_interval_upper_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (context : TripPolicy) (lower upper : ℝ),
            0 ≤ lower → lower < upper →
              ∃ derivativeValue : ℝ,
                HasDerivAt
                  (fun x =>
                    R (Function.update rho i
                      (context ∪ Set.Ioo lower x)))
                  derivativeValue upper ∧
                sameStrictSign derivativeValue
                  (response i
                    (Function.update rho i
                      (context ∪ Set.Ioo lower upper)) upper))
    (hopen_interval_lower_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (context : TripPolicy) (lower upper : ℝ),
            0 < lower → lower < upper →
              ∃ derivativeValue : ℝ,
                HasDerivAt
                  (fun x =>
                    R (Function.update rho i
                      (context ∪ Set.Ioo x upper)))
                  derivativeValue lower ∧
                sameStrictSign derivativeValue
                  (-response i
                    (Function.update rho i
                      (context ∪ Set.Ioo lower upper)) lower))
    (hopen_interval_lower_right_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (context : TripPolicy) (upper : ℝ),
            0 < upper →
              ∃ derivativeValue : ℝ,
                HasDerivWithinAt
                  (fun x =>
                    R (Function.update rho i
                      (context ∪ Set.Ioo x upper)))
                  derivativeValue (Set.Ici 0) 0 ∧
                sameStrictSign derivativeValue
                  (-response i
                    (Function.update rho i
                      (context ∪ Set.Ioo 0 upper)) 0))
    (hopen_tail_lower_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (context : TripPolicy) (lower : ℝ),
            0 < lower →
              ∃ derivativeValue : ℝ,
                HasDerivAt
                  (fun x =>
                    R (Function.update rho i (context ∪ Set.Ioi x)))
                  derivativeValue lower ∧
                sameStrictSign derivativeValue
                  (-response i
                    (Function.update rho i (context ∪ Set.Ioi lower)) lower))
    (hopen_split_lower_derivative :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (policy : TripPolicy) (pivot : ℝ),
            IsOpen policy → policy ⊆ acceptAllPolicy →
              pivot ∈ policy →
                ∃ derivativeValue : ℝ,
                  HasDerivAt
                    (fun cutoff =>
                      R (Function.update rho i
                        (gn21InteriorSplitLowerPolicy
                          policy pivot cutoff)))
                    derivativeValue pivot ∧
                  sameStrictSign derivativeValue
                    (-response i (Function.update rho i policy) pivot)) :
    (∃ rho : Fin 2 → TripPolicy,
      dynamicOpenOptimal
          (gn21AggregateDynamicRewardFunctional
            mu arrival switch12 switch21 w) rho ∧
        lemma5SourcePolicyForm (shape 0) (rho 0) ∧
        lemma5SourcePolicyForm (shape 1) (rho 1)) ∧
      ∀ rho : Fin 2 → TripPolicy,
        dynamicOpenOptimal
            (gn21AggregateDynamicRewardFunctional
              mu arrival switch12 switch21 w) rho →
          lemma5SourcePolicyFormAlmostEverywhere
              (mu 0) (shape 0) (rho 0) ∧
            lemma5SourcePolicyFormAlmostEverywhere
              (mu 1) (shape 1) (rho 1) := by
  subst R
  have hstatewise_lemma5 :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) {source : TripPolicy},
            IsOpen source → source ⊆ acceptAllPolicy →
              gn21AggregateDynamicRewardFunctional
                    mu arrival switch12 switch21 w
                    (Function.update rho i ∅) <
                  gn21AggregateDynamicRewardFunctional
                    mu arrival switch12 switch21 w
                    (Function.update rho i source) →
                ∃ policy : TripPolicy,
                  lemma5SourcePolicyForm (shape i) policy ∧
                    gn21AggregateDynamicRewardFunctional
                        mu arrival switch12 switch21 w
                        (Function.update rho i source) ≤
                      gn21AggregateDynamicRewardFunctional
                        mu arrival switch12 switch21 w
                        (Function.update rho i policy) ∧
                    (¬ lemma5SourcePolicyFormAlmostEverywhere
                        (mu i) (shape i) source →
                      gn21AggregateDynamicRewardFunctional
                          mu arrival switch12 switch21 w
                          (Function.update rho i source) <
                        gn21AggregateDynamicRewardFunctional
                          mu arrival switch12 switch21 w
                          (Function.update rho i policy)) := by
    intro rho hrho i source hsource_open hsource_subset hsource_reward
    have hmargin :=
      hmargin_pos rho hrho i source hsource_open hsource_subset hsource_reward
    fin_cases i
    · exact paper_lemma5_source_policy_replacement_open
        (mu 0)
        (fun policy =>
          gn21AggregateDynamicRewardFunctional
            mu arrival switch12 switch21 w
            (Function.update rho 0 policy))
        (fun policy => response 0 (Function.update rho 0 policy))
        (shape 0) hsource_open hsource_subset hsource_reward hmargin
        (hcontinuous rho hrho 0)
        (hendpoint_continuous rho hrho 0)
        (hresponse_positive rho hrho 0 source)
        (hresponse_increasing rho hrho 0 source)
        (hresponse_decreasing rho hrho 0 source)
        (hresponse_quasiConvex rho hrho 0 source)
        (hzero_quasiConvex rho hrho 0 source)
        (hresponse_quasiConcave rho hrho 0 source)
        (hzero_quasiConcave rho hrho 0 source)
        (hupper_derivative rho hrho 0)
        (hlower_derivative rho hrho 0)
        (hupper_right_derivative rho hrho 0)
        (hlower_right_derivative rho hrho 0)
        (hpositive_path_continuous rho hrho 0)
        (hpositive_path_derivative rho hrho 0)
        (hright_top_witness rho hrho 0 source)
        (gn21Lemma5ComponentUpperDerivativeCondition_of_arbitraryContext
          (fun policy =>
            gn21AggregateDynamicRewardFunctional
              mu arrival switch12 switch21 w (Function.update rho 0 policy))
          (fun policy => response 0 (Function.update rho 0 policy))
          (hopen_interval_upper_derivative rho hrho 0))
        (gn21Lemma5ComponentLowerDerivativeCondition_of_arbitraryContext
          (fun policy =>
            gn21AggregateDynamicRewardFunctional
              mu arrival switch12 switch21 w (Function.update rho 0 policy))
          (fun policy => response 0 (Function.update rho 0 policy))
          (hopen_interval_lower_derivative rho hrho 0))
        (gn21Lemma5ComponentLowerRightDerivativeCondition_of_arbitraryContext
          (fun policy =>
            gn21AggregateDynamicRewardFunctional
              mu arrival switch12 switch21 w (Function.update rho 0 policy))
          (fun policy => response 0 (Function.update rho 0 policy))
          (hopen_interval_lower_right_derivative rho hrho 0))
        (gn21Lemma5ComponentTailLowerDerivativeCondition_of_arbitraryContext
          (fun policy =>
            gn21AggregateDynamicRewardFunctional
              mu arrival switch12 switch21 w (Function.update rho 0 policy))
          (fun policy => response 0 (Function.update rho 0 policy))
          (hopen_tail_lower_derivative rho hrho 0))
        (hopen_split_lower_derivative rho hrho 0)
    · exact paper_lemma5_source_policy_replacement_open
        (mu 1)
        (fun policy =>
          gn21AggregateDynamicRewardFunctional
            mu arrival switch12 switch21 w
            (Function.update rho 1 policy))
        (fun policy => response 1 (Function.update rho 1 policy))
        (shape 1) hsource_open hsource_subset hsource_reward hmargin
        (hcontinuous rho hrho 1)
        (hendpoint_continuous rho hrho 1)
        (hresponse_positive rho hrho 1 source)
        (hresponse_increasing rho hrho 1 source)
        (hresponse_decreasing rho hrho 1 source)
        (hresponse_quasiConvex rho hrho 1 source)
        (hzero_quasiConvex rho hrho 1 source)
        (hresponse_quasiConcave rho hrho 1 source)
        (hzero_quasiConcave rho hrho 1 source)
        (hupper_derivative rho hrho 1)
        (hlower_derivative rho hrho 1)
        (hupper_right_derivative rho hrho 1)
        (hlower_right_derivative rho hrho 1)
        (hpositive_path_continuous rho hrho 1)
        (hpositive_path_derivative rho hrho 1)
        (hright_top_witness rho hrho 1 source)
        (gn21Lemma5ComponentUpperDerivativeCondition_of_arbitraryContext
          (fun policy =>
            gn21AggregateDynamicRewardFunctional
              mu arrival switch12 switch21 w (Function.update rho 1 policy))
          (fun policy => response 1 (Function.update rho 1 policy))
          (hopen_interval_upper_derivative rho hrho 1))
        (gn21Lemma5ComponentLowerDerivativeCondition_of_arbitraryContext
          (fun policy =>
            gn21AggregateDynamicRewardFunctional
              mu arrival switch12 switch21 w (Function.update rho 1 policy))
          (fun policy => response 1 (Function.update rho 1 policy))
          (hopen_interval_lower_derivative rho hrho 1))
        (gn21Lemma5ComponentLowerRightDerivativeCondition_of_arbitraryContext
          (fun policy =>
            gn21AggregateDynamicRewardFunctional
              mu arrival switch12 switch21 w (Function.update rho 1 policy))
          (fun policy => response 1 (Function.update rho 1 policy))
          (hopen_interval_lower_right_derivative rho hrho 1))
        (gn21Lemma5ComponentTailLowerDerivativeCondition_of_arbitraryContext
          (fun policy =>
            gn21AggregateDynamicRewardFunctional
              mu arrival switch12 switch21 w (Function.update rho 1 policy))
          (fun policy => response 1 (Function.update rho 1 policy))
          (hopen_tail_lower_derivative rho hrho 1))
        (hopen_split_lower_derivative rho hrho 1)
  have hreplace :=
    exists_two_state_source_form_replacement_of_statewise_lemma5
      mu
      (gn21AggregateDynamicRewardFunctional
        mu arrival switch12 switch21 w)
      shape hnontrivial hstatewise_lemma5
  exact
    exists_dynamicOpenOptimal_and_all_optima_source_forms_of_replacements
      mu
      (gn21AggregateDynamicRewardFunctional
        mu arrival switch12 switch21 w)
      shape hpair_continuous hreplace

end GN21DriverSurgePricing
