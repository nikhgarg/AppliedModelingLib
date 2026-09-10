import CGGG20SelectiveInformationAcquisition.ProofBridge

namespace CGGG20SelectiveInformationAcquisition

namespace PaperInterface

open MeasureTheory
open AppliedModelingLib.Decision
open AppliedModelingLib.Optimization
open AppliedModelingLib.Probability
open CGGG20SelectiveInformationAcquisition.ProofBridge
open scoped BigOperators
noncomputable section

/-! ## Main-text threshold result -/

/-- Source-facing semantic target for the definition `paper_main_text_groupwise_threshold_policy`. -/
def definition1_threshold_policySpec
    {Applicant Outcome Group : Type*} [Fintype Applicant] [Fintype Group]
    [MeasurableSpace Outcome]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    (threshold : Group → RealThreshold) (alpha : Group → ℝ)
    (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome) : Prop :=
  (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
      ∀ item outcome,
        match threshold (D.group item) with
        | .negInf => policy item outcome = 1
        | .finite t =>
            (t < D.posteriorUtility item outcome → policy item outcome = 1) ∧
            (D.posteriorUtility item outcome = t →
              policy item outcome = alpha (D.group item)) ∧
            (D.posteriorUtility item outcome < t → policy item outcome = 0)
        | .posInf => policy item outcome = 0

/-- Source-facing semantic target for `theorem1_threshold_policies_suffice`. -/
def legacy_theorem1_allocation_sliceSpec
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    [IsFiniteMeasure D.law]
    (actualUtility : Applicant → Outcome → ℝ)
    (hactual_utility_eq_posterior :
      ∀ policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
        MeasureGroupAllocationData.AllocationPolicyMeasurable policy →
          (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
            (∫ outcome,
              ∑ item : Applicant, policy item outcome * actualUtility item outcome ∂D.law) =
                D.expectedPosteriorUtility policy)
    (hactual_group_utility_eq_posterior :
      ∀ (g : Group) (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome),
        MeasureGroupAllocationData.AllocationPolicyMeasurable policy →
          (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
            (∫ outcome,
              ∑ item : Applicant,
                if D.group item = g then policy item outcome * actualUtility item outcome else 0 ∂D.law) =
                D.expectedGroupPosteriorUtility g policy)
    (c : ℝ) (hc : 0 < c) (hcost : ∀ item, D.allocCost item = c)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome)
    (horiginal :
      (∀ item outcome, 0 ≤ original item outcome ∧ original item outcome ≤ 1) ∧
        MeasureGroupAllocationData.AllocationPolicyMeasurable original ∧
          D.expectedCost original ≤ budget ∧
            (∀ g, diversityTarget g ≤
              ∫ outcome,
                ∑ item : Applicant,
                  if D.group item = g then
                    original item outcome * actualUtility item outcome else 0 ∂D.law) ∧
              ∀ other,
                ((∀ item outcome, 0 ≤ other item outcome ∧ other item outcome ≤ 1) ∧
                  MeasureGroupAllocationData.AllocationPolicyMeasurable other ∧
                    D.expectedCost other ≤ budget ∧
                      ∀ g, diversityTarget g ≤
                        ∫ outcome,
                          ∑ item : Applicant,
                            if D.group item = g then
                              other item outcome * actualUtility item outcome else 0 ∂D.law) →
                  (∫ outcome,
                    ∑ item : Applicant, other item outcome * actualUtility item outcome ∂D.law) ≤
                    ∫ outcome,
                      ∑ item : Applicant,
                        original item outcome * actualUtility item outcome ∂D.law) : Prop :=
  ∃ threshold : Group → RealThreshold,
    ∃ alpha : Group → ℝ,
      ∃ replacement : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
        paper_main_text_groupwise_threshold_policy D threshold alpha replacement ∧
          (∀ item outcome, 0 ≤ replacement item outcome ∧ replacement item outcome ≤ 1) ∧
            MeasureGroupAllocationData.AllocationPolicyMeasurable replacement ∧
              D.expectedCost replacement ≤ budget ∧
                (∀ g, diversityTarget g ≤
                  ∫ outcome,
                    ∑ item : Applicant,
                      if D.group item = g then
                        replacement item outcome * actualUtility item outcome else 0 ∂D.law) ∧
                  ∀ other,
                    ((∀ item outcome, 0 ≤ other item outcome ∧ other item outcome ≤ 1) ∧
                      MeasureGroupAllocationData.AllocationPolicyMeasurable other ∧
                        D.expectedCost other ≤ budget ∧
                          ∀ g, diversityTarget g ≤
                            ∫ outcome,
                              ∑ item : Applicant,
                                if D.group item = g then
                                  other item outcome * actualUtility item outcome else 0 ∂D.law) →
                      (∫ outcome,
                        ∑ item : Applicant,
                          other item outcome * actualUtility item outcome ∂D.law) ≤
                        ∫ outcome,
                          ∑ item : Applicant,
                            replacement item outcome * actualUtility item outcome ∂D.law

/--
Source-facing semantic target for Theorem 1.  It exposes the full policy-pair
optimization from Eqs. (def1)--(def3), rather than only its allocation slice.
-/
def theorem1_threshold_policies_sufficeSpec
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group]
    (D : paper_screening_allocation_data Applicant Outcome Group)
    (screeningCost : ℝ) (hscreenCost : ∀ item, D.screenCost item = screeningCost)
    (c : ℝ) (hc : 0 < c)
    (budget : ℝ) (hbudget_nonneg : 0 ≤ budget)
    (diversityTarget : Group → ℝ)
    (hdiversityTarget_nonneg : ∀ g, 0 ≤ diversityTarget g)
    (original : paper_screening_allocation_pair D)
    (hcost : ∀ item, D.allocCost item = c)
    (horiginal :
      letI : DecidableEq Group := Classical.decEq Group
      (ScreeningAllocationData.ScreeningPolicyBounds original.screening ∧
        MeasureGroupAllocationData.AllocationPolicyBounds original.allocation ∧
          MeasureGroupAllocationData.AllocationPolicyMeasurable original.allocation ∧
            D.screeningSpend original.screening +
                (D.post original.screening).expectedCost original.allocation ≤ budget ∧
              (∀ g, diversityTarget g ≤
                ∫ outcome,
                  ∑ item : Applicant,
                    if (D.post original.screening).group item = g then
                      original.allocation item outcome * D.actualUtility item outcome
                    else 0 ∂(D.post original.screening).law)) ∧
        ∀ other : paper_screening_allocation_pair D,
          (ScreeningAllocationData.ScreeningPolicyBounds other.screening ∧
            MeasureGroupAllocationData.AllocationPolicyBounds other.allocation ∧
              MeasureGroupAllocationData.AllocationPolicyMeasurable other.allocation ∧
                D.screeningSpend other.screening +
                    (D.post other.screening).expectedCost other.allocation ≤ budget ∧
                  (∀ g, diversityTarget g ≤
                    ∫ outcome,
                      ∑ item : Applicant,
                        if (D.post other.screening).group item = g then
                          other.allocation item outcome * D.actualUtility item outcome
                        else 0 ∂(D.post other.screening).law)) →
            (∫ outcome,
              ∑ item : Applicant,
                other.allocation item outcome * D.actualUtility item outcome ∂(D.post other.screening).law) ≤
              ∫ outcome,
                ∑ item : Applicant,
                  original.allocation item outcome * D.actualUtility item outcome ∂(D.post original.screening).law) : Prop :=
  letI : DecidableEq Group := Classical.decEq Group
  ∃ threshold : Group → RealThreshold,
    ∃ alpha : Group → ℝ,
      ∃ replacement : paper_screening_allocation_pair D,
        replacement.screening = original.screening ∧
          paper_main_text_groupwise_threshold_policy
            (D.post original.screening) threshold alpha replacement.allocation ∧
          ScreeningAllocationData.ScreeningPolicyBounds replacement.screening ∧
            MeasureGroupAllocationData.AllocationPolicyBounds replacement.allocation ∧
              MeasureGroupAllocationData.AllocationPolicyMeasurable replacement.allocation ∧
                D.screeningSpend original.screening +
                    (D.post original.screening).expectedCost replacement.allocation ≤ budget ∧
                  (∀ g, diversityTarget g ≤
                    ∫ outcome,
                      ∑ item : Applicant,
                        if (D.post original.screening).group item = g then
                          replacement.allocation item outcome * D.actualUtility item outcome
                        else 0 ∂(D.post original.screening).law) ∧
                    ∀ other : paper_screening_allocation_pair D,
                      (ScreeningAllocationData.ScreeningPolicyBounds other.screening ∧
                        MeasureGroupAllocationData.AllocationPolicyBounds other.allocation ∧
                          MeasureGroupAllocationData.AllocationPolicyMeasurable other.allocation ∧
                            D.screeningSpend other.screening +
                                (D.post other.screening).expectedCost other.allocation ≤ budget ∧
                              (∀ g, diversityTarget g ≤
                                ∫ outcome,
                                  ∑ item : Applicant,
                                    if (D.post other.screening).group item = g then
                                      other.allocation item outcome * D.actualUtility item outcome
                                    else 0 ∂(D.post other.screening).law)) →
                        (∫ outcome,
                          ∑ item : Applicant,
                            other.allocation item outcome * D.actualUtility item outcome ∂(D.post other.screening).law) ≤
                          ∫ outcome,
                            ∑ item : Applicant,
                              replacement.allocation item outcome * D.actualUtility item outcome ∂(D.post original.screening).law

/-! ## Main-text LP formulas -/

/-- Source-facing semantic target for `equation_obj_fixed_threshold_utility`. -/
def equation_obj_fixed_threshold_utilitySpec
    {Applicant Group : Type*} [Fintype Applicant]
    (D : paper_fixed_threshold_data Applicant Group) (p : Applicant → ℝ)
    (hprobability : D.screeningProbabilityBounds p) : Prop :=
  paper_equation_obj D p =
    ∑ i : Applicant, (D.q i * D.e i * p i + D.o i * D.mu i * (1 - p i))

/-- Source-facing semantic target for `equation_constr1_fixed_threshold_budget`. -/
def equation_constr1_fixed_threshold_budgetSpec
    {Applicant Group : Type*} [Fintype Applicant]
    (D : paper_fixed_threshold_data Applicant Group) (p : Applicant → ℝ)
    (hprobability : D.screeningProbabilityBounds p) : Prop :=
  paper_equation_constr1 D p ≤ D.budget ↔
    (∑ i : Applicant,
      (D.screenCost * p i + D.allocCost * D.q i * p i +
        D.allocCost * D.o i * (1 - p i))) ≤ D.budget

/-- Source-facing semantic target for `equation_constr2_fixed_threshold_diversity`. -/
def equation_constr2_fixed_threshold_diversitySpec
    {Applicant Group : Type*} [Fintype Applicant] [Fintype Group]
    (D : paper_fixed_threshold_data Applicant Group) (g : Group)
    (p : Applicant → ℝ) (hprobability : D.screeningProbabilityBounds p) : Prop :=
  letI : DecidableEq Group := Classical.decEq Group
  D.diversityTarget g ≤ paper_equation_constr2 D g p ↔
    D.diversityTarget g ≤
      ∑ i : Applicant, (if D.group i = g then
          D.q i * D.e i * p i + D.o i * D.mu i * (1 - p i)
        else 0)

/-! ## Appendix threshold results -/

/--
An allocation policy uses only the lender's complete observed posterior vector.
This is the paper's policy class `A(hat U)`: two outcomes with the same vector
of post-screening estimates induce the same allocation probability for every
applicant.
-/
def allocationPolicyUsesFullPosterior
    {Applicant Outcome : Type*}
    (posteriorUtility : Applicant → Outcome → ℝ)
    (policy : Applicant → Outcome → ℝ) : Prop :=
  ∀ item,
    Function.FactorsThrough (policy item)
      (fun outcome applicant => posteriorUtility applicant outcome)

/-- Source-facing semantic target for the definition `paper_cost_aware_groupwise_threshold_policy`. -/
def definition3_cost_aware_threshold_policySpec
    {Applicant Outcome Group : Type*} [Fintype Applicant] [Fintype Group]
    [MeasurableSpace Outcome]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (threshold : Group → paper_cost_aware_extended_threshold)
    (alpha : Group → ℝ)
    (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome) : Prop :=
  (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
      ∀ item outcome,
        match threshold (D.group item) with
        | .negInf => policy item outcome = 1
        | .finite t =>
            (t < D.posteriorUtility item outcome / D.allocCost item →
              policy item outcome = 1) ∧
            (D.posteriorUtility item outcome / D.allocCost item = t →
              policy item outcome = alpha (D.group item)) ∧
            (D.posteriorUtility item outcome / D.allocCost item < t →
              policy item outcome = 0)
        | .posInf => policy item outcome = 0

/-- Source-facing semantic target for the bundled definition `lemma1_cost_aware_threshold_non_domination`. -/
def lemma1_cost_aware_threshold_non_dominationSpec : Prop :=
  (∀ {Applicant Outcome : Type*} [Fintype Applicant]
    (D : ExpectedCostAwareData Applicant Outcome)
    (actualUtility : Applicant → Outcome → ℝ)
    (hactual_utility_eq_posterior :
      ∀ policy : ExpectedCostAwareData.AllocationPolicy Applicant Outcome,
        allocationPolicyUsesFullPosterior D.posteriorUtility policy →
        (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
          D.expect (fun outcome =>
            ∑ item : Applicant, policy item outcome * actualUtility item outcome) =
              D.expectedPosteriorUtility policy)
    (t alpha : ℝ)
    (threshold other : ExpectedCostAwareData.AllocationPolicy Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (ht : 0 < t)
    (hthreshold :
      0 ≤ alpha ∧ alpha ≤ 1 ∧
        ∀ item outcome,
          (t < D.posteriorUtility item outcome / D.allocCost item →
            threshold item outcome = 1) ∧
          (D.posteriorUtility item outcome / D.allocCost item = t →
            threshold item outcome = alpha) ∧
          (D.posteriorUtility item outcome / D.allocCost item < t →
            threshold item outcome = 0))
    (hother : ∀ item outcome, 0 ≤ other item outcome ∧ other item outcome ≤ 1)
    (hother_observed : allocationPolicyUsesFullPosterior D.posteriorUtility other)
    (hcost : D.expectedCost threshold = D.expectedCost other),
      D.expect (fun outcome =>
        ∑ item : Applicant, other item outcome * actualUtility item outcome) ≤
          D.expect (fun outcome =>
            ∑ item : Applicant, threshold item outcome * actualUtility item outcome)) ∧
  (∀ {Applicant Outcome : Type*} [Fintype Applicant]
    (D : ExpectedCostAwareData Applicant Outcome)
    (actualUtility : Applicant → Outcome → ℝ)
    (hactual_utility_eq_posterior :
      ∀ policy : ExpectedCostAwareData.AllocationPolicy Applicant Outcome,
        allocationPolicyUsesFullPosterior D.posteriorUtility policy →
        (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
          D.expect (fun outcome =>
            ∑ item : Applicant, policy item outcome * actualUtility item outcome) =
              D.expectedPosteriorUtility policy)
    (t alpha : ℝ)
    (threshold other : ExpectedCostAwareData.AllocationPolicy Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (ht : 0 < t)
    (hthreshold :
      0 ≤ alpha ∧ alpha ≤ 1 ∧
        ∀ item outcome,
          (t < D.posteriorUtility item outcome / D.allocCost item →
            threshold item outcome = 1) ∧
          (D.posteriorUtility item outcome / D.allocCost item = t →
            threshold item outcome = alpha) ∧
          (D.posteriorUtility item outcome / D.allocCost item < t →
            threshold item outcome = 0))
    (hother : ∀ item outcome, 0 ≤ other item outcome ∧ other item outcome ≤ 1)
    (hother_observed : allocationPolicyUsesFullPosterior D.posteriorUtility other)
    (hutility :
      D.expect (fun outcome =>
        ∑ item : Applicant, threshold item outcome * actualUtility item outcome) =
          D.expect (fun outcome =>
            ∑ item : Applicant, other item outcome * actualUtility item outcome)),
      D.expectedCost threshold ≤ D.expectedCost other)

/-- Source-facing semantic target for the bundled definition `lemma2_full_range_cost_aware_threshold_attainment`. -/
def lemma2_full_range_cost_aware_threshold_attainmentSpec : Prop :=
  (∀ {Applicant Outcome : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome]
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (actualUtility : Applicant → Outcome → ℝ)
    (hactual_utility_eq_posterior :
      ∀ policy : MeasureCostAwareData.AllocationPolicy Applicant Outcome,
        allocationPolicyUsesFullPosterior D.posteriorUtility policy →
        (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
          (∫ outcome,
            ∑ item : Applicant, policy item outcome * actualUtility item outcome ∂D.law) =
              D.expectedPosteriorUtility policy)
    (Upsilon : ℝ)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (hUpsilon_pos : 0 < Upsilon)
    (hachievable :
      ∃ original : MeasureCostAwareData.AllocationPolicy Applicant Outcome,
        MeasureCostAwareData.AllocationPolicyMeasurable original ∧
          allocationPolicyUsesFullPosterior D.posteriorUtility original ∧
          (∀ item outcome, 0 ≤ original item outcome ∧ original item outcome ≤ 1) ∧
            (∫ outcome,
              ∑ item : Applicant,
                original item outcome * actualUtility item outcome ∂D.law) = Upsilon),
      ∃ threshold : RealThreshold,
        ∃ alpha : ℝ,
          ∃ policy : MeasureCostAwareData.AllocationPolicy Applicant Outcome,
            0 ≤ alpha ∧ alpha ≤ 1 ∧
              (∀ item outcome,
                match threshold with
                | .negInf => policy item outcome = 1
                | .finite t =>
                    (t < D.posteriorUtility item outcome / D.allocCost item →
                      policy item outcome = 1) ∧
                    (D.posteriorUtility item outcome / D.allocCost item = t →
                      policy item outcome = alpha) ∧
                    (D.posteriorUtility item outcome / D.allocCost item < t →
                      policy item outcome = 0)
                | .posInf => policy item outcome = 0) ∧
                (∫ outcome,
                  ∑ item : Applicant,
                    policy item outcome * actualUtility item outcome ∂D.law) = Upsilon) ∧
    (∀ {Applicant Outcome : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome]
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (C : ℝ)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (hachievable :
      ∃ original : MeasureCostAwareData.AllocationPolicy Applicant Outcome,
        MeasureCostAwareData.AllocationPolicyMeasurable original ∧
          allocationPolicyUsesFullPosterior D.posteriorUtility original ∧
          (∀ item outcome, 0 ≤ original item outcome ∧ original item outcome ≤ 1) ∧
            D.expectedCost original = C),
      ∃ threshold : RealThreshold,
        ∃ alpha : ℝ,
          ∃ policy : MeasureCostAwareData.AllocationPolicy Applicant Outcome,
            0 ≤ alpha ∧ alpha ≤ 1 ∧
              (∀ item outcome,
                match threshold with
                | .negInf => policy item outcome = 1
                | .finite t =>
                    (t < D.posteriorUtility item outcome / D.allocCost item →
                      policy item outcome = 1) ∧
                    (D.posteriorUtility item outcome / D.allocCost item = t →
                      policy item outcome = alpha) ∧
                    (D.posteriorUtility item outcome / D.allocCost item < t →
                      policy item outcome = 0)
                | .posInf => policy item outcome = 0) ∧
                D.expectedCost policy = C)

/-- Source-facing semantic target for `appendix_theorem_cost_aware_threshold_policies_suffice`. -/
def legacy_appendix_theorem_allocation_sliceSpec
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    [IsFiniteMeasure D.law]
    (actualUtility : Applicant → Outcome → ℝ)
    (hactual_utility_eq_posterior :
      ∀ policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
        MeasureGroupAllocationData.AllocationPolicyMeasurable policy →
          (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
            (∫ outcome,
              ∑ item : Applicant, policy item outcome * actualUtility item outcome ∂D.law) =
                D.expectedPosteriorUtility policy)
    (hactual_group_utility_eq_posterior :
      ∀ (g : Group) (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome),
        MeasureGroupAllocationData.AllocationPolicyMeasurable policy →
          (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
            (∫ outcome,
              ∑ item : Applicant,
                if D.group item = g then policy item outcome * actualUtility item outcome else 0 ∂D.law) =
                D.expectedGroupPosteriorUtility g policy)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome)
    (horiginal :
      (∀ item outcome, 0 ≤ original item outcome ∧ original item outcome ≤ 1) ∧
        MeasureGroupAllocationData.AllocationPolicyMeasurable original ∧
          D.expectedCost original ≤ budget ∧
            (∀ g, diversityTarget g ≤
              ∫ outcome,
                ∑ item : Applicant,
                  if D.group item = g then
                    original item outcome * actualUtility item outcome else 0 ∂D.law) ∧
              ∀ other,
                ((∀ item outcome, 0 ≤ other item outcome ∧ other item outcome ≤ 1) ∧
                  MeasureGroupAllocationData.AllocationPolicyMeasurable other ∧
                    D.expectedCost other ≤ budget ∧
                      ∀ g, diversityTarget g ≤
                        ∫ outcome,
                          ∑ item : Applicant,
                            if D.group item = g then
                              other item outcome * actualUtility item outcome else 0 ∂D.law) →
                  (∫ outcome,
                    ∑ item : Applicant, other item outcome * actualUtility item outcome ∂D.law) ≤
                    ∫ outcome,
                      ∑ item : Applicant,
                        original item outcome * actualUtility item outcome ∂D.law)
    (hcost_pos : ∀ item, 0 < D.allocCost item) : Prop :=
  ∃ threshold : Group → paper_cost_aware_extended_threshold,
    ∃ alpha : Group → ℝ,
      ∃ replacement : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
        (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
          paper_cost_aware_groupwise_threshold_policy D threshold alpha replacement ∧
            (∀ item outcome, 0 ≤ replacement item outcome ∧ replacement item outcome ≤ 1) ∧
              MeasureGroupAllocationData.AllocationPolicyMeasurable replacement ∧
                D.expectedCost replacement ≤ budget ∧
                  (∀ g, diversityTarget g ≤
                    ∫ outcome,
                      ∑ item : Applicant,
                        if D.group item = g then
                          replacement item outcome * actualUtility item outcome else 0 ∂D.law) ∧
                    ∀ other,
                      ((∀ item outcome, 0 ≤ other item outcome ∧ other item outcome ≤ 1) ∧
                        MeasureGroupAllocationData.AllocationPolicyMeasurable other ∧
                          D.expectedCost other ≤ budget ∧
                            ∀ g, diversityTarget g ≤
                              ∫ outcome,
                                ∑ item : Applicant,
                                  if D.group item = g then
                                    other item outcome * actualUtility item outcome else 0 ∂D.law) →
                        (∫ outcome,
                          ∑ item : Applicant,
                            other item outcome * actualUtility item outcome ∂D.law) ≤
                          ∫ outcome,
                            ∑ item : Applicant,
                              replacement item outcome * actualUtility item outcome ∂D.law

/-- Source-facing semantic target for `lemma3_equality_diversity_threshold_sufficiency`. -/
def legacy_lemma3_equality_allocation_sliceSpec
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group] [DecidableEq Group]
    (D : paper_measure_group_allocation_data Applicant Outcome Group)
    [IsFiniteMeasure D.law]
    (actualUtility : Applicant → Outcome → ℝ)
    (hactual_utility_eq_posterior :
      ∀ policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
        MeasureGroupAllocationData.AllocationPolicyMeasurable policy →
          (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
            (∫ outcome,
              ∑ item : Applicant, policy item outcome * actualUtility item outcome ∂D.law) =
                D.expectedPosteriorUtility policy)
    (hactual_group_utility_eq_posterior :
      ∀ (g : Group) (policy : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome),
        MeasureGroupAllocationData.AllocationPolicyMeasurable policy →
          (∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1) →
            (∫ outcome,
              ∑ item : Applicant,
                if D.group item = g then policy item outcome * actualUtility item outcome else 0 ∂D.law) =
                D.expectedGroupPosteriorUtility g policy)
    (c : ℝ) (hc : 0 < c) (hcost : ∀ item, D.allocCost item = c)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome)
    (horiginal :
      (∀ item outcome, 0 ≤ original item outcome ∧ original item outcome ≤ 1) ∧
        MeasureGroupAllocationData.AllocationPolicyMeasurable original ∧
          D.expectedCost original ≤ budget ∧
            (∀ g,
              (∫ outcome,
                ∑ item : Applicant,
                  if D.group item = g then
                    original item outcome * actualUtility item outcome else 0 ∂D.law) = equalityTarget g) ∧
              ∀ other,
                ((∀ item outcome, 0 ≤ other item outcome ∧ other item outcome ≤ 1) ∧
                  MeasureGroupAllocationData.AllocationPolicyMeasurable other ∧
                    D.expectedCost other ≤ budget ∧
                      ∀ g,
                        (∫ outcome,
                          ∑ item : Applicant,
                            if D.group item = g then
                              other item outcome * actualUtility item outcome else 0 ∂D.law) = equalityTarget g) →
                  (∫ outcome,
                    ∑ item : Applicant, other item outcome * actualUtility item outcome ∂D.law) ≤
                    ∫ outcome,
                      ∑ item : Applicant,
                        original item outcome * actualUtility item outcome ∂D.law)
    (hequalityTarget_nonneg : ∀ g : Group, 0 ≤ equalityTarget g) : Prop :=
  ∃ threshold : Group → RealThreshold,
    ∃ alpha : Group → ℝ,
      ∃ replacement : MeasureGroupAllocationData.AllocationPolicy Applicant Outcome,
        (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
          (∀ item outcome,
            match threshold (D.group item) with
            | .negInf => replacement item outcome = 1
            | .finite t =>
                (t < D.posteriorUtility item outcome → replacement item outcome = 1) ∧
                (D.posteriorUtility item outcome = t →
                  replacement item outcome = alpha (D.group item)) ∧
                (D.posteriorUtility item outcome < t → replacement item outcome = 0)
            | .posInf => replacement item outcome = 0) ∧
            (∀ item outcome, 0 ≤ replacement item outcome ∧ replacement item outcome ≤ 1) ∧
              MeasureGroupAllocationData.AllocationPolicyMeasurable replacement ∧
                D.expectedCost replacement ≤ budget ∧
                  (∀ g,
                    (∫ outcome,
                      ∑ item : Applicant,
                        if D.group item = g then
                          replacement item outcome * actualUtility item outcome else 0 ∂D.law) = equalityTarget g) ∧
                    ∀ other,
                      ((∀ item outcome, 0 ≤ other item outcome ∧ other item outcome ≤ 1) ∧
                        MeasureGroupAllocationData.AllocationPolicyMeasurable other ∧
                          D.expectedCost other ≤ budget ∧
                            ∀ g,
                              (∫ outcome,
                                ∑ item : Applicant,
                                  if D.group item = g then
                                    other item outcome * actualUtility item outcome else 0 ∂D.law) = equalityTarget g) →
                        (∫ outcome,
                          ∑ item : Applicant,
                            other item outcome * actualUtility item outcome ∂D.law) ≤
                          ∫ outcome,
                            ∑ item : Applicant,
                              replacement item outcome * actualUtility item outcome ∂D.law

/-- Source-facing full policy-pair target for the appendix threshold theorem. -/
def appendix_theorem_cost_aware_threshold_policies_sufficeSpec
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group]
    (D : paper_screening_allocation_data Applicant Outcome Group)
    (budget : ℝ) (hbudget_nonneg : 0 ≤ budget)
    (diversityTarget : Group → ℝ)
    (hdiversityTarget_nonneg : ∀ g, 0 ≤ diversityTarget g)
    (original : paper_screening_allocation_pair D)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal :
      letI : DecidableEq Group := Classical.decEq Group
      (ScreeningAllocationData.ScreeningPolicyBounds original.screening ∧
        MeasureGroupAllocationData.AllocationPolicyBounds original.allocation ∧
          MeasureGroupAllocationData.AllocationPolicyMeasurable original.allocation ∧
            D.screeningSpend original.screening +
                (D.post original.screening).expectedCost original.allocation ≤ budget ∧
              (∀ g, diversityTarget g ≤
                ∫ outcome, ∑ item : Applicant,
                  if (D.post original.screening).group item = g then
                    original.allocation item outcome * D.actualUtility item outcome else 0
                  ∂(D.post original.screening).law)) ∧
        ∀ other : paper_screening_allocation_pair D,
          (ScreeningAllocationData.ScreeningPolicyBounds other.screening ∧
            MeasureGroupAllocationData.AllocationPolicyBounds other.allocation ∧
              MeasureGroupAllocationData.AllocationPolicyMeasurable other.allocation ∧
                D.screeningSpend other.screening +
                    (D.post other.screening).expectedCost other.allocation ≤ budget ∧
                  (∀ g, diversityTarget g ≤
                    ∫ outcome, ∑ item : Applicant,
                      if (D.post other.screening).group item = g then
                        other.allocation item outcome * D.actualUtility item outcome else 0
                      ∂(D.post other.screening).law)) →
            (∫ outcome, ∑ item : Applicant,
              other.allocation item outcome * D.actualUtility item outcome ∂(D.post other.screening).law) ≤
              ∫ outcome, ∑ item : Applicant,
                original.allocation item outcome * D.actualUtility item outcome ∂(D.post original.screening).law) : Prop :=
  letI : DecidableEq Group := Classical.decEq Group
  ∃ threshold : Group → paper_cost_aware_extended_threshold,
    ∃ alpha : Group → ℝ,
      ∃ replacement : paper_screening_allocation_pair D,
        replacement.screening = original.screening ∧
          paper_cost_aware_groupwise_threshold_policy
            (D.post original.screening) threshold alpha replacement.allocation ∧
          ScreeningAllocationData.ScreeningPolicyBounds replacement.screening ∧
            MeasureGroupAllocationData.AllocationPolicyBounds replacement.allocation ∧
              MeasureGroupAllocationData.AllocationPolicyMeasurable replacement.allocation ∧
                D.screeningSpend original.screening +
                    (D.post original.screening).expectedCost replacement.allocation ≤ budget ∧
                  (∀ g, diversityTarget g ≤
                    ∫ outcome, ∑ item : Applicant,
                      if (D.post original.screening).group item = g then
                          replacement.allocation item outcome * D.actualUtility item outcome else 0
                      ∂(D.post original.screening).law) ∧
                    ∀ other : paper_screening_allocation_pair D,
                      (ScreeningAllocationData.ScreeningPolicyBounds other.screening ∧
                        MeasureGroupAllocationData.AllocationPolicyBounds other.allocation ∧
                          MeasureGroupAllocationData.AllocationPolicyMeasurable other.allocation ∧
                            D.screeningSpend other.screening +
                                (D.post other.screening).expectedCost other.allocation ≤ budget ∧
                              (∀ g, diversityTarget g ≤
                                ∫ outcome, ∑ item : Applicant,
                                  if (D.post other.screening).group item = g then
                                    other.allocation item outcome * D.actualUtility item outcome else 0
                                  ∂(D.post other.screening).law)) →
                        (∫ outcome, ∑ item : Applicant,
                          other.allocation item outcome * D.actualUtility item outcome ∂(D.post other.screening).law) ≤
                          ∫ outcome, ∑ item : Applicant,
                            replacement.allocation item outcome * D.actualUtility item outcome ∂(D.post original.screening).law

/-- Source-facing full policy-pair target for Appendix Lemma 3. -/
def lemma3_equality_diversity_threshold_sufficiencySpec
    {Applicant Outcome Group : Type*} [Fintype Applicant]
    [MeasurableSpace Outcome] [Fintype Group]
    (D : paper_screening_allocation_data Applicant Outcome Group)
    (screeningCost : ℝ)
    (c : ℝ) (hc : 0 < c)
    (budget : ℝ) (hbudget_nonneg : 0 ≤ budget)
    (equalityTarget : Group → ℝ)
    (original : paper_screening_allocation_pair D)
    (hscreeningCost : ∀ item, D.screenCost item = screeningCost)
    (hcost : ∀ item, D.allocCost item = c)
    (hequalityTarget_nonneg : ∀ g : Group, 0 ≤ equalityTarget g)
    (horiginal :
      letI : DecidableEq Group := Classical.decEq Group
      (ScreeningAllocationData.ScreeningPolicyBounds original.screening ∧
        MeasureGroupAllocationData.AllocationPolicyBounds original.allocation ∧
          MeasureGroupAllocationData.AllocationPolicyMeasurable original.allocation ∧
            D.screeningSpend original.screening +
                (D.post original.screening).expectedCost original.allocation ≤ budget ∧
              (∀ g,
                (∫ outcome, ∑ item : Applicant,
                  if (D.post original.screening).group item = g then
                    original.allocation item outcome * D.actualUtility item outcome else 0
                  ∂(D.post original.screening).law) = equalityTarget g)) ∧
        ∀ other : paper_screening_allocation_pair D,
          (ScreeningAllocationData.ScreeningPolicyBounds other.screening ∧
            MeasureGroupAllocationData.AllocationPolicyBounds other.allocation ∧
              MeasureGroupAllocationData.AllocationPolicyMeasurable other.allocation ∧
                D.screeningSpend other.screening +
                    (D.post other.screening).expectedCost other.allocation ≤ budget ∧
                  (∀ g,
                    (∫ outcome, ∑ item : Applicant,
                      if (D.post other.screening).group item = g then
                        other.allocation item outcome * D.actualUtility item outcome else 0
                      ∂(D.post other.screening).law) = equalityTarget g)) →
            (∫ outcome, ∑ item : Applicant,
              other.allocation item outcome * D.actualUtility item outcome ∂(D.post other.screening).law) ≤
              ∫ outcome, ∑ item : Applicant,
                original.allocation item outcome * D.actualUtility item outcome ∂(D.post original.screening).law) : Prop :=
  letI : DecidableEq Group := Classical.decEq Group
  ∃ threshold : Group → RealThreshold,
    ∃ alpha : Group → ℝ,
      ∃ replacement : paper_screening_allocation_pair D,
        replacement.screening = original.screening ∧
          paper_main_text_groupwise_threshold_policy
            (D.post original.screening) threshold alpha replacement.allocation ∧
          ScreeningAllocationData.ScreeningPolicyBounds replacement.screening ∧
            MeasureGroupAllocationData.AllocationPolicyBounds replacement.allocation ∧
              MeasureGroupAllocationData.AllocationPolicyMeasurable replacement.allocation ∧
                D.screeningSpend original.screening +
                    (D.post original.screening).expectedCost replacement.allocation ≤ budget ∧
                  (∀ g,
                    (∫ outcome, ∑ item : Applicant,
                      if (D.post original.screening).group item = g then
                        replacement.allocation item outcome * D.actualUtility item outcome else 0
                      ∂(D.post original.screening).law) = equalityTarget g) ∧
                    ∀ other : paper_screening_allocation_pair D,
                      (ScreeningAllocationData.ScreeningPolicyBounds other.screening ∧
                        MeasureGroupAllocationData.AllocationPolicyBounds other.allocation ∧
                          MeasureGroupAllocationData.AllocationPolicyMeasurable other.allocation ∧
                            D.screeningSpend other.screening +
                                (D.post other.screening).expectedCost other.allocation ≤ budget ∧
                              (∀ g,
                                (∫ outcome, ∑ item : Applicant,
                                  if (D.post other.screening).group item = g then
                                    other.allocation item outcome * D.actualUtility item outcome else 0
                                  ∂(D.post other.screening).law) = equalityTarget g)) →
                        (∫ outcome, ∑ item : Applicant,
                          other.allocation item outcome * D.actualUtility item outcome ∂(D.post other.screening).law) ≤
                        ∫ outcome, ∑ item : Applicant,
                          replacement.allocation item outcome * D.actualUtility item outcome ∂(D.post original.screening).law

/-! ## Optimized-procedure formulas -/

/-- Source-facing semantic target for `equation_lp1_optimized_two_group_objective`. -/
def equation_lp1_optimized_two_group_objectiveSpec
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ)
    (hprobability : D.probabilityBounds p a) : Prop :=
  paper_equation_lp1 D p a =
    (∑ i : ScreenApplicant,
      (D.q i * D.e i * p i + D.o i * D.muScreen i * (1 - p i))) +
      ∑ i : DirectApplicant, D.muDirect i * a i

/-- Source-facing semantic target for `equation_lp2_optimized_two_group_budget`. -/
def equation_lp2_optimized_two_group_budgetSpec
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ)
    (hprobability : D.probabilityBounds p a) : Prop :=
  paper_equation_lp2 D p a ≤ D.budget ↔
    (∑ i : ScreenApplicant,
      (D.screenCost * p i + D.allocCost * D.q i * p i +
        D.allocCost * D.o i * (1 - p i))) +
        (∑ i : DirectApplicant, D.allocCost * a i) ≤ D.budget

/-- Source-facing semantic target for `equation_lp3_optimized_screened_group_equality`. -/
def equation_lp3_optimized_screened_group_equalitySpec
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ)
    (hprobability : D.probabilityBounds p a) : Prop :=
  paper_equation_lp3 D p = D.lambdaScreen ↔
    (∑ i : ScreenApplicant,
      (D.q i * D.e i * p i + D.o i * D.muScreen i * (1 - p i))) =
        D.lambdaScreen

/-- Source-facing semantic target for `equation_lp4_optimized_direct_group_equality`. -/
def equation_lp4_optimized_direct_group_equalitySpec
    {ScreenApplicant DirectApplicant : Type*}
    [Fintype ScreenApplicant] [Fintype DirectApplicant]
    (D : paper_optimized_two_group_data ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ)
    (hprobability : D.probabilityBounds p a) : Prop :=
  paper_equation_lp4 D a = D.lambdaDirect ↔
    (∑ i : DirectApplicant, D.muDirect i * a i) = D.lambdaDirect

end

end PaperInterface
end CGGG20SelectiveInformationAcquisition
