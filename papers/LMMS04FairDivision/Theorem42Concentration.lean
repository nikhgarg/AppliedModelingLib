import LMMS04FairDivision.Theorem42
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open scoped BigOperators
open AppliedModelingLib
open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace Theorem42

noncomputable section

/-!
# Finite-PMF concentration layer for LMMS Theorem 4.2

This module keeps the probability/concentration part separate from the random
mechanism shell.  The main endpoint is a reusable finite union bound for the
uniform assignment law: pairwise tail bounds for all ordered pairs imply a high
probability bound on maximum reported envy.
-/

/-- Item weights for the additive source valuations in LMMS Theorem 4.2. -/
abbrev LMMS42ItemWeights (Agent Item : Type*) :=
  Agent → Item → ℝ

/-- The signed contribution of one item to `p`'s reported envy for `q`. -/
def lmms42PairContribution
    {Agent Item : Type*} [DecidableEq Agent]
    (p q : Agent) (assign : Item → Agent) (item : Item) : ℝ :=
  lmms42Y p q item assign

/-- The paper's `f_{pq}` random variable for a realized assignment. -/
noncomputable def lmms42Fpq
    {Agent Item : Type*} [Fintype Item] [DecidableEq Agent]
    (w : LMMS42ItemWeights Agent Item) (p q : Agent)
    (assign : Item → Agent) : ℝ :=
  lmms42F w p q assign

/-- Difference between `p`'s value for `q`'s bundle and her own bundle. -/
noncomputable def lmms42PairwiseReportGap
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [DecidableEq Agent]
    (w : LMMS42ItemWeights Agent Item) (p q : Agent)
    (assign : Item → Agent) : ℝ :=
  lmms42AdditiveReport w p (lmms42AllocationOfAssignment assign q) -
    lmms42AdditiveReport w p (lmms42AllocationOfAssignment assign p)

@[simp] theorem lmms42_reportEnvy_additive_eq_max_gap
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [DecidableEq Agent]
    (w : LMMS42ItemWeights Agent Item) (p q : Agent)
    (assign : Item → Agent) :
    reportEnvy (lmms42AdditiveReport w)
        (lmms42AllocationOfAssignment assign) p q =
      max 0 (lmms42PairwiseReportGap w p q assign) := by
  rfl

theorem lmms42PairwiseReportGap_eq_fpq_of_ne
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [DecidableEq Agent]
    (w : LMMS42ItemWeights Agent Item) {p q : Agent} (hpq : p ≠ q)
    (assign : Item → Agent) :
    lmms42PairwiseReportGap w p q assign =
      lmms42Fpq w p q assign := by
  simpa [lmms42PairwiseReportGap, lmms42Fpq] using
    lmms42_allocationOfAssignment_additive_value_diff_eq_f w hpq assign

/--
Chebyshev tail for a single ordered pair, using a variance certificate for the
paper's `f_{pq}`/bundle-gap random variable.
-/
theorem lmms42_pair_bad_prob_le_of_variance
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (w : LMMS42ItemWeights Agent Item) (p q : Agent) {alpha t : ℝ}
    (ht : 0 < t)
    (hmean :
      pmfExp (lmms42UniformAssignmentLaw Agent Item)
        (lmms42PairwiseReportGap w p q) = 0)
    (hvar :
      pmfVariance (lmms42UniformAssignmentLaw Agent Item)
          (lmms42PairwiseReportGap w p q) ≤
        2 * alpha / (Fintype.card Agent : ℝ)) :
    pmfProb (lmms42UniformAssignmentLaw Agent Item)
        (fun assign : Item → Agent =>
          t < reportEnvy (lmms42AdditiveReport w)
            (lmms42AllocationOfAssignment assign) p q) ≤
      2 * alpha / ((Fintype.card Agent : ℝ) * t ^ 2) := by
  classical
  let μ : PMF (Item → Agent) := lmms42UniformAssignmentLaw Agent Item
  let X : (Item → Agent) → ℝ := lmms42PairwiseReportGap w p q
  have hto_abs :
      pmfProb μ
          (fun assign : Item → Agent =>
            t < reportEnvy (lmms42AdditiveReport w)
              (lmms42AllocationOfAssignment assign) p q) ≤
        pmfProb μ (fun assign : Item → Agent =>
          t < |X assign - pmfExp μ X|) := by
    refine pmfProb_le_of_imp μ _ _ ?_
    intro assign hbad
    have hmax_le_abs :
        max 0 (X assign) ≤ |X assign| := by
      exact max_le (abs_nonneg _) (le_abs_self _)
    have hbad_gap : t < max 0 (X assign) := by
      simpa [X] using hbad
    have hbad_abs : t < |X assign| := lt_of_lt_of_le hbad_gap hmax_le_abs
    simpa [X, μ, hmean] using hbad_abs
  have hcheb :
      pmfProb μ (fun assign : Item → Agent =>
          t < |X assign - pmfExp μ X|) ≤
        pmfVariance μ X / t ^ 2 :=
    pmfProb_abs_sub_mean_gt_le_variance_div_sq μ X ht
  have hdiv :
      pmfVariance μ X / t ^ 2 ≤
        (2 * alpha / (Fintype.card Agent : ℝ)) / t ^ 2 :=
    div_le_div_of_nonneg_right (by simpa [μ, X] using hvar) (sq_nonneg t)
  have hcard_ne : (Fintype.card Agent : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty Agent›).ne'
  have ht2_ne : t ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos ht)
  have hsimpl :
      (2 * alpha / (Fintype.card Agent : ℝ)) / t ^ 2 =
        2 * alpha / ((Fintype.card Agent : ℝ) * t ^ 2) := by
    field_simp [hcard_ne, ht2_ne]
  exact le_trans hto_abs (le_trans hcheb (by simpa [hsimpl] using hdiv))

theorem lmms42PairwiseReportGap_expectation_eq_zero_of_ne
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (w : LMMS42ItemWeights Agent Item) {p q : Agent} (hpq : p ≠ q) :
    pmfExp (lmms42UniformAssignmentLaw Agent Item)
        (lmms42PairwiseReportGap w p q) = 0 := by
  classical
  let μ : PMF (Item → Agent) := lmms42UniformAssignmentLaw Agent Item
  calc
    pmfExp μ (lmms42PairwiseReportGap w p q) =
        pmfExp μ (fun assign : Item → Agent => lmms42F w p q assign) := by
          refine pmfExp_congr μ ?_
          intro assign
          exact lmms42PairwiseReportGap_eq_fpq_of_ne w hpq assign
    _ = 0 := by
          simpa [μ] using lmms42F_expectation_eq_zero w hpq

theorem lmms42PairwiseReportGap_variance_le_of_weights
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (w : LMMS42ItemWeights Agent Item) {alpha : ℝ} {p q : Agent}
    (hpq : p ≠ q)
    (hnonneg : ∀ g : Item, 0 ≤ w p g)
    (hsum : ∑ g : Item, w p g = 1)
    (hbound : ∀ g : Item, w p g ≤ alpha) :
    pmfVariance (lmms42UniformAssignmentLaw Agent Item)
        (lmms42PairwiseReportGap w p q) ≤
      2 * alpha / (Fintype.card Agent : ℝ) := by
  classical
  let μ : PMF (Item → Agent) := lmms42UniformAssignmentLaw Agent Item
  let G : (Item → Agent) → ℝ := lmms42PairwiseReportGap w p q
  let F : (Item → Agent) → ℝ := fun assign => lmms42F w p q assign
  have hGF : ∀ assign, G assign = F assign := by
    intro assign
    exact lmms42PairwiseReportGap_eq_fpq_of_ne w hpq assign
  have hmean : pmfExp μ G = pmfExp μ F :=
    pmfExp_congr μ hGF
  have hvar_eq : pmfVariance μ G = pmfVariance μ F := by
    unfold pmfVariance
    refine pmfExp_congr μ ?_
    intro assign
    rw [hGF assign, hmean]
  calc
    pmfVariance μ G = pmfVariance μ F := hvar_eq
    _ ≤ 2 * alpha / (Fintype.card Agent : ℝ) := by
          simpa [μ, F] using lmms42F_variance_le w hpq hnonneg hsum hbound

theorem lmms42_pair_bad_prob_le_of_weights
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (w : LMMS42ItemWeights Agent Item) {alpha t : ℝ}
    {p q : Agent} (hpq : p ≠ q)
    (ht : 0 < t)
    (hnonneg : ∀ g : Item, 0 ≤ w p g)
    (hsum : ∑ g : Item, w p g = 1)
    (hbound : ∀ g : Item, w p g ≤ alpha) :
    pmfProb (lmms42UniformAssignmentLaw Agent Item)
        (fun assign : Item → Agent =>
          t < reportEnvy (lmms42AdditiveReport w)
            (lmms42AllocationOfAssignment assign) p q) ≤
      2 * alpha / ((Fintype.card Agent : ℝ) * t ^ 2) := by
  exact
    lmms42_pair_bad_prob_le_of_variance w p q ht
      (lmms42PairwiseReportGap_expectation_eq_zero_of_ne w hpq)
      (lmms42PairwiseReportGap_variance_le_of_weights
        w hpq hnonneg hsum hbound)

@[simp] theorem lmms42_reportEnvy_self
    {Agent Item : Type*} (values : FairDivisionReport Agent Item)
    (A : Allocation Agent Item) (p : Agent) :
    reportEnvy values A p p = 0 := by
  simp [reportEnvy]

/--
Finite union-bound endpoint for the LMMS uniform assignment law.  It is stated
directly for an arbitrary report profile, so later paper-facing wrappers can
plug in either additive reports or a more specialized report interface.
-/
theorem lmms42_uniformAssignment_maxReportEnvy_prob_ge_of_pair_tails
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (values : FairDivisionReport Agent Item) {alpha t : ℝ}
    (halpha : 0 ≤ alpha) (ht : 0 < t)
    (hpair :
      ∀ p q : Agent, p ≠ q →
        pmfProb (lmms42UniformAssignmentLaw Agent Item)
          (fun assign : Item → Agent =>
            t < reportEnvy values
              (lmms42AllocationOfAssignment assign) p q) ≤
          2 * alpha / ((Fintype.card Agent : ℝ) * t ^ 2)) :
    1 - 2 * alpha * (Fintype.card Agent : ℝ) / t ^ 2 ≤
      pmfProb (lmms42UniformAssignmentLaw Agent Item)
        (fun assign : Item → Agent =>
          maxReportEnvy values (lmms42AllocationOfAssignment assign) ≤ t) := by
  classical
  let μ : PMF (Item → Agent) := lmms42UniformAssignmentLaw Agent Item
  let eps : ℝ := 2 * alpha / ((Fintype.card Agent : ℝ) * t ^ 2)
  let bad : Agent × Agent → (Item → Agent) → Prop :=
    fun pq assign =>
      t < reportEnvy values (lmms42AllocationOfAssignment assign) pq.1 pq.2
  have hcard_pos : 0 < (Fintype.card Agent : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty Agent›
  have ht2_pos : 0 < t ^ 2 := sq_pos_of_pos ht
  have heps_nonneg : 0 ≤ eps := by
    exact div_nonneg
      (mul_nonneg (by norm_num) halpha)
      (mul_nonneg (le_of_lt hcard_pos) (le_of_lt ht2_pos))
  have hprob_each : ∀ pq : Agent × Agent, pmfProb μ (bad pq) ≤ eps := by
    intro pq
    by_cases hpq : pq.1 = pq.2
    · have hfalse :
          pmfProb μ (bad pq) = 0 := by
        rw [pmfProb_congr μ (q := fun _assign : Item → Agent => False)]
        · exact pmfProb_false μ
        · intro assign
          have hself :
              reportEnvy values
                (lmms42AllocationOfAssignment assign) pq.1 pq.2 = 0 := by
            rw [hpq]
            simp
          simp [bad, hself, not_lt_of_ge ht.le]
      rw [hfalse]
      exact heps_nonneg
    · simpa [μ, eps, bad] using hpair pq.1 pq.2 hpq
  have hbad_union :
      pmfProb μ (fun assign : Item → Agent => ∃ pq : Agent × Agent, bad pq assign) ≤
        (Fintype.card (Agent × Agent) : ℝ) * eps :=
    pmfProb_exists_le_card_mul μ bad eps hprob_each
  have hcard_prod :
      (Fintype.card (Agent × Agent) : ℝ) =
        (Fintype.card Agent : ℝ) * (Fintype.card Agent : ℝ) := by
    rw [Fintype.card_prod, Nat.cast_mul]
  have hcard_ne : (Fintype.card Agent : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have ht2_ne : t ^ 2 ≠ 0 := ne_of_gt ht2_pos
  have hbad_bound :
      pmfProb μ (fun assign : Item → Agent => ∃ pq : Agent × Agent, bad pq assign) ≤
        2 * alpha * (Fintype.card Agent : ℝ) / t ^ 2 := by
    calc
      pmfProb μ (fun assign : Item → Agent => ∃ pq : Agent × Agent, bad pq assign) ≤
          (Fintype.card (Agent × Agent) : ℝ) * eps := hbad_union
      _ = 2 * alpha * (Fintype.card Agent : ℝ) / t ^ 2 := by
          rw [hcard_prod]
          change
            (Fintype.card Agent : ℝ) * (Fintype.card Agent : ℝ) *
                (2 * alpha / ((Fintype.card Agent : ℝ) * t ^ 2)) =
              2 * alpha * (Fintype.card Agent : ℝ) / t ^ 2
          field_simp [hcard_ne, ht2_ne]
  have hgood_congr :
      pmfProb μ
          (fun assign : Item → Agent =>
            maxReportEnvy values (lmms42AllocationOfAssignment assign) ≤ t) =
        pmfProb μ
          (fun assign : Item → Agent =>
            ¬ ∃ pq : Agent × Agent, bad pq assign) := by
    refine pmfProb_congr μ ?_
    intro assign
    constructor
    · intro hmax hbad
      rcases hbad with ⟨pq, hpq_bad⟩
      have hpair_le :
          reportEnvy values (lmms42AllocationOfAssignment assign) pq.1 pq.2 ≤ t :=
        (maxReportEnvy_le_iff values
          (lmms42AllocationOfAssignment assign) t).mp hmax pq.1 pq.2
      exact not_lt_of_ge hpair_le hpq_bad
    · intro hnot
      rw [maxReportEnvy_le_iff]
      intro p q
      exact le_of_not_gt (fun hbad => hnot ⟨(p, q), hbad⟩)
  rw [hgood_congr, pmfProb_compl]
  linarith

/--
Source concentration endpoint for LMMS Theorem 4.2: if every agent's additive
item weights are normalized to total value one and every single item has value
at most `alpha`, then the independent uniform random allocation has maximum
envy at most `t` with the explicit Chebyshev/union-bound probability from the
paper proof.
-/
theorem lmms42_uniformAssignment_maxReportEnvy_prob_ge_of_weights
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [Nonempty Agent] [DecidableEq Agent]
    (w : LMMS42ItemWeights Agent Item) {alpha t : ℝ}
    (halpha : 0 ≤ alpha) (ht : 0 < t)
    (hnonneg : ∀ p : Agent, ∀ g : Item, 0 ≤ w p g)
    (hsum : ∀ p : Agent, ∑ g : Item, w p g = 1)
    (hbound : ∀ p : Agent, ∀ g : Item, w p g ≤ alpha) :
    1 - 2 * alpha * (Fintype.card Agent : ℝ) / t ^ 2 ≤
      pmfProb (lmms42UniformAssignmentLaw Agent Item)
        (fun assign : Item → Agent =>
          maxReportEnvy (lmms42AdditiveReport w)
            (lmms42AllocationOfAssignment assign) ≤ t) := by
  exact
    lmms42_uniformAssignment_maxReportEnvy_prob_ge_of_pair_tails
      (values := lmms42AdditiveReport w) halpha ht
      (by
        intro p q hpq
        exact
          lmms42_pair_bad_prob_le_of_weights
            w hpq ht (hnonneg p) (hsum p) (hbound p))

end

end Theorem42
end LMMS04FairDivision
