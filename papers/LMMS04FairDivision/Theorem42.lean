import AppliedModelingLib.SocialChoice.FairDivision.Mechanisms

open scoped BigOperators
open AppliedModelingLib
open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace Theorem42

noncomputable section

/-!
# Random Allocation Shell for LMMS Theorem 4.2

The source randomized algorithm assigns each good independently and uniformly
to a player.  This module formalizes the allocation law, exact allocation of
all goods, the report-independence/truthfulness part of the theorem, and the
deterministic `f_{pq}` envy expression used by the source concentration proof.
-/

/-! ## Deterministic allocation and envy algebra -/

/-- Additive bundle-value report from item weights. -/
def lmms42AdditiveReport
    {Agent Item : Type*} (w : Agent → Item → ℝ) :
    FairDivisionReport Agent Item :=
  fun agent S => S.sum fun item => w agent item

/-- Allocation induced by assigning each item to an agent. -/
def lmms42AllocationOfAssignment
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [DecidableEq Agent]
    (assign : Item → Agent) : Allocation Agent Item :=
  fun agent => Finset.univ.filter fun item => assign item = agent

theorem lmms42AllocationOfAssignment_isAllocationOf
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [DecidableEq Agent]
    (assign : Item → Agent) :
    IsAllocationOf
      (lmms42AllocationOfAssignment assign : Allocation Agent Item)
      (Finset.univ : Finset Item) := by
  constructor
  · intro _agent item _hmem
    simp
  · intro item _hgoods
    refine ⟨assign item, ?_, ?_⟩
    · simp [lmms42AllocationOfAssignment]
    · intro owner howner
      have hassign : assign item = owner := by
        simpa [lmms42AllocationOfAssignment] using howner
      exact hassign.symm

/--
Contribution sign of item `g` to player `p`'s envy for player `q`: `1` if
`q` receives the item, `-1` if `p` receives it, and `0` otherwise.
-/
def lmms42Y
    {Agent Item : Type*} [DecidableEq Agent]
    (p q : Agent) (g : Item) (assign : Item → Agent) : ℝ :=
  if assign g = q then 1 else if assign g = p then -1 else 0

/-- The source random variable `f_{pq} = ∑_j v_{p,j} Y_j`. -/
def lmms42F
    {Agent Item : Type*} [Fintype Item] [DecidableEq Agent]
    (w : Agent → Item → ℝ) (p q : Agent) (assign : Item → Agent) : ℝ :=
  ∑ g : Item, w p g * lmms42Y p q g assign

theorem lmms42_weight_mul_y_eq_indicator_sub
    {Agent Item : Type*} [DecidableEq Agent]
    (w : Agent → Item → ℝ) {p q : Agent} (hpq : p ≠ q)
    (g : Item) (assign : Item → Agent) :
    w p g * lmms42Y p q g assign =
      (if assign g = q then w p g else 0) -
        (if assign g = p then w p g else 0) := by
  classical
  by_cases hq : assign g = q
  · have hp : assign g ≠ p := by
      intro hp
      exact hpq (by simpa [hp] using hq)
    have hqp : q ≠ p := by
      intro hqp
      exact hpq hqp.symm
    simp [lmms42Y, hq, hqp]
  · by_cases hp : assign g = p
    · simp [lmms42Y, hp, hpq]
    · simp [lmms42Y, hq, hp]

theorem lmms42_allocationOfAssignment_additive_value_diff_eq_f
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [DecidableEq Agent]
    (w : Agent → Item → ℝ) {p q : Agent} (hpq : p ≠ q)
    (assign : Item → Agent) :
    lmms42AdditiveReport w p (lmms42AllocationOfAssignment assign q) -
        lmms42AdditiveReport w p (lmms42AllocationOfAssignment assign p) =
      lmms42F w p q assign := by
  classical
  unfold lmms42AdditiveReport lmms42AllocationOfAssignment lmms42F
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro g _hg
  exact (lmms42_weight_mul_y_eq_indicator_sub w hpq g assign).symm

/--
For distinct players, reported envy under the assignment allocation is exactly
the positive part of the paper's `f_{pq}` random variable.
-/
theorem lmms42_reportEnvy_allocationOfAssignment_eq_max_f
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [DecidableEq Agent]
    (w : Agent → Item → ℝ) {p q : Agent} (hpq : p ≠ q)
    (assign : Item → Agent) :
    reportEnvy (lmms42AdditiveReport w)
        (lmms42AllocationOfAssignment assign) p q =
      max 0 (lmms42F w p q assign) := by
  rw [reportEnvy, lmms42_allocationOfAssignment_additive_value_diff_eq_f w hpq assign]

theorem lmms42_reportEnvy_self_allocationOfAssignment
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [DecidableEq Agent]
    (w : Agent → Item → ℝ) (p : Agent) (assign : Item → Agent) :
    reportEnvy (lmms42AdditiveReport w)
        (lmms42AllocationOfAssignment assign) p p = 0 := by
  simp [reportEnvy]

/--
If every distinct ordered pair has `f_{pq} ≤ t`, then maximum reported envy is
at most `t`.
-/
theorem lmms42_maxReportEnvy_allocationOfAssignment_le_of_forall_f_le
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    [Fintype Item] [DecidableEq Item] [DecidableEq Agent]
    (w : Agent → Item → ℝ) (assign : Item → Agent) {t : ℝ}
    (ht : 0 ≤ t)
    (hpair : ∀ p q : Agent, p ≠ q → lmms42F w p q assign ≤ t) :
    maxReportEnvy (lmms42AdditiveReport w)
        (lmms42AllocationOfAssignment assign) ≤ t := by
  rw [maxReportEnvy_le_iff]
  intro p q
  by_cases hpq : p = q
  · subst q
    rw [lmms42_reportEnvy_self_allocationOfAssignment]
    exact ht
  · rw [lmms42_reportEnvy_allocationOfAssignment_eq_max_f w hpq assign]
    exact max_le ht (hpair p q hpq)

/--
A failed maximum-envy bound is witnessed by a distinct ordered pair with
`t < f_{pq}`.  This is the deterministic event inclusion used before the
finite union bound.
-/
theorem lmms42_exists_bad_pair_of_not_maxReportEnvy_le
    {Agent Item : Type*} [Fintype Agent] [Nonempty Agent]
    [Fintype Item] [DecidableEq Item] [DecidableEq Agent]
    (w : Agent → Item → ℝ) (assign : Item → Agent) {t : ℝ}
    (ht : 0 ≤ t)
    (hbad :
      ¬ maxReportEnvy (lmms42AdditiveReport w)
          (lmms42AllocationOfAssignment assign) ≤ t) :
    ∃ pair ∈ (Finset.univ : Finset Agent).product (Finset.univ : Finset Agent),
      pair.1 ≠ pair.2 ∧ t < lmms42F w pair.1 pair.2 assign := by
  classical
  have hnotall :
      ¬ ∀ p q : Agent,
        reportEnvy (lmms42AdditiveReport w)
          (lmms42AllocationOfAssignment assign) p q ≤ t := by
    simpa [maxReportEnvy_le_iff] using hbad
  push Not at hnotall
  obtain ⟨p, q, hpq_bad⟩ := hnotall
  have hpq_ne : p ≠ q := by
    intro hpq
    subst q
    have hself :
        reportEnvy (lmms42AdditiveReport w)
          (lmms42AllocationOfAssignment assign) p p ≤ t := by
      rw [lmms42_reportEnvy_self_allocationOfAssignment]
      exact ht
    exact not_lt_of_ge hself hpq_bad
  have henvy_gt :
      t < reportEnvy (lmms42AdditiveReport w)
        (lmms42AllocationOfAssignment assign) p q :=
    hpq_bad
  have hf_gt : t < lmms42F w p q assign := by
    rw [lmms42_reportEnvy_allocationOfAssignment_eq_max_f w hpq_ne assign] at henvy_gt
    by_contra hf_not
    have hf_le : lmms42F w p q assign ≤ t := le_of_not_gt hf_not
    exact not_lt_of_ge (max_le ht hf_le) henvy_gt
  exact ⟨(p, q), by simp, hpq_ne, hf_gt⟩

/-! ## Uniform random mechanism -/

/-- Independent uniform assignment of every item to an agent. -/
noncomputable def lmms42UniformAssignmentLaw
    (Agent Item : Type*) [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [Nonempty Agent] : PMF (Item → Agent) :=
  pmfProduct Item Agent (uniformPMF Agent)

theorem lmms42UniformAssignmentLaw_eq_uniformPMF_fun
    (Agent Item : Type*) [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [Nonempty Agent] :
    lmms42UniformAssignmentLaw Agent Item = uniformPMF (Item → Agent) := by
  exact pmfProduct_uniformPMF_eq_uniformPMF_fun Item Agent

theorem lmms42Y_eq_indicator_sub
    {Agent Item : Type*} [DecidableEq Agent]
    {p q : Agent} (hpq : p ≠ q) (g : Item) (assign : Item → Agent) :
    lmms42Y p q g assign =
      (if assign g = q then (1 : ℝ) else 0) -
        (if assign g = p then (1 : ℝ) else 0) := by
  classical
  simpa using
    (lmms42_weight_mul_y_eq_indicator_sub
      (fun _agent _item => (1 : ℝ)) hpq g assign)

theorem lmms42Y_sq_eq_indicator_add
    {Agent Item : Type*} [DecidableEq Agent]
    {p q : Agent} (hpq : p ≠ q) (g : Item) (assign : Item → Agent) :
    (lmms42Y p q g assign) ^ 2 =
      (if assign g = q then (1 : ℝ) else 0) +
        (if assign g = p then (1 : ℝ) else 0) := by
  classical
  by_cases hq : assign g = q
  · have hqp : q ≠ p := by
      intro hqp
      exact hpq hqp.symm
    simp [lmms42Y, hq, hqp]
  · by_cases hp : assign g = p
    · simp [lmms42Y, hp, hpq]
    · simp [lmms42Y, hq, hp]

theorem lmms42Y_expectation_eq_zero
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [DecidableEq Agent] [Nonempty Agent]
    {p q : Agent} (hpq : p ≠ q) (g : Item) :
    pmfExp (lmms42UniformAssignmentLaw Agent Item)
        (fun assign : Item → Agent => lmms42Y p q g assign) = 0 := by
  classical
  let μ : PMF (Item → Agent) := lmms42UniformAssignmentLaw Agent Item
  have hY :
      pmfExp μ (fun assign : Item → Agent => lmms42Y p q g assign) =
        pmfExp μ
          (fun assign : Item → Agent =>
            (if assign g = q then (1 : ℝ) else 0) -
              (if assign g = p then (1 : ℝ) else 0)) := by
    refine pmfExp_congr μ ?_
    intro assign
    exact lmms42Y_eq_indicator_sub hpq g assign
  calc
    pmfExp μ (fun assign : Item → Agent => lmms42Y p q g assign) =
        pmfExp μ
          (fun assign : Item → Agent =>
            (if assign g = q then (1 : ℝ) else 0) -
              (if assign g = p then (1 : ℝ) else 0)) := hY
    _ =
        pmfProb μ (fun assign : Item → Agent => assign g = q) -
          pmfProb μ (fun assign : Item → Agent => assign g = p) := by
          rw [pmfExp_sub]
          rfl
    _ = 0 := by
          rw [show μ = uniformPMF (Item → Agent) by
            exact lmms42UniformAssignmentLaw_eq_uniformPMF_fun Agent Item]
          rw [pmfProb_uniformPMF_fun_eval_eq (i := g) q]
          rw [pmfProb_uniformPMF_fun_eval_eq (i := g) p]
          ring

theorem lmms42Y_second_moment
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [DecidableEq Agent] [Nonempty Agent]
    {p q : Agent} (hpq : p ≠ q) (g : Item) :
    pmfExp (lmms42UniformAssignmentLaw Agent Item)
        (fun assign : Item → Agent => (lmms42Y p q g assign) ^ 2) =
      2 * (Fintype.card Agent : ℝ)⁻¹ := by
  classical
  let μ : PMF (Item → Agent) := lmms42UniformAssignmentLaw Agent Item
  have hY :
      pmfExp μ
          (fun assign : Item → Agent => (lmms42Y p q g assign) ^ 2) =
        pmfExp μ
          (fun assign : Item → Agent =>
            (if assign g = q then (1 : ℝ) else 0) +
              (if assign g = p then (1 : ℝ) else 0)) := by
    refine pmfExp_congr μ ?_
    intro assign
    exact lmms42Y_sq_eq_indicator_add hpq g assign
  calc
    pmfExp μ
        (fun assign : Item → Agent => (lmms42Y p q g assign) ^ 2) =
        pmfExp μ
          (fun assign : Item → Agent =>
            (if assign g = q then (1 : ℝ) else 0) +
              (if assign g = p then (1 : ℝ) else 0)) := hY
    _ =
        pmfProb μ (fun assign : Item → Agent => assign g = q) +
          pmfProb μ (fun assign : Item → Agent => assign g = p) := by
          rw [pmfExp_add]
          rfl
    _ = 2 * (Fintype.card Agent : ℝ)⁻¹ := by
          rw [show μ = uniformPMF (Item → Agent) by
            exact lmms42UniformAssignmentLaw_eq_uniformPMF_fun Agent Item]
          rw [pmfProb_uniformPMF_fun_eval_eq (i := g) q]
          rw [pmfProb_uniformPMF_fun_eval_eq (i := g) p]
          ring

theorem lmms42_indicator_pair_expectation
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [DecidableEq Agent] [Nonempty Agent]
    {g h : Item} (hgh : g ≠ h) (a b : Agent) :
    pmfExp (lmms42UniformAssignmentLaw Agent Item)
        (fun assign : Item → Agent =>
          (if assign g = a then (1 : ℝ) else 0) *
            (if assign h = b then (1 : ℝ) else 0)) =
      (Fintype.card Agent : ℝ)⁻¹ ^ 2 := by
  classical
  let μ : PMF (Item → Agent) := lmms42UniformAssignmentLaw Agent Item
  have hindicator :
      pmfExp μ
          (fun assign : Item → Agent =>
            (if assign g = a then (1 : ℝ) else 0) *
              (if assign h = b then (1 : ℝ) else 0)) =
        pmfProb μ (fun assign : Item → Agent =>
          assign g = a ∧ assign h = b) := by
    unfold pmfProb
    refine pmfExp_congr μ ?_
    intro assign
    by_cases hg : assign g = a <;>
      by_cases hh : assign h = b <;> simp [hg, hh]
  calc
    pmfExp μ
        (fun assign : Item → Agent =>
          (if assign g = a then (1 : ℝ) else 0) *
            (if assign h = b then (1 : ℝ) else 0)) =
        pmfProb μ (fun assign : Item → Agent =>
          assign g = a ∧ assign h = b) := hindicator
    _ = pmfProb (uniformPMF (Item → Agent))
        (fun assign : Item → Agent => assign g = a ∧ assign h = b) := by
          rw [show μ = uniformPMF (Item → Agent) by
            exact lmms42UniformAssignmentLaw_eq_uniformPMF_fun Agent Item]
    _ = (Fintype.card Agent : ℝ)⁻¹ ^ 2 := by
          exact pmfProb_uniformPMF_fun_eq_pair_of_ne hgh a b

theorem lmms42Y_mul_expectation_eq_zero_of_ne_item
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [DecidableEq Agent] [Nonempty Agent]
    {p q : Agent} (hpq : p ≠ q) {g h : Item} (hgh : g ≠ h) :
    pmfExp (lmms42UniformAssignmentLaw Agent Item)
        (fun assign : Item → Agent =>
          lmms42Y p q g assign * lmms42Y p q h assign) = 0 := by
  classical
  let μ : PMF (Item → Agent) := lmms42UniformAssignmentLaw Agent Item
  let I : Agent → Item → (Item → Agent) → ℝ :=
    fun a item assign => if assign item = a then (1 : ℝ) else 0
  have hpoint :
      ∀ assign : Item → Agent,
        lmms42Y p q g assign * lmms42Y p q h assign =
          I q g assign * I q h assign -
            I q g assign * I p h assign -
            I p g assign * I q h assign +
            I p g assign * I p h assign := by
    intro assign
    rw [lmms42Y_eq_indicator_sub hpq g assign,
      lmms42Y_eq_indicator_sub hpq h assign]
    dsimp [I]
    ring
  calc
    pmfExp μ
        (fun assign : Item → Agent =>
          lmms42Y p q g assign * lmms42Y p q h assign) =
        pmfExp μ
          (fun assign : Item → Agent =>
            I q g assign * I q h assign -
              I q g assign * I p h assign -
              I p g assign * I q h assign +
              I p g assign * I p h assign) := by
          exact pmfExp_congr μ hpoint
    _ =
        pmfExp μ (fun assign : Item → Agent => I q g assign * I q h assign) -
          pmfExp μ (fun assign : Item → Agent => I q g assign * I p h assign) -
          pmfExp μ (fun assign : Item → Agent => I p g assign * I q h assign) +
          pmfExp μ (fun assign : Item → Agent => I p g assign * I p h assign) := by
          rw [pmfExp_add, pmfExp_sub, pmfExp_sub]
    _ = 0 := by
          rw [show
            pmfExp μ (fun assign : Item → Agent => I q g assign * I q h assign) =
              (Fintype.card Agent : ℝ)⁻¹ ^ 2 by
                simpa [μ, I] using
                  lmms42_indicator_pair_expectation
                    (Agent := Agent) (Item := Item) hgh q q]
          rw [show
            pmfExp μ (fun assign : Item → Agent => I q g assign * I p h assign) =
              (Fintype.card Agent : ℝ)⁻¹ ^ 2 by
                simpa [μ, I] using
                  lmms42_indicator_pair_expectation
                    (Agent := Agent) (Item := Item) hgh q p]
          rw [show
            pmfExp μ (fun assign : Item → Agent => I p g assign * I q h assign) =
              (Fintype.card Agent : ℝ)⁻¹ ^ 2 by
                simpa [μ, I] using
                  lmms42_indicator_pair_expectation
                    (Agent := Agent) (Item := Item) hgh p q]
          rw [show
            pmfExp μ (fun assign : Item → Agent => I p g assign * I p h assign) =
              (Fintype.card Agent : ℝ)⁻¹ ^ 2 by
                simpa [μ, I] using
                  lmms42_indicator_pair_expectation
                    (Agent := Agent) (Item := Item) hgh p p]
          ring

theorem lmms42F_expectation_eq_zero
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [DecidableEq Agent] [Nonempty Agent]
    (w : Agent → Item → ℝ) {p q : Agent} (hpq : p ≠ q) :
    pmfExp (lmms42UniformAssignmentLaw Agent Item)
        (fun assign : Item → Agent => lmms42F w p q assign) = 0 := by
  classical
  let μ : PMF (Item → Agent) := lmms42UniformAssignmentLaw Agent Item
  calc
    pmfExp μ (fun assign : Item → Agent => lmms42F w p q assign) =
        pmfExp μ
          (fun assign : Item → Agent =>
            ∑ g : Item, w p g * lmms42Y p q g assign) := by
          rfl
    _ = ∑ g : Item,
        pmfExp μ (fun assign : Item → Agent => w p g * lmms42Y p q g assign) := by
          rw [pmfExp_univ_sum]
    _ = ∑ _g : Item, 0 := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          rw [pmfExp_const_mul]
          rw [show
            pmfExp μ (fun assign : Item → Agent => lmms42Y p q g assign) = 0 by
              simpa [μ] using
                lmms42Y_expectation_eq_zero
                  (Agent := Agent) (Item := Item) hpq g]
          simp
    _ = 0 := by simp

theorem lmms42F_second_moment_eq
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [DecidableEq Agent] [Nonempty Agent]
    (w : Agent → Item → ℝ) {p q : Agent} (hpq : p ≠ q) :
    pmfExp (lmms42UniformAssignmentLaw Agent Item)
        (fun assign : Item → Agent => (lmms42F w p q assign) ^ 2) =
      2 * (Fintype.card Agent : ℝ)⁻¹ * ∑ g : Item, (w p g) ^ 2 := by
  classical
  let μ : PMF (Item → Agent) := lmms42UniformAssignmentLaw Agent Item
  let X : Item → (Item → Agent) → ℝ :=
    fun g assign => w p g * lmms42Y p q g assign
  have hdiag :
      ∀ g : Item,
        pmfExp μ (fun assign : Item → Agent => X g assign * X g assign) =
          2 * (Fintype.card Agent : ℝ)⁻¹ * (w p g) ^ 2 := by
    intro g
    calc
      pmfExp μ (fun assign : Item → Agent => X g assign * X g assign) =
          pmfExp μ
            (fun assign : Item → Agent =>
              (w p g) ^ 2 * (lmms42Y p q g assign) ^ 2) := by
            refine pmfExp_congr μ ?_
            intro assign
            simp [X]
            ring
      _ = (w p g) ^ 2 *
          pmfExp μ (fun assign : Item → Agent => (lmms42Y p q g assign) ^ 2) := by
            rw [pmfExp_const_mul]
      _ = 2 * (Fintype.card Agent : ℝ)⁻¹ * (w p g) ^ 2 := by
            rw [show
              pmfExp μ
                  (fun assign : Item → Agent => (lmms42Y p q g assign) ^ 2) =
                2 * (Fintype.card Agent : ℝ)⁻¹ by
                  simpa [μ] using
                    lmms42Y_second_moment
                      (Agent := Agent) (Item := Item) hpq g]
            ring
  have hoffdiag :
      ∀ g h : Item, g ≠ h →
        pmfExp μ (fun assign : Item → Agent => X g assign * X h assign) = 0 := by
    intro g h hgh
    calc
      pmfExp μ (fun assign : Item → Agent => X g assign * X h assign) =
          (w p g * w p h) *
            pmfExp μ
              (fun assign : Item → Agent =>
                lmms42Y p q g assign * lmms42Y p q h assign) := by
            rw [← pmfExp_const_mul]
            refine pmfExp_congr μ ?_
            intro assign
            simp [X]
            ring
      _ = 0 := by
            rw [show
              pmfExp μ
                  (fun assign : Item → Agent =>
                    lmms42Y p q g assign * lmms42Y p q h assign) = 0 by
                simpa [μ] using
                  lmms42Y_mul_expectation_eq_zero_of_ne_item
                    (Agent := Agent) (Item := Item) hpq hgh]
            simp
  calc
    pmfExp μ (fun assign : Item → Agent => (lmms42F w p q assign) ^ 2) =
        pmfExp μ
          (fun assign : Item → Agent =>
            ∑ g : Item, ∑ h : Item, X g assign * X h assign) := by
          refine pmfExp_congr μ ?_
          intro assign
          simp [lmms42F, X]
          rw [sq]
          exact Fintype.sum_mul_sum
            (fun g : Item => w p g * lmms42Y p q g assign)
            (fun h : Item => w p h * lmms42Y p q h assign)
    _ = ∑ g : Item, ∑ h : Item,
        pmfExp μ (fun assign : Item → Agent => X g assign * X h assign) := by
          rw [pmfExp_univ_sum]
          refine Finset.sum_congr rfl ?_
          intro g _hg
          rw [pmfExp_univ_sum]
    _ = ∑ g : Item, 2 * (Fintype.card Agent : ℝ)⁻¹ * (w p g) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro g _hg
          rw [Finset.sum_eq_single g]
          · exact hdiag g
          · intro h _hh hne
            exact hoffdiag g h (fun hgh => hne hgh.symm)
          · intro hg_not
            exact False.elim (hg_not (Finset.mem_univ g))
    _ = 2 * (Fintype.card Agent : ℝ)⁻¹ * ∑ g : Item, (w p g) ^ 2 := by
          rw [Finset.mul_sum]

theorem lmms42F_variance_le
    {Agent Item : Type*} [Fintype Item] [DecidableEq Item]
    [Fintype Agent] [DecidableEq Agent] [Nonempty Agent]
    (w : Agent → Item → ℝ) {alpha : ℝ} {p q : Agent} (hpq : p ≠ q)
    (hnonneg : ∀ g : Item, 0 ≤ w p g)
    (hsum : ∑ g : Item, w p g = 1)
    (hbound : ∀ g : Item, w p g ≤ alpha) :
    pmfVariance (lmms42UniformAssignmentLaw Agent Item)
        (fun assign : Item → Agent => lmms42F w p q assign) ≤
      2 * alpha / (Fintype.card Agent : ℝ) := by
  classical
  let μ : PMF (Item → Agent) := lmms42UniformAssignmentLaw Agent Item
  let F : (Item → Agent) → ℝ := fun assign => lmms42F w p q assign
  have hsquare_bound :
      ∑ g : Item, (w p g) ^ 2 ≤ alpha := by
    calc
      ∑ g : Item, (w p g) ^ 2 ≤ ∑ g : Item, alpha * w p g := by
          refine Finset.sum_le_sum ?_
          intro g _hg
          nlinarith [hnonneg g, hbound g]
      _ = alpha := by
          rw [← Finset.mul_sum, hsum]
          ring
  have hcoeff_nonneg :
      0 ≤ 2 * (Fintype.card Agent : ℝ)⁻¹ := by
    have hcard_pos : 0 < (Fintype.card Agent : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty Agent›
    positivity
  have hcard_ne : (Fintype.card Agent : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty Agent›).ne'
  calc
    pmfVariance μ F =
        pmfExp μ (fun assign : Item → Agent => F assign ^ 2) -
          (pmfExp μ F) ^ 2 := by
          exact pmfVariance_eq_exp_sq_sub_sq_exp μ F
    _ = pmfExp μ (fun assign : Item → Agent => F assign ^ 2) := by
          rw [show pmfExp μ F = 0 by
            simpa [μ, F] using lmms42F_expectation_eq_zero w hpq]
          ring
    _ = 2 * (Fintype.card Agent : ℝ)⁻¹ *
        ∑ g : Item, (w p g) ^ 2 := by
          simpa [μ, F] using lmms42F_second_moment_eq w hpq
    _ ≤ 2 * (Fintype.card Agent : ℝ)⁻¹ * alpha := by
          exact mul_le_mul_of_nonneg_left hsquare_bound hcoeff_nonneg
    _ = 2 * alpha / (Fintype.card Agent : ℝ) := by
          field_simp [hcard_ne]

/-- The induced random allocation law from independent uniform assignments. -/
noncomputable def lmms42RandomAllocationLaw
    (Agent Item : Type*) [Fintype Item] [DecidableEq Item]
    [DecidableEq Agent] [Fintype Agent] [Nonempty Agent] :
    PMF (Allocation Agent Item) :=
  (lmms42UniformAssignmentLaw Agent Item).map
    (fun assign => lmms42AllocationOfAssignment assign)

/-- The source randomized allocation rule, expressed as a direct mechanism. -/
noncomputable def lmms42UniformRandomMechanism
    (Agent Item : Type*) [Fintype Item] [DecidableEq Item]
    [DecidableEq Agent] [Fintype Agent] [Nonempty Agent] :
    RandomizedDirectFairDivisionMechanism Agent Item where
  allocationLaw := fun _reports => lmms42RandomAllocationLaw Agent Item

theorem lmms42UniformRandomMechanism_reportIndependent
    (Agent Item : Type*) [Fintype Item] [DecidableEq Item]
    [DecidableEq Agent] [Fintype Agent] [Nonempty Agent] :
    (lmms42UniformRandomMechanism Agent Item).ReportIndependent := by
  intro _reports _reports'
  rfl

theorem lmms42UniformRandomMechanism_truthful
    (Agent Item : Type*) [Fintype Item] [DecidableEq Item]
    [DecidableEq Agent] [Fintype Agent] [Nonempty Agent]
    [Fintype (Allocation Agent Item)] [DecidableEq (Allocation Agent Item)] :
    (lmms42UniformRandomMechanism Agent Item).Truthful := by
  exact
    RandomizedDirectFairDivisionMechanism.truthful_of_reportIndependent
      (lmms42UniformRandomMechanism Agent Item)
      (lmms42UniformRandomMechanism_reportIndependent Agent Item)

end

end Theorem42
end LMMS04FairDivision
