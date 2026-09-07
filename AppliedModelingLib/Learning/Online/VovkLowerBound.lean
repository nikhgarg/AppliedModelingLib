import AppliedModelingLib.Foundations.Math.FiniteOptimization
import AppliedModelingLib.Foundations.Math.ExponentialBounds
import AppliedModelingLib.Foundations.Math.Asymptotics

/-!
# Finite Vovk Lower-Bound Ingredients

Finite algebra used by the lower-bound decision game for prediction with expert
advice. The unit-coordinate loss is the loss of a unit-vector expert against a
unit-vector outcome. Its uniform discounted average is the calculation used in
the Freund--Schapire Appendix and in Vovk's lower-bound construction.
-/

open scoped BigOperators
open Filter

namespace AppliedModelingLib
namespace Learning
namespace Online

/-- The loss of a unit-coordinate expert against a unit-coordinate outcome. -/
noncomputable def unitCoordinateLoss {Coordinate : Type*}
    (expert outcome : Coordinate) : ℝ := by
  classical
  exact if expert = outcome then 1 else 0

/-- The uniform expert average of the discounted unit-coordinate losses. -/
noncomputable def vovkUniformUnitExpertMixMass {Coordinate : Type*} [Fintype Coordinate]
    (β : ℝ) : ℝ :=
  β * (Fintype.card Coordinate : ℝ)⁻¹ +
    ((Fintype.card Coordinate : ℝ) - 1) * (Fintype.card Coordinate : ℝ)⁻¹

/-- The discounted loss average of a finite distribution over unit-coordinate experts. -/
noncomputable def unitCoordinateDiscountedMixMass {Coordinate : Type*} [Fintype Coordinate]
    (β : ℝ) (expertMass : Coordinate → ℝ) (outcome : Coordinate) : ℝ :=
  ∑ expert : Coordinate, β ^ unitCoordinateLoss expert outcome * expertMass expert

/--
The finite unit-coordinate specialization of Vovk's one-step minimax condition.
For every finite expert distribution, the learner chooses a probability vector
whose loss is bounded by `c` times the discounted expert mixture at every outcome.
-/
def finiteUnitCoordinateVovkCondition {Coordinate : Type*} [Fintype Coordinate]
    (β c : ℝ) : Prop :=
  ∀ expertMass : Coordinate → ℝ, FiniteProbabilitySimplex expertMass →
    ∃ learnerMass : Coordinate → ℝ, FiniteProbabilitySimplex learnerMass ∧
      ∀ outcome : Coordinate, learnerMass outcome ≤
        c * (Real.log (unitCoordinateDiscountedMixMass β expertMass outcome) / Real.log β)

/--
Failure of the finite Vovk one-step condition supplies an expert distribution
against which every simplex learner decision has a violating outcome.
-/
theorem not_finiteUnitCoordinateVovkCondition_iff
    {Coordinate : Type*} [Fintype Coordinate] {β c : ℝ} :
    ¬ finiteUnitCoordinateVovkCondition (Coordinate := Coordinate) β c ↔
      ∃ expertMass : Coordinate → ℝ, FiniteProbabilitySimplex expertMass ∧
        ∀ learnerMass : Coordinate → ℝ, FiniteProbabilitySimplex learnerMass →
          ∃ outcome : Coordinate,
            c * (Real.log (unitCoordinateDiscountedMixMass β expertMass outcome) / Real.log β) <
              learnerMass outcome := by
  classical
  simp only [finiteUnitCoordinateVovkCondition, not_forall, not_exists,
    not_and_or, not_le]
  constructor
  · rintro ⟨expertMass, hexpertMass, hviolates⟩
    refine ⟨expertMass, hexpertMass, ?_⟩
    intro learnerMass hlearnerMass
    rcases hviolates learnerMass with hnot_learner | houtcome
    · exact False.elim (hnot_learner hlearnerMass)
    · exact houtcome
  · rintro ⟨expertMass, hexpertMass, hviolates⟩
    refine ⟨expertMass, hexpertMass, ?_⟩
    intro learnerMass
    by_cases hlearnerMass : FiniteProbabilitySimplex learnerMass
    · exact Or.inr (hviolates learnerMass hlearnerMass)
    · exact Or.inl hlearnerMass

/-- The convex mixture of finite simplex decisions with finite simplex allocation weights. -/
noncomputable def finiteSimplexMixture
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (allocation : Expert → ℝ) (expertDecision : Expert → Coordinate → ℝ) :
    Coordinate → ℝ :=
  fun coordinate => ∑ expert : Expert, allocation expert * expertDecision expert coordinate

/-- A finite convex mixture of probability vectors is again a probability vector. -/
theorem finiteSimplexMixture_mem
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (allocation : Expert → ℝ) (hallocation : FiniteProbabilitySimplex allocation)
    (expertDecision : Expert → Coordinate → ℝ)
    (hexpertDecision : ∀ expert, FiniteProbabilitySimplex (expertDecision expert)) :
    FiniteProbabilitySimplex (finiteSimplexMixture allocation expertDecision) := by
  constructor
  · intro coordinate
    exact Finset.sum_nonneg fun expert _ =>
      mul_nonneg (hallocation.1 expert) ((hexpertDecision expert).1 coordinate)
  · change (∑ coordinate : Coordinate,
      ∑ expert : Expert, allocation expert * expertDecision expert coordinate) = 1
    rw [Finset.sum_comm]
    calc
      (∑ expert : Expert, ∑ coordinate : Coordinate,
          allocation expert * expertDecision expert coordinate) =
          ∑ expert : Expert, allocation expert *
            ∑ coordinate : Coordinate, expertDecision expert coordinate := by
              apply Finset.sum_congr rfl
              intro expert _hexpert
              rw [Finset.mul_sum]
      _ = ∑ expert : Expert, allocation expert := by
        apply Finset.sum_congr rfl
        intro expert _hexpert
        rw [(hexpertDecision expert).2, mul_one]
      _ = 1 := hallocation.2

/-- A finite round in the allocation-to-decision-game reduction of the Hedge Appendix. -/
structure UnitCoordinateAllocationRound (Expert Coordinate : Type*)
    [Fintype Expert] [Fintype Coordinate] where
  allocation : Expert → ℝ
  allocation_mem : FiniteProbabilitySimplex allocation
  expertDecision : Expert → Coordinate → ℝ
  expertDecision_mem : ∀ expert, FiniteProbabilitySimplex (expertDecision expert)
  outcome : Coordinate

/-- The decision formed by mixing the experts' simplex decisions with the allocation. -/
noncomputable def UnitCoordinateAllocationRound.learnerDecision
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (round : UnitCoordinateAllocationRound Expert Coordinate) : Coordinate → ℝ :=
  finiteSimplexMixture round.allocation round.expertDecision

/-- The unit-coordinate decision loss is its coordinate at the realized outcome. -/
def unitCoordinateDecisionLoss {Coordinate : Type*}
    (decision : Coordinate → ℝ) (outcome : Coordinate) : ℝ :=
  decision outcome

/-- The allocation loss is the allocation-weighted loss of the experts' decisions. -/
noncomputable def UnitCoordinateAllocationRound.allocationLoss
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (round : UnitCoordinateAllocationRound Expert Coordinate) : ℝ :=
  ∑ expert : Expert, round.allocation expert *
    unitCoordinateDecisionLoss (round.expertDecision expert) round.outcome

/-- The learner's loss in the constructed decision game. -/
noncomputable def UnitCoordinateAllocationRound.learnerLoss
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (round : UnitCoordinateAllocationRound Expert Coordinate) : ℝ :=
  unitCoordinateDecisionLoss round.learnerDecision round.outcome

/-- The mixed decision in the Appendix reduction remains a probability vector. -/
theorem UnitCoordinateAllocationRound.learnerDecision_mem
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (round : UnitCoordinateAllocationRound Expert Coordinate) :
    FiniteProbabilitySimplex round.learnerDecision := by
  exact finiteSimplexMixture_mem round.allocation round.allocation_mem
    round.expertDecision round.expertDecision_mem

/-- Each induced allocation loss vector has the source range `[0, 1]`. -/
theorem UnitCoordinateAllocationRound.expertLoss_mem_Icc
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (round : UnitCoordinateAllocationRound Expert Coordinate) (expert : Expert) :
    0 ≤ unitCoordinateDecisionLoss (round.expertDecision expert) round.outcome ∧
      unitCoordinateDecisionLoss (round.expertDecision expert) round.outcome ≤ 1 := by
  exact ⟨(round.expertDecision_mem expert).1 round.outcome,
    finiteProbabilitySimplex_coord_le_one (round.expertDecision_mem expert) round.outcome⟩

/--
The allocation loss equals the loss of the mixed decision.  This is the exact
one-round identity in Step 6 of the Hedge Appendix reduction.
-/
theorem UnitCoordinateAllocationRound.learnerLoss_eq_allocationLoss
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (round : UnitCoordinateAllocationRound Expert Coordinate) :
    round.learnerLoss = round.allocationLoss := by
  rfl

/-- Cumulative learner loss over a list of constructed decision-game rounds. -/
noncomputable def unitCoordinateAllocationCumulativeLearnerLoss
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (rounds : List (UnitCoordinateAllocationRound Expert Coordinate)) : ℝ :=
  (rounds.map UnitCoordinateAllocationRound.learnerLoss).sum

/-- Cumulative allocation loss over a list of constructed decision-game rounds. -/
noncomputable def unitCoordinateAllocationCumulativeLoss
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (rounds : List (UnitCoordinateAllocationRound Expert Coordinate)) : ℝ :=
  (rounds.map UnitCoordinateAllocationRound.allocationLoss).sum

/-- The Appendix allocation-to-decision loss identity persists over every finite horizon. -/
theorem unitCoordinateAllocationCumulativeLearnerLoss_eq_allocation
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (rounds : List (UnitCoordinateAllocationRound Expert Coordinate)) :
    unitCoordinateAllocationCumulativeLearnerLoss rounds =
      unitCoordinateAllocationCumulativeLoss rounds := by
  unfold unitCoordinateAllocationCumulativeLearnerLoss unitCoordinateAllocationCumulativeLoss
  induction rounds with
  | nil => rfl
  | cons round rounds ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [round.learnerLoss_eq_allocationLoss, ih]

/-- Summing discounted unit-coordinate losses leaves one `β` term and unit terms elsewhere. -/
theorem sum_rpow_unitCoordinateLoss
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    (β : ℝ) (outcome : Coordinate) :
    (∑ expert : Coordinate, β ^ unitCoordinateLoss expert outcome) =
      β + (Fintype.card Coordinate : ℝ) - 1 := by
  classical
  rw [show (fun expert : Coordinate => β ^ unitCoordinateLoss expert outcome) =
      fun expert => if expert = outcome then β else 1 by
        funext expert
        simp [unitCoordinateLoss]]
  calc
    (∑ expert : Coordinate, if expert = outcome then β else 1) =
        (∑ _expert : Coordinate, (1 : ℝ)) +
          ∑ expert : Coordinate, if expert = outcome then β - 1 else 0 := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro expert _hexpert
          by_cases h : expert = outcome <;> simp [h]
    _ = (Fintype.card Coordinate : ℝ) + (β - 1) := by simp
    _ = β + (Fintype.card Coordinate : ℝ) - 1 := by ring

/-- The uniform discounted average of unit-coordinate expert losses. -/
theorem uniform_average_rpow_unitCoordinateLoss
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    (β : ℝ) (outcome : Coordinate) :
    (∑ expert : Coordinate,
        β ^ unitCoordinateLoss expert outcome * (Fintype.card Coordinate : ℝ)⁻¹) =
      β * (Fintype.card Coordinate : ℝ)⁻¹ +
        ((Fintype.card Coordinate : ℝ) - 1) * (Fintype.card Coordinate : ℝ)⁻¹ := by
  rw [← Finset.sum_mul, sum_rpow_unitCoordinateLoss]
  ring

/-- Under the uniform expert distribution, the finite discounted mixture is outcome-independent. -/
theorem unitCoordinateDiscountedMixMass_uniform
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    (β : ℝ) (outcome : Coordinate) :
    unitCoordinateDiscountedMixMass β
        (fun _expert : Coordinate => (Fintype.card Coordinate : ℝ)⁻¹) outcome =
      vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β := by
  exact uniform_average_rpow_unitCoordinateLoss β outcome

/-- The uniform discounted average is `1 - (1 - β) / |Coordinate|`. -/
theorem vovkUniformUnitExpertMixMass_eq_one_sub
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate] (β : ℝ) :
    vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β =
      1 - (1 - β) * (Fintype.card Coordinate : ℝ)⁻¹ := by
  have hcard_pos : 0 < (Fintype.card Coordinate : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Coordinate)
  rw [vovkUniformUnitExpertMixMass]
  field_simp [hcard_pos.ne']
  ring

/-- For `0 < β < 1`, the uniform discounted average is strictly positive. -/
theorem vovkUniformUnitExpertMixMass_pos
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β : ℝ} (hβ_pos : 0 < β) :
    0 < vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β := by
  have hcard_pos : 0 < (Fintype.card Coordinate : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Coordinate)
  have hcard_ge_one : 1 ≤ (Fintype.card Coordinate : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card Coordinate))
  rw [vovkUniformUnitExpertMixMass]
  have hinv_pos : 0 < (Fintype.card Coordinate : ℝ)⁻¹ := inv_pos.mpr hcard_pos
  have htail_nonneg : 0 ≤ ((Fintype.card Coordinate : ℝ) - 1) *
      (Fintype.card Coordinate : ℝ)⁻¹ :=
    mul_nonneg (sub_nonneg.mpr hcard_ge_one) hinv_pos.le
  exact add_pos_of_pos_of_nonneg (mul_pos hβ_pos hinv_pos) htail_nonneg

/-- For `β < 1`, the uniform discounted average is strictly below one. -/
theorem vovkUniformUnitExpertMixMass_lt_one
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β : ℝ} (hβ_lt_one : β < 1) :
    vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β < 1 := by
  rw [vovkUniformUnitExpertMixMass_eq_one_sub]
  have hcard_pos : 0 < (Fintype.card Coordinate : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Coordinate)
  have hgap_pos : 0 < 1 - β := sub_pos.mpr hβ_lt_one
  have hinv_pos : 0 < (Fintype.card Coordinate : ℝ)⁻¹ := inv_pos.mpr hcard_pos
  nlinarith [mul_pos hgap_pos hinv_pos]

/-- The negative logarithm of the uniform discounted average is positive. -/
theorem vovkUniformUnitExpert_neg_log_mixMass_pos
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1) :
    0 < -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) := by
  have hlog_neg :
      Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) < 0 :=
    Real.log_neg (vovkUniformUnitExpertMixMass_pos hβ_pos)
      (vovkUniformUnitExpertMixMass_lt_one hβ_lt_one)
  linarith

/--
For the uniform unit-expert mixture, the logarithmic denominator in the Vovk
lower-bound calculation is at least `(1 - β) / |Coordinate|`.
-/
theorem one_sub_le_card_mul_neg_log_vovkUniformUnitExpertMixMass
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1) :
    1 - β ≤ (Fintype.card Coordinate : ℝ) *
      -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) := by
  let x : ℝ := (1 - β) * (Fintype.card Coordinate : ℝ)⁻¹
  have hcard_pos : 0 < (Fintype.card Coordinate : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Coordinate)
  have hx_nonneg : 0 ≤ x :=
    mul_nonneg (sub_nonneg.mpr hβ_lt_one.le) (inv_nonneg.mpr hcard_pos.le)
  have hx_lt_one : x < 1 := by
    apply sub_pos.mp
    change 0 < 1 - (1 - β) * (Fintype.card Coordinate : ℝ)⁻¹
    rw [← vovkUniformUnitExpertMixMass_eq_one_sub]
    exact vovkUniformUnitExpertMixMass_pos hβ_pos
  have hlog : x ≤ -Real.log (1 - x) :=
    AppliedModelingLib.Math.le_neg_log_one_sub hx_nonneg hx_lt_one
  have hmul : (Fintype.card Coordinate : ℝ) * x ≤
      (Fintype.card Coordinate : ℝ) * -Real.log (1 - x) :=
    mul_le_mul_of_nonneg_left hlog hcard_pos.le
  rw [vovkUniformUnitExpertMixMass_eq_one_sub]
  change 1 - β ≤ (Fintype.card Coordinate : ℝ) * -Real.log (1 - x)
  rw [show 1 - β = (Fintype.card Coordinate : ℝ) * x by
    dsimp [x]
    field_simp [hcard_pos.ne']]
  exact hmul

/--
For the uniform unit-expert mixture, the logarithmic denominator in the Vovk
lower-bound calculation is at most `(1 - β) / (1 - (1 - β) / |Coordinate|)`.
-/
theorem card_mul_neg_log_vovkUniformUnitExpertMixMass_le
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1) :
    (Fintype.card Coordinate : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) ≤
      (1 - β) /
        (1 - (1 - β) * (Fintype.card Coordinate : ℝ)⁻¹) := by
  let x : ℝ := (1 - β) * (Fintype.card Coordinate : ℝ)⁻¹
  have hcard_pos : 0 < (Fintype.card Coordinate : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Coordinate)
  have hx_nonneg : 0 ≤ x :=
    mul_nonneg (sub_nonneg.mpr hβ_lt_one.le) (inv_nonneg.mpr hcard_pos.le)
  have hx_lt_one : x < 1 := by
    apply sub_pos.mp
    change 0 < 1 - (1 - β) * (Fintype.card Coordinate : ℝ)⁻¹
    rw [← vovkUniformUnitExpertMixMass_eq_one_sub]
    exact vovkUniformUnitExpertMixMass_pos hβ_pos
  have hlog : -Real.log (1 - x) ≤ x / (1 - x) :=
    AppliedModelingLib.Math.neg_log_one_sub_le_div_self hx_nonneg hx_lt_one
  have hmul : (Fintype.card Coordinate : ℝ) * -Real.log (1 - x) ≤
      (Fintype.card Coordinate : ℝ) * (x / (1 - x)) :=
    mul_le_mul_of_nonneg_left hlog hcard_pos.le
  rw [vovkUniformUnitExpertMixMass_eq_one_sub]
  change (Fintype.card Coordinate : ℝ) * -Real.log (1 - x) ≤ (1 - β) / (1 - x)
  calc
    (Fintype.card Coordinate : ℝ) * -Real.log (1 - x) ≤
        (Fintype.card Coordinate : ℝ) * (x / (1 - x)) := hmul
    _ = ((Fintype.card Coordinate : ℝ) * x) / (1 - x) := by ring
    _ = (1 - β) / (1 - x) := by
      congr 1
      dsimp [x]
      field_simp [hcard_pos.ne']

/--
The finite Eq. (31) logarithmic denominator converges to `1 - β` as the number
of unit-coordinate experts tends to infinity.
-/
theorem tendsto_card_mul_neg_log_vovkUniformUnitExpertMixMass_fin_succ
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1) :
    Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin (n + 1)) β))
      atTop (nhds (1 - β)) := by
  have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 0) := by
    simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hden : Tendsto
      (fun n : ℕ => 1 - (1 - β) * ((n + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 1) := by
    have hmul : Tendsto
        (fun n : ℕ => (1 - β) * ((n + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hinv)
    simpa using (tendsto_const_nhds.sub hmul)
  have hupper : Tendsto
      (fun n : ℕ => (1 - β) / (1 - (1 - β) * ((n + 1 : ℕ) : ℝ)⁻¹))
      atTop (nhds (1 - β)) := by
    have hinvden : Tendsto
        (fun n : ℕ => (1 - (1 - β) * ((n + 1 : ℕ) : ℝ)⁻¹)⁻¹) atTop (nhds 1) := by
      simpa using hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinvden)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards with n
    simpa [Fintype.card_fin, vovkUniformUnitExpertMixMass_eq_one_sub] using
      (one_sub_le_card_mul_neg_log_vovkUniformUnitExpertMixMass
        (Coordinate := Fin (n + 1)) hβ_pos hβ_lt_one)
  · filter_upwards with n
    simpa [Fintype.card_fin, vovkUniformUnitExpertMixMass_eq_one_sub] using
      (card_mul_neg_log_vovkUniformUnitExpertMixMass_le
        (Coordinate := Fin (n + 1)) hβ_pos hβ_lt_one)

/-- The finite Eq. (31) coefficient lower bound tends to `log (1 / β) / (1 - β)`. -/
theorem tendsto_vovkCoefficientLowerBound_fin_succ
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1) :
    Tendsto
      (fun n : ℕ => (-Real.log β) /
        (((n + 1 : ℕ) : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin (n + 1)) β)))
      atTop (nhds ((-Real.log β) / (1 - β))) := by
  have hden := tendsto_card_mul_neg_log_vovkUniformUnitExpertMixMass_fin_succ
    hβ_pos hβ_lt_one
  have hinv : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin (n + 1)) β))⁻¹)
      atTop (nhds ((1 - β)⁻¹)) := by
    exact hden.inv₀ (ne_of_gt (sub_pos.mpr hβ_lt_one))
  simpa [div_eq_mul_inv] using ((tendsto_const_nhds (x := -Real.log β)).mul hinv)

/-- The finite Eq. (32) additive lower-bound threshold tends to `1 / (1 - β)`. -/
theorem tendsto_vovkAdditiveLowerBound_fin_succ
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1) :
    Tendsto
      (fun n : ℕ => 1 /
        (((n + 1 : ℕ) : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin (n + 1)) β)))
      atTop (nhds (1 / (1 - β))) := by
  have hden := tendsto_card_mul_neg_log_vovkUniformUnitExpertMixMass_fin_succ
    hβ_pos hβ_lt_one
  have hinv : Tendsto
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin (n + 1)) β))⁻¹)
      atTop (nhds ((1 - β)⁻¹)) := by
    exact hden.inv₀ (ne_of_gt (sub_pos.mpr hβ_lt_one))
  simpa [one_div] using hinv

/--
If the finite Vovk alternatives hold for every number of unit-coordinate
experts, their limiting alternative has the Hedge Theorem-3 constants.
-/
theorem vovkFiniteAlternative_limit
    {β c a : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hfinite : ∀ n : ℕ,
      ((-Real.log β) /
          (((n + 1 : ℕ) : ℝ) *
            -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin (n + 1)) β)) ≤ c) ∨
        (1 /
          (((n + 1 : ℕ) : ℝ) *
            -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin (n + 1)) β)) ≤ a)) :
    (-Real.log β) / (1 - β) ≤ c ∨ 1 / (1 - β) ≤ a := by
  by_contra hlimit
  push Not at hlimit
  rcases hlimit with ⟨hc_lt, ha_lt⟩
  have hc_event : ∀ᶠ n : ℕ in atTop,
      c < (-Real.log β) /
        (((n + 1 : ℕ) : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin (n + 1)) β)) :=
    (tendsto_vovkCoefficientLowerBound_fin_succ hβ_pos hβ_lt_one).eventually
      (eventually_gt_nhds hc_lt)
  have ha_event : ∀ᶠ n : ℕ in atTop,
      a < 1 /
        (((n + 1 : ℕ) : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin (n + 1)) β)) :=
    (tendsto_vovkAdditiveLowerBound_fin_succ hβ_pos hβ_lt_one).eventually
      (eventually_gt_nhds ha_lt)
  obtain ⟨n, hcn, han⟩ := (hc_event.and ha_event).exists
  rcases hfinite n with hcoef | hadd
  · exact (not_lt_of_ge hcoef) hcn
  · exact (not_lt_of_ge hadd) han

/--
The same limiting alternative when the finite games start at two coordinates.
The Section-6 iid construction needs a nontrivial coordinate type, so this
shifted form is the one consumed by the fully formal finite-game argument.
-/
theorem vovkFiniteAlternative_limit_fin_succ_succ
    {β c a : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hfinite : ∀ n : ℕ,
      ((-Real.log β) /
          ((((n + 1) + 1 : ℕ) : ℝ) *
            -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin ((n + 1) + 1)) β)) ≤ c) ∨
        (1 /
          ((((n + 1) + 1 : ℕ) : ℝ) *
            -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin ((n + 1) + 1)) β)) ≤ a)) :
    (-Real.log β) / (1 - β) ≤ c ∨ 1 / (1 - β) ≤ a := by
  by_contra hlimit
  push Not at hlimit
  rcases hlimit with ⟨hc_lt, ha_lt⟩
  have hcoefficient_tendsto : Tendsto
      (fun n : ℕ => (-Real.log β) /
        ((((n + 1) + 1 : ℕ) : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin ((n + 1) + 1)) β)))
      atTop (nhds ((-Real.log β) / (1 - β))) := by
    simpa [Function.comp_def] using
      (tendsto_vovkCoefficientLowerBound_fin_succ hβ_pos hβ_lt_one).comp
        (tendsto_add_atTop_nat 1)
  have hadditive_tendsto : Tendsto
      (fun n : ℕ => 1 /
        ((((n + 1) + 1 : ℕ) : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin ((n + 1) + 1)) β)))
      atTop (nhds (1 / (1 - β))) := by
    simpa [Function.comp_def] using
      (tendsto_vovkAdditiveLowerBound_fin_succ hβ_pos hβ_lt_one).comp
        (tendsto_add_atTop_nat 1)
  have hc_event : ∀ᶠ n : ℕ in atTop,
      c < (-Real.log β) /
        ((((n + 1) + 1 : ℕ) : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin ((n + 1) + 1)) β)) :=
    hcoefficient_tendsto.eventually (eventually_gt_nhds hc_lt)
  have ha_event : ∀ᶠ n : ℕ in atTop,
      a < 1 /
        ((((n + 1) + 1 : ℕ) : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Fin ((n + 1) + 1)) β)) :=
    hadditive_tendsto.eventually (eventually_gt_nhds ha_lt)
  obtain ⟨n, hcn, han⟩ := (hc_event.and ha_event).exists
  rcases hfinite n with hcoef | hadd
  · exact (not_lt_of_ge hcoef) hcn
  · exact (not_lt_of_ge hadd) han

/--
Vovk's coefficient alternative yields the Appendix Eq. (32) finite
alternative once the finite unit-coordinate coefficient lower bound is known.
-/
theorem finiteVovkAlternative_of_coefficientLower
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β coefficient c a : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hcoefficient_lower : (-Real.log β) /
      ((Fintype.card Coordinate : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)) ≤ coefficient)
    (halternative : coefficient ≤ c ∨ coefficient / (-Real.log β) ≤ a) :
    (-Real.log β) /
        ((Fintype.card Coordinate : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)) ≤ c ∨
      1 /
        ((Fintype.card Coordinate : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)) ≤ a := by
  rcases halternative with hcoefficient | hadditive
  · exact Or.inl (hcoefficient_lower.trans hcoefficient)
  · right
    have hlog_pos : 0 < -Real.log β := by
      exact neg_pos.mpr (Real.log_neg hβ_pos hβ_lt_one)
    have hlog_ne : Real.log β ≠ 0 := by
      intro hlog_zero
      rw [hlog_zero] at hlog_pos
      exact (lt_irrefl (0 : ℝ)) (by simpa using hlog_pos)
    have hden_pos : 0 < (Fintype.card Coordinate : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) :=
      mul_pos
        (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Coordinate))
        (vovkUniformUnitExpert_neg_log_mixMass_pos hβ_pos hβ_lt_one)
    calc
      1 /
          ((Fintype.card Coordinate : ℝ) *
            -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)) =
          ((-Real.log β) /
            ((Fintype.card Coordinate : ℝ) *
              -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β))) /
            (-Real.log β) := by
              field_simp [hden_pos.ne', hlog_ne]
      _ ≤ coefficient / (-Real.log β) :=
        div_le_div_of_nonneg_right hcoefficient_lower hlog_pos.le
      _ ≤ a := hadditive

/--
The finite uniform-mixture lower bound behind Vovk's coefficient `c(β)`.
It is the one-step necessary condition obtained by testing the minimax property
against the uniform distribution over the unit-coordinate experts.
-/
theorem finiteUnitCoordinateVovkCondition_coefficient_lower
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β c : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hcondition : finiteUnitCoordinateVovkCondition (Coordinate := Coordinate) β c) :
    -Real.log β /
        ((Fintype.card Coordinate : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)) ≤ c := by
  classical
  obtain ⟨learnerMass, hlearnerMass, hlearnerBound⟩ :=
    hcondition (fun _expert : Coordinate => (Fintype.card Coordinate : ℝ)⁻¹)
      uniformProbabilityMass_finiteProbabilitySimplex
  obtain ⟨outcome, houtcome⟩ := exists_finiteMax_eq learnerMass
  have hlearnerLower : (Fintype.card Coordinate : ℝ)⁻¹ ≤ learnerMass outcome := by
    calc
      (Fintype.card Coordinate : ℝ)⁻¹ ≤ finiteMax learnerMass :=
        finiteProbabilitySimplex_inv_card_le_finiteMax learnerMass hlearnerMass
      _ = learnerMass outcome := houtcome
  have hcoordinate : (Fintype.card Coordinate : ℝ)⁻¹ ≤
      c * (Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) /
        Real.log β) := by
    calc
      (Fintype.card Coordinate : ℝ)⁻¹ ≤ learnerMass outcome := hlearnerLower
      _ ≤ c *
          (Real.log (unitCoordinateDiscountedMixMass β
            (fun _expert : Coordinate => (Fintype.card Coordinate : ℝ)⁻¹) outcome) /
              Real.log β) := hlearnerBound outcome
      _ = c * (Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) /
          Real.log β) := by rw [unitCoordinateDiscountedMixMass_uniform]
  let k : ℝ := Fintype.card Coordinate
  let a : ℝ := -Real.log β
  let b : ℝ := -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)
  have hk_pos : 0 < k := by
    dsimp [k]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Coordinate)
  have ha_pos : 0 < a := by
    dsimp [a]
    exact neg_pos.mpr (Real.log_neg hβ_pos hβ_lt_one)
  have hb_pos : 0 < b := by
    dsimp [b]
    exact vovkUniformUnitExpert_neg_log_mixMass_pos hβ_pos hβ_lt_one
  have hcoordinate' : k⁻¹ ≤ c * (b / a) := by
    dsimp [k, a, b]
    rw [show Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) /
        Real.log β =
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) /
          -Real.log β by ring] at hcoordinate
    exact hcoordinate
  have hscaled : a / k ≤ c * b := by
    calc
      a / k = k⁻¹ * a := by ring
      _ ≤ (c * (b / a)) * a := mul_le_mul_of_nonneg_right hcoordinate' ha_pos.le
      _ = c * b := by
        field_simp [ha_pos.ne']
  change a / (k * b) ≤ c
  calc
    a / (k * b) = (a / k) / b := by
      field_simp [hk_pos.ne', hb_pos.ne']
    _ ≤ c := (div_le_iff₀ hb_pos).mpr hscaled

/--
Any proposed coefficient below the finite Eq. (31) lower bound has a concrete
one-step witness distribution and a violating outcome for every learner mass.
-/
theorem exists_finiteUnitCoordinateVovkWitness_of_lt_coefficient_lower
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β c : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hc_lt : c < (-Real.log β) /
      ((Fintype.card Coordinate : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β))) :
    ∃ expertMass : Coordinate → ℝ, FiniteProbabilitySimplex expertMass ∧
      ∀ learnerMass : Coordinate → ℝ, FiniteProbabilitySimplex learnerMass →
        ∃ outcome : Coordinate,
          c * (Real.log (unitCoordinateDiscountedMixMass β expertMass outcome) / Real.log β) <
            learnerMass outcome := by
  apply not_finiteUnitCoordinateVovkCondition_iff.mp
  intro hcondition
  exact (not_lt_of_ge
    (finiteUnitCoordinateVovkCondition_coefficient_lower hβ_pos hβ_lt_one hcondition)) hc_lt

/--
Below the finite Eq. (31) coefficient, the uniform unit-expert distribution
itself supplies a learner-dependent outcome that violates the one-step bound.
-/
theorem exists_uniformUnitCoordinate_violation_of_lt_coefficient_lower
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β c : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hc_lt : c < (-Real.log β) /
      ((Fintype.card Coordinate : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)))
    (learnerMass : Coordinate → ℝ) (hlearnerMass : FiniteProbabilitySimplex learnerMass) :
    ∃ outcome : Coordinate,
      c * (Real.log (unitCoordinateDiscountedMixMass β
        (fun _expert : Coordinate => (Fintype.card Coordinate : ℝ)⁻¹) outcome) / Real.log β) <
        learnerMass outcome := by
  obtain ⟨outcome, houtcome⟩ := exists_finiteMax_eq learnerMass
  have hcoordinate : (Fintype.card Coordinate : ℝ)⁻¹ ≤ learnerMass outcome := by
    calc
      (Fintype.card Coordinate : ℝ)⁻¹ ≤ finiteMax learnerMass :=
        finiteProbabilitySimplex_inv_card_le_finiteMax learnerMass hlearnerMass
      _ = learnerMass outcome := houtcome
  refine ⟨outcome, ?_⟩
  rw [unitCoordinateDiscountedMixMass_uniform]
  let k : ℝ := Fintype.card Coordinate
  let a : ℝ := -Real.log β
  let b : ℝ := -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)
  have hk_pos : 0 < k := by
    dsimp [k]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Coordinate)
  have ha_pos : 0 < a := by
    dsimp [a]
    exact neg_pos.mpr (Real.log_neg hβ_pos hβ_lt_one)
  have hb_pos : 0 < b := by
    dsimp [b]
    exact vovkUniformUnitExpert_neg_log_mixMass_pos hβ_pos hβ_lt_one
  have hc_lt' : c < a / (k * b) := by
    simpa [k, a, b] using hc_lt
  have hratio_pos : 0 < b / a := div_pos hb_pos ha_pos
  have hscaled : c * (b / a) < (a / (k * b)) * (b / a) :=
    mul_lt_mul_of_pos_right hc_lt' hratio_pos
  have hformula : (a / (k * b)) * (b / a) = k⁻¹ := by
    field_simp [hk_pos.ne', ha_pos.ne', hb_pos.ne']
  calc
    c * (Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) /
        Real.log β) = c * (b / a) := by
          dsimp [a, b]
          ring
    _ < (a / (k * b)) * (b / a) := hscaled
    _ = k⁻¹ := hformula
    _ = (Fintype.card Coordinate : ℝ)⁻¹ := rfl
    _ ≤ learnerMass outcome := hcoordinate

/--
The deterministic outcome selector supplied by the uniform unit-expert local
obstruction below the finite Eq. (31) coefficient.
-/
noncomputable def uniformUnitCoordinateViolatingOutcome
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β c : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hc_lt : c < (-Real.log β) /
      ((Fintype.card Coordinate : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)))
    (learnerMass : Coordinate → ℝ) (hlearnerMass : FiniteProbabilitySimplex learnerMass) :
    Coordinate :=
  Classical.choose
    (exists_uniformUnitCoordinate_violation_of_lt_coefficient_lower
      hβ_pos hβ_lt_one hc_lt learnerMass hlearnerMass)

/-- The selected outcome strictly violates the uniform one-step mixture inequality. -/
theorem uniformUnitCoordinateViolatingOutcome_spec
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β c : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hc_lt : c < (-Real.log β) /
      ((Fintype.card Coordinate : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)))
    (learnerMass : Coordinate → ℝ) (hlearnerMass : FiniteProbabilitySimplex learnerMass) :
    c * (Real.log (unitCoordinateDiscountedMixMass β
      (fun _expert : Coordinate => (Fintype.card Coordinate : ℝ)⁻¹)
      (uniformUnitCoordinateViolatingOutcome
        hβ_pos hβ_lt_one hc_lt learnerMass hlearnerMass)) /
        Real.log β) <
      learnerMass
        (uniformUnitCoordinateViolatingOutcome
          hβ_pos hβ_lt_one hc_lt learnerMass hlearnerMass) := by
  exact Classical.choose_spec
    (exists_uniformUnitCoordinate_violation_of_lt_coefficient_lower
      hβ_pos hβ_lt_one hc_lt learnerMass hlearnerMass)

end Online
end Learning
end AppliedModelingLib
