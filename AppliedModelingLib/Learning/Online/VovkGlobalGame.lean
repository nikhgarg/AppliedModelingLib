import AppliedModelingLib.Learning.Online.UnitCoordinateGame
import AppliedModelingLib.Foundations.Probability.FiniteTypeLogMass
import AppliedModelingLib.Foundations.Math.Asymptotics

/-!
# Finite game-tree layer of Vovk's global lower-bound argument

Vovk's Section 6 turns a failed one-step inequality into an adaptive global
game.  This file formalizes the deterministic part of that construction for the
finite unit-coordinate game: experts make pure coordinate predictions, the
learner policy sees their decisions, and an outcome selector responds to the
learner's resulting simplex decision.  The probabilistic iid-expert argument
that supplies a low-loss expert is a subsequent layer.
-/

open scoped BigOperators
open Filter

namespace AppliedModelingLib
namespace Learning
namespace Online

/-- The simplex decision concentrated at a single coordinate. -/
noncomputable def unitCoordinatePureDecision
    {Coordinate : Type*} (coordinate : Coordinate) : Coordinate → ℝ :=
  fun candidate => unitCoordinateLoss coordinate candidate

/-- A pure coordinate decision is a finite probability simplex. -/
theorem unitCoordinatePureDecision_mem
    {Coordinate : Type*} [Fintype Coordinate] (coordinate : Coordinate) :
    FiniteProbabilitySimplex (unitCoordinatePureDecision coordinate) := by
  classical
  constructor
  · intro candidate
    change 0 ≤ if coordinate = candidate then (1 : ℝ) else 0
    split_ifs <;> norm_num
  · simp [unitCoordinatePureDecision, unitCoordinateLoss]

/-- A time-indexed table of pure coordinate predictions, one for each expert. -/
abbrev UnitCoordinatePureExpertTable (Expert Coordinate : Type*) :=
  ℕ → Expert → Coordinate

/-- The finite uniform law for a horizon of iid pure-expert prediction rows. -/
noncomputable def unitCoordinateUniformExpertTableLaw
    (Expert Coordinate : Type*) [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    (horizon : ℕ) : PMF (Fin horizon → Expert → Coordinate) :=
  uniformPMF (Fin horizon → Expert → Coordinate)

/--
Transpose the time-major representation of a finite expert table to the
expert-major representation used by the independent-experts product law.
-/
def unitCoordinateFiniteTableTransposeEquiv
    {Expert Coordinate : Type*} {horizon : ℕ} :
    (Expert → Fin horizon → Coordinate) ≃ (Fin horizon → Expert → Coordinate) where
  toFun table time expert := table expert time
  invFun table expert time := table time expert
  left_inv := by
    intro table
    rfl
  right_inv := by
    intro table
    rfl

/-- One uniform pure-expert row is exactly the iid product of coordinate laws. -/
theorem uniformPMF_pureExpertRow_eq_iid
    (Expert Coordinate : Type*) [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate] :
    uniformPMF (Expert → Coordinate) =
      pmfProduct Expert Coordinate (uniformPMF Coordinate) := by
  symm
  exact pmfProduct_uniformPMF_eq_uniformPMF_fun Expert Coordinate

/-- The uniform finite table law factors into independent uniform expert rows. -/
theorem unitCoordinateUniformExpertTableLaw_eq_iid_rows
    (Expert Coordinate : Type*) [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    (horizon : ℕ) :
    unitCoordinateUniformExpertTableLaw Expert Coordinate horizon =
      pmfProduct (Fin horizon) (Expert → Coordinate) (uniformPMF (Expert → Coordinate)) := by
  unfold unitCoordinateUniformExpertTableLaw
  symm
  exact pmfProduct_uniformPMF_eq_uniformPMF_fun (Fin horizon) (Expert → Coordinate)

/-- The simplex decisions induced by one row of a pure-expert table. -/
noncomputable def unitCoordinatePureExpertDecisions
    {Expert Coordinate : Type*} (table : UnitCoordinatePureExpertTable Expert Coordinate)
    (time : ℕ) : Expert → Coordinate → ℝ :=
  fun expert => unitCoordinatePureDecision (table time expert)

/-- Every table entry supplies a valid simplex decision. -/
theorem unitCoordinatePureExpertDecisions_mem
    {Expert Coordinate : Type*} [Fintype Coordinate]
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (time : ℕ) :
    ∀ expert, FiniteProbabilitySimplex (unitCoordinatePureExpertDecisions table time expert) := by
  intro expert
  exact unitCoordinatePureDecision_mem (table time expert)

/--
The uniform iid law of a pure expert has the Appendix Eq. (29) discounted
moment.  This identifies the finite probability law used in Vovk's Section 6
with the algebraic discounted mixture used in the Hedge Appendix.
-/
theorem pmfExp_uniform_unitCoordinateDiscountedLoss
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    (β : ℝ) (outcome : Coordinate) :
    pmfExp (uniformPMF Coordinate)
        (fun expert => β ^ unitCoordinateLoss expert outcome) =
      vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β := by
  classical
  unfold pmfExp
  simp only [uniformPMF_apply_toReal]
  simpa [unitCoordinateDiscountedMixMass, mul_comm] using
    (unitCoordinateDiscountedMixMass_uniform β outcome)

/--
At the dual parameter `log β`, the finite MGF of the uniform unit-coordinate
loss is exactly the discounted mass from Appendix Eq. (29).
-/
theorem finiteMGF_uniform_unitCoordinateLoss_log
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    {β : ℝ} (hβ_pos : 0 < β) (outcome : Coordinate) :
    Probability.finiteMGF (uniformPMF Coordinate)
      (fun expert => unitCoordinateLoss expert outcome) (Real.log β) =
        vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β := by
  calc
    Probability.finiteMGF (uniformPMF Coordinate)
        (fun expert => unitCoordinateLoss expert outcome) (Real.log β) =
      pmfExp (uniformPMF Coordinate)
        (fun expert => β ^ unitCoordinateLoss expert outcome) := by
          unfold Probability.finiteMGF pmfExp
          refine Finset.sum_congr rfl ?_
          intro expert _hexpert
          congr 1
          by_cases hexpert_outcome : expert = outcome
          · simp [unitCoordinateLoss, hexpert_outcome, Real.exp_log hβ_pos]
          · simp [unitCoordinateLoss, hexpert_outcome]
    _ = vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β :=
      pmfExp_uniform_unitCoordinateDiscountedLoss β outcome

/--
The uniformly weighted exponential first moment of the unit-coordinate loss
at dual parameter `log β` is `β / K`.
-/
theorem uniform_unitCoordinateLoss_weightedExp_log
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    {β : ℝ} (hβ_pos : 0 < β) (outcome : Coordinate) :
    (∑ expert : Coordinate,
      (uniformPMF Coordinate expert).toReal *
        (unitCoordinateLoss expert outcome *
          Real.exp (Real.log β * unitCoordinateLoss expert outcome))) =
        β * (Fintype.card Coordinate : ℝ)⁻¹ := by
  simp only [uniformPMF_apply_toReal]
  rw [show (fun expert : Coordinate =>
      (Fintype.card Coordinate : ℝ)⁻¹ *
        (unitCoordinateLoss expert outcome *
          Real.exp (Real.log β * unitCoordinateLoss expert outcome))) =
      fun expert => if expert = outcome then β * (Fintype.card Coordinate : ℝ)⁻¹ else 0 by
        funext expert
        by_cases hexpert_outcome : expert = outcome
        · simp [unitCoordinateLoss, hexpert_outcome, Real.exp_log hβ_pos]
          ring
        · simp [unitCoordinateLoss, hexpert_outcome]]
  simp

/--
The centered uniform unit-coordinate score has an explicit exponentially
weighted first moment at the dual point `log β`.  Its zero determines the
interior Cramer tilt used in Vovk's Section 6.
-/
theorem uniform_unitCoordinateLoss_sub_weightedExp_log
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    {β : ℝ} (hβ_pos : 0 < β) (outcome : Coordinate) (z : ℝ) :
    (∑ expert : Coordinate,
      (uniformPMF Coordinate expert).toReal *
        ((unitCoordinateLoss expert outcome - z) *
          Real.exp (Real.log β * (unitCoordinateLoss expert outcome - z)))) =
      Real.exp (-(Real.log β * z)) *
        (β * (Fintype.card Coordinate : ℝ)⁻¹ -
          z * vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) := by
  have hpoint : ∀ expert : Coordinate,
      (uniformPMF Coordinate expert).toReal *
          ((unitCoordinateLoss expert outcome - z) *
            Real.exp (Real.log β * (unitCoordinateLoss expert outcome - z))) =
        Real.exp (-(Real.log β * z)) *
          ((uniformPMF Coordinate expert).toReal *
              (unitCoordinateLoss expert outcome *
                Real.exp (Real.log β * unitCoordinateLoss expert outcome)) -
            z * ((uniformPMF Coordinate expert).toReal *
              Real.exp (Real.log β * unitCoordinateLoss expert outcome))) := by
    intro expert
    rw [show Real.log β * (unitCoordinateLoss expert outcome - z) =
      -(Real.log β * z) + Real.log β * unitCoordinateLoss expert outcome by ring]
    rw [Real.exp_add]
    ring
  calc
    (∑ expert : Coordinate,
        (uniformPMF Coordinate expert).toReal *
          ((unitCoordinateLoss expert outcome - z) *
            Real.exp (Real.log β * (unitCoordinateLoss expert outcome - z)))) =
      ∑ expert : Coordinate, Real.exp (-(Real.log β * z)) *
        ((uniformPMF Coordinate expert).toReal *
            (unitCoordinateLoss expert outcome *
              Real.exp (Real.log β * unitCoordinateLoss expert outcome)) -
          z * ((uniformPMF Coordinate expert).toReal *
            Real.exp (Real.log β * unitCoordinateLoss expert outcome))) := by
          exact Finset.sum_congr rfl (fun expert _ => hpoint expert)
    _ = Real.exp (-(Real.log β * z)) *
        ((∑ expert : Coordinate,
            (uniformPMF Coordinate expert).toReal *
              (unitCoordinateLoss expert outcome *
                Real.exp (Real.log β * unitCoordinateLoss expert outcome))) -
          z * (∑ expert : Coordinate,
            (uniformPMF Coordinate expert).toReal *
              Real.exp (Real.log β * unitCoordinateLoss expert outcome))) := by
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = Real.exp (-(Real.log β * z)) *
        (β * (Fintype.card Coordinate : ℝ)⁻¹ -
          z * vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) := by
          rw [uniform_unitCoordinateLoss_weightedExp_log hβ_pos outcome]
          change Real.exp (-(Real.log β * z)) *
            (β * (Fintype.card Coordinate : ℝ)⁻¹ -
              z * Probability.finiteMGF (uniformPMF Coordinate)
                (fun expert => unitCoordinateLoss expert outcome) (Real.log β)) = _
          rw [finiteMGF_uniform_unitCoordinateLoss_log hβ_pos outcome]

/-- The stationary centered-loss threshold induced by the `log β` exponential tilt. -/
noncomputable def unitCoordinateVovkCramerThreshold
    {Coordinate : Type*} [Fintype Coordinate] (β : ℝ) : ℝ :=
  β * (Fintype.card Coordinate : ℝ)⁻¹ /
    vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β

/-- The `log β` tilt is stationary for the source's centered unit-coordinate score. -/
theorem uniform_unitCoordinateLoss_sub_weightedExp_log_eq_zero
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    {β : ℝ} (hβ_pos : 0 < β) (outcome : Coordinate) :
    (∑ expert : Coordinate,
      (uniformPMF Coordinate expert).toReal *
        ((unitCoordinateLoss expert outcome -
            unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β) *
          Real.exp (Real.log β *
            (unitCoordinateLoss expert outcome -
              unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β)))) = 0 := by
  rw [uniform_unitCoordinateLoss_sub_weightedExp_log hβ_pos outcome]
  have hmass_pos : 0 < vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β :=
    vovkUniformUnitExpertMixMass_pos hβ_pos
  have hbracket : β * (Fintype.card Coordinate : ℝ)⁻¹ -
      unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β *
        vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β = 0 := by
    unfold unitCoordinateVovkCramerThreshold
    field_simp [hmass_pos.ne']
    ring
  rw [hbracket]
  simp

/--
The exact finite Chernoff exponent of the stationary centered uniform
unit-coordinate loss.  This is the source Cramer transform evaluated at the
explicit `log β` minimizer.
-/
theorem finiteChernoffRate_uniform_unitCoordinateLoss_sub
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    {β : ℝ} (hβ_pos : 0 < β) (outcome : Coordinate) :
    Probability.finiteChernoffRate (uniformPMF Coordinate)
      (fun expert => unitCoordinateLoss expert outcome -
        unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β) =
      Real.log β * unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β -
        Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) := by
  let threshold : ℝ := unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β
  let base : ℝ :=
    Real.exp (-(Real.log β * threshold)) *
      vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β
  have hbase_pos : 0 < base := by
    dsimp [base]
    exact mul_pos (Real.exp_pos _) (vovkUniformUnitExpertMixMass_pos hβ_pos)
  have hstationary :
      (∑ expert : Coordinate,
        (uniformPMF Coordinate expert).toReal *
          ((unitCoordinateLoss expert outcome - threshold) *
            Real.exp (Real.log β * (unitCoordinateLoss expert outcome - threshold)))) = 0 := by
    simpa [threshold] using
      (uniform_unitCoordinateLoss_sub_weightedExp_log_eq_zero hβ_pos outcome)
  have hwitness : Probability.finiteLogMGF (uniformPMF Coordinate)
      (fun expert => unitCoordinateLoss expert outcome - threshold) (Real.log β) =
        Real.log base := by
    rw [Probability.finiteLogMGF_sub_const,
      Probability.finiteLogMGF,
      finiteMGF_uniform_unitCoordinateLoss_log hβ_pos outcome]
    dsimp [base]
    rw [Real.log_mul (Real.exp_pos _).ne'
      (vovkUniformUnitExpertMixMass_pos hβ_pos).ne', Real.log_exp]
    ring
  have hrate := Probability.finiteChernoffRate_eq_neg_log_base_of_convex_stationary
    (uniformPMF Coordinate)
    (fun expert => unitCoordinateLoss expert outcome - threshold)
    (Probability.finiteLogMGF_convex (uniformPMF Coordinate)
      (fun expert => unitCoordinateLoss expert outcome - threshold))
    hstationary hwitness
  dsimp [threshold, base] at hrate ⊢
  rw [hrate, Real.log_mul (Real.exp_pos _).ne'
    (vovkUniformUnitExpertMixMass_pos hβ_pos).ne', Real.log_exp]
  ring

/-- The stationary Cramer threshold is strictly inside the unit-loss interval. -/
theorem unitCoordinateVovkCramerThreshold_pos_lt_one
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate] [Nontrivial Coordinate]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1) :
    0 < unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β ∧
      unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β < 1 := by
  let K : ℝ := Fintype.card Coordinate
  let mass : ℝ := vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β
  have hK_pos : 0 < K := by
    dsimp [K]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Coordinate)
  have hK_gt_one : 1 < K := by
    dsimp [K]
    exact_mod_cast Fintype.one_lt_card
  have hmass_pos : 0 < mass := by
    dsimp [mass]
    exact vovkUniformUnitExpertMixMass_pos hβ_pos
  have hthreshold : unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β =
      β / (K * mass) := by
    unfold unitCoordinateVovkCramerThreshold
    dsimp [K, mass]
    field_simp [hK_pos.ne', hmass_pos.ne']
  have hmass_mul : K * mass = β + K - 1 := by
    dsimp [K, mass, vovkUniformUnitExpertMixMass]
    field_simp [hK_pos.ne']
    ring
  have hden_gt_beta : β < K * mass := by
    rw [hmass_mul]
    linarith
  constructor
  · rw [hthreshold]
    exact div_pos hβ_pos (lt_trans hβ_pos hden_gt_beta)
  · rw [hthreshold]
    exact (div_lt_one (lt_trans hβ_pos hden_gt_beta)).mpr hden_gt_beta

/-- The stationary Cramer threshold is at most the uncentered uniform loss mean. -/
theorem unitCoordinateVovkCramerThreshold_le_uniformMean
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_le_one : β ≤ 1) :
    unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β ≤
      (Fintype.card Coordinate : ℝ)⁻¹ := by
  let K : ℝ := Fintype.card Coordinate
  let mass : ℝ := vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β
  have hK_pos : 0 < K := by
    dsimp [K]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Coordinate)
  have hmass_pos : 0 < mass := by
    dsimp [mass]
    exact vovkUniformUnitExpertMixMass_pos hβ_pos
  have hthreshold : unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β =
      β / (K * mass) := by
    unfold unitCoordinateVovkCramerThreshold
    dsimp [K, mass]
    field_simp [hK_pos.ne', hmass_pos.ne']
  have hbeta_le_mass : β ≤ mass := by
    have hK_ge_one : 1 ≤ K := by
      dsimp [K]
      exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card Coordinate))
    have hinv_le_one : K⁻¹ ≤ 1 := (inv_le_one₀ hK_pos).mpr hK_ge_one
    have hmass_eq : mass = 1 - (1 - β) * K⁻¹ := by
      dsimp [mass, K]
      rw [vovkUniformUnitExpertMixMass_eq_one_sub]
    rw [hmass_eq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hβ_le_one) (sub_nonneg.mpr hinv_le_one)]
  rw [hthreshold]
  apply (div_le_iff₀ (mul_pos hK_pos hmass_pos)).mpr
  calc
    β ≤ mass := hbeta_le_mass
    _ = K⁻¹ * (K * mass) := by
      field_simp [hK_pos.ne']

/-- The uniform iid pure expert incurs mean unit-coordinate loss `1 / K`. -/
theorem pmfExp_uniform_unitCoordinateLoss
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    (outcome : Coordinate) :
    pmfExp (uniformPMF Coordinate)
        (fun expert => unitCoordinateLoss expert outcome) =
      (Fintype.card Coordinate : ℝ)⁻¹ := by
  classical
  unfold pmfExp
  simp only [uniformPMF_apply_toReal]
  rw [show (fun expert : Coordinate =>
      (Fintype.card Coordinate : ℝ)⁻¹ * unitCoordinateLoss expert outcome) =
      fun expert => if expert = outcome then (Fintype.card Coordinate : ℝ)⁻¹ else 0 by
        funext expert
        simp [unitCoordinateLoss]]
  simp

/-- A nontrivial finite coordinate type has an alternative to every outcome. -/
theorem exists_coordinate_ne
    {Coordinate : Type*} [Nontrivial Coordinate] (outcome : Coordinate) :
    ∃ other : Coordinate, other ≠ outcome := by
  obtain ⟨first, second, hfirst_ne_second⟩ := exists_pair_ne Coordinate
  by_cases hfirst : first = outcome
  · refine ⟨second, ?_⟩
    intro hsecond
    apply hfirst_ne_second
    calc
      first = outcome := hfirst
      _ = second := hsecond.symm
  · exact ⟨first, hfirst⟩

/-- The mean of the centered pure-expert loss is `1 / K - z`. -/
theorem pmfExp_uniform_unitCoordinateLoss_sub
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    (outcome : Coordinate) (z : ℝ) :
    pmfExp (uniformPMF Coordinate)
        (fun expert => unitCoordinateLoss expert outcome - z) =
      (Fintype.card Coordinate : ℝ)⁻¹ - z := by
  rw [pmfExp_sub, pmfExp_uniform_unitCoordinateLoss, pmfExp_const]

/-- A threshold at most the uniform loss mean makes the centered score mean nonnegative. -/
theorem pmfExp_uniform_unitCoordinateLoss_sub_nonneg
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    {z : ℝ} (hz : z ≤ (Fintype.card Coordinate : ℝ)⁻¹) (outcome : Coordinate) :
    0 ≤ pmfExp (uniformPMF Coordinate)
      (fun expert => unitCoordinateLoss expert outcome - z) := by
  rw [pmfExp_uniform_unitCoordinateLoss_sub]
  exact sub_nonneg.mpr hz

/--
At an interior threshold `z`, the centered uniform pure-expert loss has
positive-mass atoms on both sides of zero.  This supplies the elementary
hypotheses for the finite iid Cramer certificate used in Vovk's Section 6.
-/
theorem uniform_unitCoordinateLoss_sub_pos_neg_atoms
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    {z : ℝ} (hz_pos : 0 < z) (hz_lt_one : z < 1) (outcome : Coordinate) :
    ∃ positive negative : Coordinate,
      0 < (uniformPMF Coordinate positive).toReal ∧
        0 < unitCoordinateLoss positive outcome - z ∧
        0 < (uniformPMF Coordinate negative).toReal ∧
          unitCoordinateLoss negative outcome - z < 0 := by
  obtain ⟨other, hother_ne_outcome⟩ := exists_coordinate_ne outcome
  refine ⟨outcome, other, uniformPMF_apply_toReal_pos outcome, ?_,
    uniformPMF_apply_toReal_pos other, ?_⟩
  · simp [unitCoordinateLoss, hz_lt_one]
  · simp [unitCoordinateLoss, hother_ne_outcome, hz_pos]

/--
The finite-alphabet Cramer certificate for Vovk's interior uniform
unit-coordinate score.  Its lower side is the entropy-aware empirical-type
construction: it approximates the stationary exponential tilt by tail-safe
types and retains their full multinomial mass.
-/
theorem finiteIidScoreCramerCertificate_uniform_unitCoordinateLoss_sub
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1) (outcome : Coordinate) :
    Probability.FiniteIidScoreCramerCertificate
      (uniformPMF Coordinate)
      (fun expert => unitCoordinateLoss expert outcome -
        unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β) := by
  have hthreshold_range :=
    unitCoordinateVovkCramerThreshold_pos_lt_one
      (Coordinate := Coordinate) hβ_pos hβ_lt_one
  obtain ⟨positive, negative, hpositive_mass, hpositive_score,
    hnegative_mass, hnegative_score⟩ :=
    uniform_unitCoordinateLoss_sub_pos_neg_atoms
      hthreshold_range.1 hthreshold_range.2 outcome
  exact
    Probability.finiteIidScoreCramerCertificate_of_stationary_tilted_empiricalTypes_of_pos_neg_atoms
      (uniformPMF Coordinate)
      (fun expert => unitCoordinateLoss expert outcome -
        unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β)
      (pmfExp_uniform_unitCoordinateLoss_sub_nonneg
        (unitCoordinateVovkCramerThreshold_le_uniformMean hβ_pos hβ_lt_one.le)
        outcome)
      hpositive_mass hpositive_score hnegative_mass hnegative_score
      (by
        simpa using
          (uniform_unitCoordinateLoss_sub_weightedExp_log_eq_zero
            (Coordinate := Coordinate) hβ_pos outcome))

/--
Vovk's finite iid lower-tail exponent for the interior uniform unit-expert
score, in the source's explicit `log β` form.
-/
theorem finiteIidScoreLeftTail_uniform_unitCoordinateLoss_sub_exponentialRate
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    {β : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1) (outcome : Coordinate) :
    Probability.ExponentialRateCertificate
      (fun horizon : ℕ =>
        Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
          (fun expert => unitCoordinateLoss expert outcome -
            unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β)
          0 horizon)
      (Real.log β * unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β -
        Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)) := by
  have hcertificate :=
    Probability.FiniteIidScoreCramerCertificate.exponentialRateCertificate
      (finiteIidScoreCramerCertificate_uniform_unitCoordinateLoss_sub
        (Coordinate := Coordinate) hβ_pos hβ_lt_one outcome)
  rw [finiteChernoffRate_uniform_unitCoordinateLoss_sub hβ_pos outcome] at hcertificate
  exact hcertificate

/--
For at least two coordinates, an iid uniform pure expert has a positive
probability of zero cumulative loss against any fixed outcome coordinate at
every finite horizon.  This is the elementary positivity base of the Section-6
expert-tail argument; its sharp exponential rate is handled separately.
-/
theorem finiteIidScoreLeftTailProb_uniform_unitCoordinateLoss_pos
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    (outcome : Coordinate) (horizon : ℕ) :
    0 < Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
      (fun expert => unitCoordinateLoss expert outcome) 0 horizon := by
  classical
  obtain ⟨other, hother_ne_outcome⟩ := exists_coordinate_ne outcome
  have hevent_pos :
      0 < pmfProb (uniformPMF Coordinate)
        (fun expert => unitCoordinateLoss expert outcome = 0) := by
    refine pmfProb_pos_of_mass (uniformPMF Coordinate)
      (fun expert => unitCoordinateLoss expert outcome = 0) other ?_ ?_
    · simp [unitCoordinateLoss, hother_ne_outcome]
    · exact uniformPMF_apply_toReal_pos other
  have hforce :
      ∀ {n : ℕ} (sample : Fin n → Coordinate),
        (∀ i : Fin n, unitCoordinateLoss (sample i) outcome = 0) →
          Probability.finiteIidScoreSum (fun expert => unitCoordinateLoss expert outcome)
            sample ≤ 0 := by
    intro n sample hsample
    simp only [Probability.finiteIidScoreSum]
    have hsum_zero :
        (∑ i : Fin n, unitCoordinateLoss (sample i) outcome) = 0 := by
      calc
        (∑ i : Fin n, unitCoordinateLoss (sample i) outcome) =
            ∑ _i : Fin n, (0 : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              exact hsample i
        _ = 0 := by simp
    exact le_of_eq hsum_zero
  exact Probability.finiteIidScoreLeftTailProb_pos_of_event
    (uniformPMF Coordinate) (fun expert => unitCoordinateLoss expert outcome)
    hevent_pos hforce horizon

/-- The zero-loss atom of a uniform unit-coordinate expert has mass `1 - 1/K`. -/
theorem pmfProb_uniform_unitCoordinateLoss_eq_zero
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    (outcome : Coordinate) :
    pmfProb (uniformPMF Coordinate)
      (fun expert => unitCoordinateLoss expert outcome = 0) =
        1 - (Fintype.card Coordinate : ℝ)⁻¹ := by
  calc
    pmfProb (uniformPMF Coordinate)
        (fun expert => unitCoordinateLoss expert outcome = 0) =
      pmfProb (uniformPMF Coordinate) (fun expert => ¬ expert = outcome) := by
        apply pmfProb_congr
        intro expert
        simp [unitCoordinateLoss]
    _ = 1 - pmfProb (uniformPMF Coordinate) (fun expert => expert = outcome) :=
      pmfProb_compl (uniformPMF Coordinate) (fun expert => expert = outcome)
    _ = 1 - (uniformPMF Coordinate outcome).toReal := by
      rw [pmfProb_singleton]
    _ = 1 - (Fintype.card Coordinate : ℝ)⁻¹ := by
      simp only [uniformPMF_apply_toReal]

/--
At the zero-threshold boundary, the uniform unit-coordinate iid tail has its
exact elementary exponential rate.  This is the trivial-outcome branch of the
Section-6 Cramer analysis, stated as a reusable certificate rather than an
asymptotic shortcut.
-/
theorem finiteIidScoreLeftTail_uniform_unitCoordinateLoss_rate_zero
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    (outcome : Coordinate) :
    Probability.ExponentialRateCertificate
      (fun horizon : ℕ =>
        Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
          (fun expert => unitCoordinateLoss expert outcome) 0 horizon)
      (-Real.log (1 - (Fintype.card Coordinate : ℝ)⁻¹)) := by
  have hsupport : ∀ expert : Coordinate,
      0 < (uniformPMF Coordinate expert).toReal →
        0 ≤ unitCoordinateLoss expert outcome := by
    intro expert _hmass
    simp only [unitCoordinateLoss]
    split_ifs <;> norm_num
  have hzero := pmfProb_uniform_unitCoordinateLoss_eq_zero outcome
  have hzero_pos :
      0 < pmfProb (uniformPMF Coordinate)
        (fun expert => unitCoordinateLoss expert outcome = 0) := by
    obtain ⟨other, hother_ne_outcome⟩ := exists_coordinate_ne outcome
    refine pmfProb_pos_of_mass (uniformPMF Coordinate)
      (fun expert => unitCoordinateLoss expert outcome = 0) other ?_ ?_
    · simp [unitCoordinateLoss, hother_ne_outcome]
    · exact uniformPMF_apply_toReal_pos other
  exact Probability.finiteIidScoreLeftTail_exponentialRateCertificate_of_support_nonneg_zero_prob
    (uniformPMF Coordinate) (fun expert => unitCoordinateLoss expert outcome)
    hsupport hzero (by simpa [hzero] using hzero_pos)

/-- The cumulative loss of one pure expert against a fixed finite outcome path. -/
noncomputable def unitCoordinatePureExpertCumulativeLoss
    {Coordinate : Type*} {horizon : ℕ}
    (outcomes prediction : Fin horizon → Coordinate) : ℝ :=
  ∑ time : Fin horizon, unitCoordinateLoss (prediction time) (outcomes time)

/--
Coordinatewise swaps rebase a fixed outcome path to one constant coordinate.
They are a permutation of the finite pure-prediction sample space.
-/
noncomputable def unitCoordinateRebasePredictionEquiv
    {Coordinate : Type*} [DecidableEq Coordinate] {horizon : ℕ}
    (outcomes : Fin horizon → Coordinate) (base : Coordinate) :
    (Fin horizon → Coordinate) ≃ (Fin horizon → Coordinate) :=
  Equiv.piCongrRight (fun time => Equiv.swap (outcomes time) base)

/-- Swapping an outcome to a base coordinate preserves unit-coordinate loss. -/
theorem unitCoordinateLoss_rebase
    {Coordinate : Type*} [DecidableEq Coordinate]
    (prediction outcome base : Coordinate) :
    unitCoordinateLoss (Equiv.swap outcome base prediction) base =
      unitCoordinateLoss prediction outcome := by
  simp [unitCoordinateLoss, Equiv.swap_apply_eq_iff]

/-- Rebasing a prediction path preserves its cumulative pure-expert loss. -/
theorem unitCoordinatePureExpertCumulativeLoss_rebase
    {Coordinate : Type*} [DecidableEq Coordinate] {horizon : ℕ}
    (outcomes : Fin horizon → Coordinate) (base : Coordinate)
    (prediction : Fin horizon → Coordinate) :
    unitCoordinatePureExpertCumulativeLoss (fun _time => base)
        (unitCoordinateRebasePredictionEquiv outcomes base prediction) =
      unitCoordinatePureExpertCumulativeLoss outcomes prediction := by
  unfold unitCoordinatePureExpertCumulativeLoss
  refine Finset.sum_congr rfl ?_
  intro time _htime
  exact unitCoordinateLoss_rebase (prediction time) (outcomes time) base

/--
Under the uniform pure-prediction law, the cumulative-loss tail probability is
invariant under an arbitrary fixed outcome path.  This is the finite
path-relabeling bridge from Vovk's adaptive game to a fixed-outcome iid score.
-/
theorem pmfProb_uniform_unitCoordinatePureExpertCumulativeLoss_eq_constant
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    [Nonempty Coordinate] {horizon : ℕ}
    (outcomes : Fin horizon → Coordinate) (base : Coordinate) (threshold : ℝ) :
    pmfProb (uniformPMF (Fin horizon → Coordinate))
        (fun prediction =>
          unitCoordinatePureExpertCumulativeLoss outcomes prediction ≤ threshold) =
        pmfProb (uniformPMF (Fin horizon → Coordinate))
          (fun prediction =>
            unitCoordinatePureExpertCumulativeLoss (fun _time => base) prediction ≤
              threshold) := by
  classical
  symm
  apply pmfProb_uniformPMF_eq_of_comp_equiv
    (unitCoordinateRebasePredictionEquiv outcomes base)
  intro prediction
  rw [unitCoordinatePureExpertCumulativeLoss_rebase]

/--
The uniform pure-expert cumulative-loss tail against any fixed outcome path is
exactly the finite iid tail for the one-coordinate loss law at a base outcome.
-/
theorem pmfProb_uniform_unitCoordinatePureExpertCumulativeLoss_eq_finiteIid
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    [Nonempty Coordinate] {horizon : ℕ}
    (outcomes : Fin horizon → Coordinate) (base : Coordinate) (threshold : ℝ) :
    pmfProb (uniformPMF (Fin horizon → Coordinate))
        (fun prediction =>
          unitCoordinatePureExpertCumulativeLoss outcomes prediction ≤ threshold) =
      Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
        (fun expert => unitCoordinateLoss expert base) threshold horizon := by
  calc
    pmfProb (uniformPMF (Fin horizon → Coordinate))
        (fun prediction =>
          unitCoordinatePureExpertCumulativeLoss outcomes prediction ≤ threshold) =
        pmfProb (uniformPMF (Fin horizon → Coordinate))
          (fun prediction =>
            unitCoordinatePureExpertCumulativeLoss (fun _time => base) prediction ≤
              threshold) :=
          pmfProb_uniform_unitCoordinatePureExpertCumulativeLoss_eq_constant
            outcomes base threshold
    _ = pmfProb (pmfProduct (Fin horizon) Coordinate (uniformPMF Coordinate))
          (fun prediction =>
            unitCoordinatePureExpertCumulativeLoss (fun _time => base) prediction ≤
              threshold) := by
          rw [pmfProduct_uniformPMF_eq_uniformPMF_fun]
    _ = Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
          (fun expert => unitCoordinateLoss expert base) threshold horizon := by
          rfl

/-- The centered pure-expert loss sum used by Vovk's Cramer argument. -/
noncomputable def unitCoordinatePureExpertCenteredCumulativeLoss
    {Coordinate : Type*} {horizon : ℕ}
    (outcomes prediction : Fin horizon → Coordinate) (z : ℝ) : ℝ :=
  ∑ time : Fin horizon, (unitCoordinateLoss (prediction time) (outcomes time) - z)

/-- Centering subtracts `horizon * z` from the raw cumulative loss. -/
theorem unitCoordinatePureExpertCenteredCumulativeLoss_eq
    {Coordinate : Type*} {horizon : ℕ}
    (outcomes prediction : Fin horizon → Coordinate) (z : ℝ) :
    unitCoordinatePureExpertCenteredCumulativeLoss outcomes prediction z =
      unitCoordinatePureExpertCumulativeLoss outcomes prediction - (horizon : ℝ) * z := by
  unfold unitCoordinatePureExpertCenteredCumulativeLoss unitCoordinatePureExpertCumulativeLoss
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  simp [nsmul_eq_mul]

/--
The centered cumulative-loss tail against any fixed outcome path is exactly the
finite iid centered-score tail at a base outcome.  This is the direct input
shape of the finite Cramer certificate.
-/
theorem pmfProb_uniform_unitCoordinateCenteredCumulativeLoss_eq_finiteIid
    {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]
    [Nonempty Coordinate] {horizon : ℕ}
    (outcomes : Fin horizon → Coordinate) (base : Coordinate) (z : ℝ) :
    pmfProb (uniformPMF (Fin horizon → Coordinate))
        (fun prediction =>
          unitCoordinatePureExpertCenteredCumulativeLoss outcomes prediction z ≤ 0) =
      Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
        (fun expert => unitCoordinateLoss expert base - z) 0 horizon := by
  calc
    pmfProb (uniformPMF (Fin horizon → Coordinate))
        (fun prediction =>
          unitCoordinatePureExpertCenteredCumulativeLoss outcomes prediction z ≤ 0) =
        pmfProb (uniformPMF (Fin horizon → Coordinate))
          (fun prediction =>
            unitCoordinatePureExpertCumulativeLoss outcomes prediction ≤
              (horizon : ℝ) * z) := by
          apply pmfProb_congr
          intro prediction
          rw [unitCoordinatePureExpertCenteredCumulativeLoss_eq]
          constructor <;> intro htail <;> linarith
    _ = Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
          (fun expert => unitCoordinateLoss expert base) ((horizon : ℝ) * z) horizon :=
          pmfProb_uniform_unitCoordinatePureExpertCumulativeLoss_eq_finiteIid
            outcomes base ((horizon : ℝ) * z)
    _ = Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
          (fun expert => unitCoordinateLoss expert base - z) 0 horizon := by
          unfold Probability.finiteIidScoreLeftTailProb
          apply pmfProb_congr
          intro prediction
          unfold Probability.finiteIidScoreSum
          rw [Finset.sum_sub_distrib, Finset.sum_const]
          simp [nsmul_eq_mul]

/--
For independent uniform pure experts, the probability that every expert misses
the fixed-path centered-loss target is the product of their identical failure
probabilities.  This is Vovk's independent-experts step before the adaptive
stopping argument selects a suitable outcome path.
-/
theorem pmfProduct_uniform_noCenteredGoodExpert_prob
    {Expert Coordinate : Type*} [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    {horizon : ℕ} (outcomes : Fin horizon → Coordinate) (base : Coordinate) (z : ℝ) :
    pmfProb
        (pmfProduct Expert (Fin horizon → Coordinate)
          (uniformPMF (Fin horizon → Coordinate)))
        (fun expertPredictions =>
          ∀ expert,
            ¬ unitCoordinatePureExpertCenteredCumulativeLoss outcomes
                (expertPredictions expert) z ≤ 0) =
      (1 - Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
        (fun expert => unitCoordinateLoss expert base - z) 0 horizon) ^
        Fintype.card Expert := by
  classical
  let good : (Fin horizon → Coordinate) → Prop :=
    fun prediction =>
      unitCoordinatePureExpertCenteredCumulativeLoss outcomes prediction z ≤ 0
  change pmfProb
      (pmfProduct Expert (Fin horizon → Coordinate)
        (uniformPMF (Fin horizon → Coordinate)))
      (fun expertPredictions => ∀ expert, ¬good (expertPredictions expert)) = _
  have hgood :
      pmfProb (uniformPMF (Fin horizon → Coordinate)) good =
        Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
          (fun expert => unitCoordinateLoss expert base - z) 0 horizon := by
    simpa [good] using
      (pmfProb_uniform_unitCoordinateCenteredCumulativeLoss_eq_finiteIid
        outcomes base z)
  calc
    pmfProb
        (pmfProduct Expert (Fin horizon → Coordinate)
          (uniformPMF (Fin horizon → Coordinate)))
        (fun expertPredictions => ∀ expert, ¬good (expertPredictions expert)) =
      (pmfProb (uniformPMF (Fin horizon → Coordinate))
        (fun prediction => ¬good prediction)) ^ Fintype.card Expert := by
          exact pmfProduct_prob_forall
            (uniformPMF (Fin horizon → Coordinate))
            (fun prediction => ¬good prediction)
    _ = (1 - Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
        (fun expert => unitCoordinateLoss expert base - z) 0 horizon) ^
          Fintype.card Expert := by
      rw [pmfProb_compl (uniformPMF (Fin horizon → Coordinate)) good, hgood]

/--
Every finite-valued random construction has an output path whose probability
is at least the reciprocal of the number of possible outputs.  This is the
finite pigeonhole step used when Vovk selects a suitable outcome path.
-/
theorem exists_pmfProb_preimage_ge_inv_card
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output] [Nonempty Output]
    (μ : PMF Input) (output : Input → Output) :
    ∃ selected : Output,
      (Fintype.card Output : ℝ)⁻¹ ≤
        pmfProb μ (fun input => output input = selected) := by
  classical
  let mass : Output → ℝ := fun selected => ((μ.map output) selected).toReal
  have hmass : FiniteProbabilitySimplex mass := by
    constructor
    · intro selected
      exact ENNReal.toReal_nonneg
    · simpa [mass] using pmfToRealSum (μ.map output)
  obtain ⟨selected, hselected⟩ := exists_finiteMax_eq mass
  refine ⟨selected, ?_⟩
  calc
    (Fintype.card Output : ℝ)⁻¹ ≤ finiteMax mass :=
      finiteProbabilitySimplex_inv_card_le_finiteMax mass hmass
    _ = mass selected := hselected
    _ = pmfProb μ (fun input => output input = selected) := by
      exact pmf_map_apply_toReal_eq_pmfProb_preimage μ output selected

/--
The outcome chosen by Vovk's Section-6 environment for the unit-coordinate
game: a coordinate at which the learner's simplex decision is maximal.
Unlike the failed-one-step selector below, this is the source strategy used in
the probabilistic/Cramer part of the necessary-direction proof.
-/
noncomputable def maxUnitCoordinateOutcomeSelector
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    (learnerMass : Coordinate → ℝ) : Coordinate :=
  Classical.choose (exists_finiteMax_eq learnerMass)

/-- The max-coordinate selector attains the finite maximum. -/
theorem maxUnitCoordinateOutcomeSelector_spec
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    (learnerMass : Coordinate → ℝ) :
    learnerMass (maxUnitCoordinateOutcomeSelector learnerMass) = finiteMax learnerMass := by
  exact (Classical.choose_spec (exists_finiteMax_eq learnerMass)).symm

/-- A pure coordinate decision makes that coordinate the unique max-selector outcome. -/
theorem maxUnitCoordinateOutcomeSelector_pureDecision
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    [Nontrivial Coordinate] (coordinate : Coordinate) :
    maxUnitCoordinateOutcomeSelector (unitCoordinatePureDecision coordinate) = coordinate := by
  have hmax : finiteMax (unitCoordinatePureDecision coordinate) = 1 := by
    apply le_antisymm
    · obtain ⟨candidate, hcandidate⟩ :=
        exists_finiteMax_eq (unitCoordinatePureDecision coordinate)
      rw [hcandidate]
      simp [unitCoordinatePureDecision, unitCoordinateLoss]
      split_ifs <;> norm_num
    · calc
        (1 : ℝ) = unitCoordinatePureDecision coordinate coordinate := by
          simp [unitCoordinatePureDecision, unitCoordinateLoss]
        _ ≤ finiteMax (unitCoordinatePureDecision coordinate) :=
          le_finiteMax _ coordinate
  by_contra hselector_ne
  have hcoordinate_ne_selector :
      coordinate ≠ maxUnitCoordinateOutcomeSelector (unitCoordinatePureDecision coordinate) := by
    intro h
    exact hselector_ne h.symm
  have hselector_zero :
      unitCoordinatePureDecision coordinate
          (maxUnitCoordinateOutcomeSelector (unitCoordinatePureDecision coordinate)) = 0 := by
    simp [unitCoordinatePureDecision, unitCoordinateLoss, hcoordinate_ne_selector]
  have hselector_max :=
    maxUnitCoordinateOutcomeSelector_spec (unitCoordinatePureDecision coordinate)
  rw [hselector_max, hmax] at hselector_zero
  norm_num at hselector_zero

/-- A finite game history agrees with a prescribed infinite outcome path. -/
def unitCoordinateHistoryAgrees
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (target : ℕ → Coordinate) (history : List (UnitCoordinateDecisionRound Expert Coordinate)) : Prop :=
  history.map UnitCoordinateDecisionRound.outcome =
    (List.range history.length).map target

/-- Agreement is preserved precisely by appending the prescribed next outcome. -/
theorem unitCoordinateHistoryAgrees_append_singleton
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (target : ℕ → Coordinate) (history : List (UnitCoordinateDecisionRound Expert Coordinate))
    (round : UnitCoordinateDecisionRound Expert Coordinate) :
    unitCoordinateHistoryAgrees target (history ++ [round]) ↔
      unitCoordinateHistoryAgrees target history ∧ round.outcome = target history.length := by
  constructor
  · intro hagrees
    constructor
    · have hdrop := congrArg List.dropLast hagrees
      simpa [unitCoordinateHistoryAgrees, List.range_succ] using hdrop
    · have hlast := congrArg List.getLast? hagrees
      simpa [unitCoordinateHistoryAgrees, List.range_succ] using hlast
  · rintro ⟨hhistory, hround⟩
    unfold unitCoordinateHistoryAgrees at hhistory ⊢
    simp [List.range_succ, hhistory, hround]

/-- Agreement of a history extended by future rounds implies agreement of its prefix. -/
theorem unitCoordinateHistoryAgrees_prefix
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (target : ℕ → Coordinate) (history remaining : List (UnitCoordinateDecisionRound Expert Coordinate))
    (hagrees : unitCoordinateHistoryAgrees target (history ++ remaining)) :
    unitCoordinateHistoryAgrees target history := by
  unfold unitCoordinateHistoryAgrees at hagrees ⊢
  have htake := congrArg (fun entries : List Coordinate => entries.take history.length) hagrees
  dsimp at htake
  rw [← List.map_take, ← List.map_take] at htake
  have hlength : history.length ≤ history.length + remaining.length := Nat.le_add_right _ _
  simpa [List.map_append, List.take_append, List.take_range,
    Nat.min_eq_left hlength] using htake

/-- Agreement of a nonempty continuation identifies its next prescribed outcome. -/
theorem unitCoordinateHistoryAgrees_next_outcome
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (target : ℕ → Coordinate) (history : List (UnitCoordinateDecisionRound Expert Coordinate))
    (round : UnitCoordinateDecisionRound Expert Coordinate)
    (remaining : List (UnitCoordinateDecisionRound Expert Coordinate))
    (hagrees : unitCoordinateHistoryAgrees target (history ++ round :: remaining)) :
    round.outcome = target history.length := by
  have hpref : unitCoordinateHistoryAgrees target (history ++ [round]) := by
    simpa [List.append_assoc] using
      (unitCoordinateHistoryAgrees_prefix target (history ++ [round]) remaining
        (by simpa [List.append_assoc] using hagrees))
  exact (unitCoordinateHistoryAgrees_append_singleton target history round).1 hpref |>.2

/--
The agreement modification from Vovk's Section 6.  Until the original policy
would select the prescribed next outcome, it is followed unchanged; otherwise
the policy switches to the corresponding pure decision.  The modification
therefore forces the max-coordinate environment to follow `target`.
-/
noncomputable def unitCoordinateAgreementModification
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate) (target : ℕ → Coordinate) :
    UnitCoordinateDecisionPolicy Expert Coordinate := by
  classical
  exact fun history expertDecision =>
    if h : unitCoordinateHistoryAgrees target history ∧
        maxUnitCoordinateOutcomeSelector (policy history expertDecision) = target history.length
    then policy history expertDecision
    else unitCoordinatePureDecision (target history.length)

/-- The agreement modification remains an admissible simplex decision policy. -/
theorem unitCoordinateAgreementModification_admissible
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (hpolicy : UnitCoordinateDecisionPolicyAdmissible policy) (target : ℕ → Coordinate) :
    UnitCoordinateDecisionPolicyAdmissible
      (unitCoordinateAgreementModification policy target) := by
  classical
  intro history expertDecision hexpertDecision
  unfold unitCoordinateAgreementModification
  split_ifs with hagrees
  · exact hpolicy history expertDecision hexpertDecision
  · exact unitCoordinatePureDecision_mem _

/-- The max-coordinate environment follows the prescribed path after modification. -/
theorem maxUnitCoordinateOutcomeSelector_agreementModification
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate) (target : ℕ → Coordinate)
    (history : List (UnitCoordinateDecisionRound Expert Coordinate))
    (expertDecision : Expert → Coordinate → ℝ) :
    maxUnitCoordinateOutcomeSelector
      (unitCoordinateAgreementModification policy target history expertDecision) =
        target history.length := by
  classical
  unfold unitCoordinateAgreementModification
  split_ifs with hagrees
  · exact hagrees.2
  · exact maxUnitCoordinateOutcomeSelector_pureDecision _

/--
Every finite simplex incurs at least uniform-coordinate loss against Vovk's
max-coordinate outcome selector.  This is the literal `R` lower floor in
Section 6 for the unit-coordinate specialization.
-/
theorem unitCoordinateDecisionLoss_le_maxUnitCoordinateOutcomeSelector
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    (learnerMass : Coordinate → ℝ) (hlearnerMass : FiniteProbabilitySimplex learnerMass) :
    (Fintype.card Coordinate : ℝ)⁻¹ ≤
      unitCoordinateDecisionLoss learnerMass
        (maxUnitCoordinateOutcomeSelector learnerMass) := by
  change (Fintype.card Coordinate : ℝ)⁻¹ ≤
    learnerMass (maxUnitCoordinateOutcomeSelector learnerMass)
  rw [maxUnitCoordinateOutcomeSelector_spec learnerMass]
  exact finiteProbabilitySimplex_inv_card_le_finiteMax learnerMass hlearnerMass

/--
Run a unit-coordinate policy for a fixed number of rounds against a pure-expert
table and an outcome selector.  The selector is applied after the policy has
observed the current row of expert decisions, exactly as in Vovk's global game.
-/
noncomputable def unitCoordinateVovkRoundsFrom
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) :
    ℕ → List (UnitCoordinateDecisionRound Expert Coordinate) →
      List (UnitCoordinateDecisionRound Expert Coordinate)
  | 0, _history => []
  | time + 1, history =>
      let expertDecision := unitCoordinatePureExpertDecisions table history.length
      let learnerDecision := policy history expertDecision
      let outcome := outcomeSelector learnerDecision
      let round : UnitCoordinateDecisionRound Expert Coordinate :=
        { expertDecision := expertDecision
          expertDecision_mem := unitCoordinatePureExpertDecisions_mem table history.length
          outcome := outcome }
      round :: unitCoordinateVovkRoundsFrom policy outcomeSelector table time (history ++ [round])

/-- The Vovk game tree started from the empty game history. -/
noncomputable def unitCoordinateVovkRounds
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (horizon : ℕ) :
    List (UnitCoordinateDecisionRound Expert Coordinate) :=
  unitCoordinateVovkRoundsFrom policy outcomeSelector table horizon []

/-- The recursive game-tree construction has exactly its requested horizon. -/
theorem unitCoordinateVovkRoundsFrom_length
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) :
    ∀ (horizon : ℕ) (history : List (UnitCoordinateDecisionRound Expert Coordinate)),
      (unitCoordinateVovkRoundsFrom policy outcomeSelector table horizon history).length =
        horizon := by
  intro horizon
  induction horizon with
  | zero => intro history; rfl
  | succ horizon ih =>
      intro history
      simp only [unitCoordinateVovkRoundsFrom, List.length_cons]
      rw [ih]

/-- The empty-history game tree has exactly its requested horizon. -/
theorem unitCoordinateVovkRounds_length
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (horizon : ℕ) :
    (unitCoordinateVovkRounds policy outcomeSelector table horizon).length = horizon := by
  exact unitCoordinateVovkRoundsFrom_length policy outcomeSelector table horizon []

/--
Against the max-coordinate environment, the agreement modification makes every
finite game continuation follow its prescribed outcome path.
-/
theorem unitCoordinateAgreementModification_roundsFrom_agree
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate) (target : ℕ → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) :
    ∀ (horizon : ℕ) (history : List (UnitCoordinateDecisionRound Expert Coordinate)),
      unitCoordinateHistoryAgrees target history →
        unitCoordinateHistoryAgrees target
          (history ++ unitCoordinateVovkRoundsFrom
            (unitCoordinateAgreementModification policy target)
            maxUnitCoordinateOutcomeSelector table horizon history) := by
  intro horizon
  induction horizon with
  | zero =>
      intro history hagrees
      simpa [unitCoordinateVovkRoundsFrom] using hagrees
  | succ horizon ih =>
      intro history hagrees
      let expertDecision := unitCoordinatePureExpertDecisions table history.length
      let learnerDecision :=
        unitCoordinateAgreementModification policy target history expertDecision
      let outcome := maxUnitCoordinateOutcomeSelector learnerDecision
      let round : UnitCoordinateDecisionRound Expert Coordinate :=
        { expertDecision := expertDecision
          expertDecision_mem := unitCoordinatePureExpertDecisions_mem table history.length
          outcome := outcome }
      have houtcome : round.outcome = target history.length := by
        dsimp [round, outcome, learnerDecision]
        exact maxUnitCoordinateOutcomeSelector_agreementModification
          policy target history expertDecision
      have happend : unitCoordinateHistoryAgrees target (history ++ [round]) :=
        (unitCoordinateHistoryAgrees_append_singleton target history round).2
          ⟨hagrees, houtcome⟩
      have htail := ih (history ++ [round]) happend
      simpa [unitCoordinateVovkRoundsFrom, expertDecision, learnerDecision, outcome,
        round, List.append_assoc] using htail

/-- The empty-history agreement-modified game has the prescribed finite path. -/
theorem unitCoordinateAgreementModification_rounds_agree
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate) (target : ℕ → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (horizon : ℕ) :
    unitCoordinateHistoryAgrees target
      (unitCoordinateVovkRounds
        (unitCoordinateAgreementModification policy target)
        maxUnitCoordinateOutcomeSelector table horizon) := by
  have hempty : unitCoordinateHistoryAgrees target
      ([] : List (UnitCoordinateDecisionRound Expert Coordinate)) := by
    simp [unitCoordinateHistoryAgrees]
  simpa [unitCoordinateVovkRounds] using
    (unitCoordinateAgreementModification_roundsFrom_agree
      policy target table horizon [] hempty)

/--
On a realization where the original max-coordinate game already follows the
prescribed path, the agreement modification leaves the whole finite game tree
unchanged.  This is the coupling assertion behind Vovk's suitable-path step.
-/
theorem unitCoordinateAgreementModification_roundsFrom_eq_of_agrees
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate) (target : ℕ → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) :
    ∀ (horizon : ℕ) (history : List (UnitCoordinateDecisionRound Expert Coordinate)),
      unitCoordinateHistoryAgrees target
        (history ++ unitCoordinateVovkRoundsFrom
          policy maxUnitCoordinateOutcomeSelector table horizon history) →
        unitCoordinateVovkRoundsFrom
          (unitCoordinateAgreementModification policy target)
          maxUnitCoordinateOutcomeSelector table horizon history =
        unitCoordinateVovkRoundsFrom
          policy maxUnitCoordinateOutcomeSelector table horizon history := by
  intro horizon
  induction horizon with
  | zero =>
      intro history _hagrees
      rfl
  | succ horizon ih =>
      intro history hagrees
      let expertDecision := unitCoordinatePureExpertDecisions table history.length
      let learnerDecision := policy history expertDecision
      let outcome := maxUnitCoordinateOutcomeSelector learnerDecision
      let round : UnitCoordinateDecisionRound Expert Coordinate :=
        { expertDecision := expertDecision
          expertDecision_mem := unitCoordinatePureExpertDecisions_mem table history.length
          outcome := outcome }
      have hagrees' : unitCoordinateHistoryAgrees target
          (history ++ round :: unitCoordinateVovkRoundsFrom
            policy maxUnitCoordinateOutcomeSelector table horizon (history ++ [round])) := by
        simpa [unitCoordinateVovkRoundsFrom, expertDecision, learnerDecision, outcome, round] using
          hagrees
      have hprefix : unitCoordinateHistoryAgrees target history :=
        unitCoordinateHistoryAgrees_prefix target history
          (round :: unitCoordinateVovkRoundsFrom
            policy maxUnitCoordinateOutcomeSelector table horizon (history ++ [round])) hagrees'
      have houtcome : outcome = target history.length := by
        exact unitCoordinateHistoryAgrees_next_outcome target history round
          (unitCoordinateVovkRoundsFrom
            policy maxUnitCoordinateOutcomeSelector table horizon (history ++ [round])) hagrees'
      have hmodified :
          unitCoordinateAgreementModification policy target history expertDecision = learnerDecision := by
        unfold unitCoordinateAgreementModification
        rw [dif_pos ⟨hprefix, by simpa [outcome, learnerDecision] using houtcome⟩]
      have htail_agrees : unitCoordinateHistoryAgrees target
          ((history ++ [round]) ++ unitCoordinateVovkRoundsFrom
            policy maxUnitCoordinateOutcomeSelector table horizon (history ++ [round])) := by
        simpa [List.append_assoc] using hagrees'
      have htail := ih (history ++ [round]) htail_agrees
      simp only [unitCoordinateVovkRoundsFrom]
      simp [expertDecision, learnerDecision, outcome, round, hmodified, htail]

/-- The empty-history suitable-path coupling for the agreement modification. -/
theorem unitCoordinateAgreementModification_rounds_eq_of_agrees
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate) (target : ℕ → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (horizon : ℕ)
    (hagrees : unitCoordinateHistoryAgrees target
      (unitCoordinateVovkRounds policy maxUnitCoordinateOutcomeSelector table horizon)) :
    unitCoordinateVovkRounds
        (unitCoordinateAgreementModification policy target)
        maxUnitCoordinateOutcomeSelector table horizon =
      unitCoordinateVovkRounds policy maxUnitCoordinateOutcomeSelector table horizon := by
  simpa [unitCoordinateVovkRounds] using
    (unitCoordinateAgreementModification_roundsFrom_eq_of_agrees
      policy target table horizon [] (by simpa using hagrees))

/--
On the suitable-path branch, the modified policy's cumulative loss equals the
original policy's cumulative loss.  Thus the original global guarantee
transfers to that branch without assuming the modification is globally winning.
-/
theorem unitCoordinateAgreementModification_policyCumulativeLossFrom_eq_of_agrees
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate) (target : ℕ → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) :
    ∀ (horizon : ℕ) (history : List (UnitCoordinateDecisionRound Expert Coordinate)),
      unitCoordinateHistoryAgrees target
        (history ++ unitCoordinateVovkRoundsFrom
          policy maxUnitCoordinateOutcomeSelector table horizon history) →
        unitCoordinateDecisionPolicyCumulativeLossFrom
            (unitCoordinateAgreementModification policy target) history
            (unitCoordinateVovkRoundsFrom
              (unitCoordinateAgreementModification policy target)
              maxUnitCoordinateOutcomeSelector table horizon history) =
          unitCoordinateDecisionPolicyCumulativeLossFrom policy history
            (unitCoordinateVovkRoundsFrom
              policy maxUnitCoordinateOutcomeSelector table horizon history) := by
  intro horizon
  induction horizon with
  | zero =>
      intro history _hagrees
      rfl
  | succ horizon ih =>
      intro history hagrees
      let expertDecision := unitCoordinatePureExpertDecisions table history.length
      let learnerDecision := policy history expertDecision
      let outcome := maxUnitCoordinateOutcomeSelector learnerDecision
      let round : UnitCoordinateDecisionRound Expert Coordinate :=
        { expertDecision := expertDecision
          expertDecision_mem := unitCoordinatePureExpertDecisions_mem table history.length
          outcome := outcome }
      have hagrees' : unitCoordinateHistoryAgrees target
          (history ++ round :: unitCoordinateVovkRoundsFrom
            policy maxUnitCoordinateOutcomeSelector table horizon (history ++ [round])) := by
        simpa [unitCoordinateVovkRoundsFrom, expertDecision, learnerDecision, outcome, round] using
          hagrees
      have hprefix : unitCoordinateHistoryAgrees target history :=
        unitCoordinateHistoryAgrees_prefix target history
          (round :: unitCoordinateVovkRoundsFrom
            policy maxUnitCoordinateOutcomeSelector table horizon (history ++ [round])) hagrees'
      have houtcome : outcome = target history.length := by
        exact unitCoordinateHistoryAgrees_next_outcome target history round
          (unitCoordinateVovkRoundsFrom
            policy maxUnitCoordinateOutcomeSelector table horizon (history ++ [round])) hagrees'
      have hmodified :
          unitCoordinateAgreementModification policy target history expertDecision = learnerDecision := by
        unfold unitCoordinateAgreementModification
        rw [dif_pos ⟨hprefix, by simpa [outcome, learnerDecision] using houtcome⟩]
      have htail_agrees : unitCoordinateHistoryAgrees target
          ((history ++ [round]) ++ unitCoordinateVovkRoundsFrom
            policy maxUnitCoordinateOutcomeSelector table horizon (history ++ [round])) := by
        simpa [List.append_assoc] using hagrees'
      have htail := ih (history ++ [round]) htail_agrees
      simp only [unitCoordinateVovkRoundsFrom,
        unitCoordinateDecisionPolicyCumulativeLossFrom]
      simp [expertDecision, learnerDecision, outcome, round, hmodified, htail]

/-- The empty-history suitable-path coupling for cumulative learner loss. -/
theorem unitCoordinateAgreementModification_policyCumulativeLoss_eq_of_agrees
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate) (target : ℕ → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (horizon : ℕ)
    (hagrees : unitCoordinateHistoryAgrees target
      (unitCoordinateVovkRounds policy maxUnitCoordinateOutcomeSelector table horizon)) :
    unitCoordinateDecisionPolicyCumulativeLoss
        (unitCoordinateAgreementModification policy target)
        (unitCoordinateVovkRounds
          (unitCoordinateAgreementModification policy target)
          maxUnitCoordinateOutcomeSelector table horizon) =
      unitCoordinateDecisionPolicyCumulativeLoss policy
        (unitCoordinateVovkRounds policy maxUnitCoordinateOutcomeSelector table horizon) := by
  simpa [unitCoordinateDecisionPolicyCumulativeLoss, unitCoordinateVovkRounds] using
    (unitCoordinateAgreementModification_policyCumulativeLossFrom_eq_of_agrees
      policy target table horizon [] (by simpa using hagrees))

/--
Extend a finite random pure-expert table beyond its sampled horizon.  Values
after the horizon are arbitrary and cannot affect a `horizon`-round game.
-/
noncomputable def unitCoordinateExtendFiniteTable
    {Expert Coordinate : Type*} [Nonempty Coordinate] {horizon : ℕ}
    (table : Fin horizon → Expert → Coordinate) : UnitCoordinatePureExpertTable Expert Coordinate :=
  fun time expert =>
    if htime : time < horizon then table ⟨time, htime⟩ expert
    else Classical.choice (inferInstance : Nonempty Coordinate)

/-- Extend a finite outcome path arbitrarily past its horizon. -/
noncomputable def unitCoordinateExtendFiniteOutcomePath
    {Coordinate : Type*} [Nonempty Coordinate] {horizon : ℕ}
    (outcomes : Fin horizon → Coordinate) : ℕ → Coordinate :=
  fun time =>
    if htime : time < horizon then outcomes ⟨time, htime⟩
    else Classical.choice (inferInstance : Nonempty Coordinate)

/-- The finite prefix of an extended path is unchanged. -/
theorem unitCoordinateExtendFiniteOutcomePath_apply
    {Coordinate : Type*} [Nonempty Coordinate] {horizon : ℕ}
    (outcomes : Fin horizon → Coordinate) (time : Fin horizon) :
    unitCoordinateExtendFiniteOutcomePath outcomes time = outcomes time := by
  simp [unitCoordinateExtendFiniteOutcomePath, time.isLt]

/--
The outcome path generated from a finite pure-expert table by an adaptive
Vovk game tree.  It is a finite-valued random variable when the table is
sampled uniformly.
-/
noncomputable def unitCoordinateVovkFiniteTableOutcomePath
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Coordinate] {horizon : ℕ}
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate)
    (table : Fin horizon → Expert → Coordinate) : Fin horizon → Coordinate :=
  fun time =>
    ((unitCoordinateVovkRounds policy outcomeSelector
      (unitCoordinateExtendFiniteTable table) horizon).get
        (Fin.cast (unitCoordinateVovkRounds_length policy outcomeSelector
          (unitCoordinateExtendFiniteTable table) horizon).symm time)).outcome

/--
If the finite adaptive outcome random variable realizes `outcomes`, the
underlying game history agrees with the corresponding extended path.
-/
theorem unitCoordinateVovkFiniteTableOutcomePath_agrees
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Coordinate] {horizon : ℕ}
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate)
    (table : Fin horizon → Expert → Coordinate)
    (outcomes : Fin horizon → Coordinate)
    (hpath : unitCoordinateVovkFiniteTableOutcomePath policy outcomeSelector table = outcomes) :
    unitCoordinateHistoryAgrees (unitCoordinateExtendFiniteOutcomePath outcomes)
      (unitCoordinateVovkRounds policy outcomeSelector
        (unitCoordinateExtendFiniteTable table) horizon) := by
  let rounds : List (UnitCoordinateDecisionRound Expert Coordinate) :=
    unitCoordinateVovkRounds policy outcomeSelector
      (unitCoordinateExtendFiniteTable table) horizon
  have hlength : rounds.length = horizon :=
    unitCoordinateVovkRounds_length policy outcomeSelector
      (unitCoordinateExtendFiniteTable table) horizon
  unfold unitCoordinateHistoryAgrees
  apply List.ext_get
  · simp [rounds, hlength]
  · intro n hnleft _hnright
    have hn_round : n < rounds.length := by simpa using hnleft
    have hn : n < horizon := by simpa [hlength] using hn_round
    let time : Fin horizon := ⟨n, hn⟩
    have hvalue := congrFun hpath time
    unfold unitCoordinateVovkFiniteTableOutcomePath at hvalue
    change (rounds.get (Fin.cast hlength.symm time)).outcome = outcomes time at hvalue
    have hindex : Fin.cast hlength.symm time = ⟨n, hn_round⟩ := by
      apply Fin.ext
      rfl
    rw [hindex] at hvalue
    have hext : outcomes time = unitCoordinateExtendFiniteOutcomePath outcomes n := by
      symm
      simpa [time] using unitCoordinateExtendFiniteOutcomePath_apply outcomes time
    simpa [rounds, hlength] using hvalue.trans hext

/--
Some realized outcome path of the finite adaptive game has at least its
uniform pigeonhole probability under the uniform finite pure-table law.
This is the finite selection component of Vovk's ``suitable path'' step.
-/
theorem exists_unitCoordinateVovkFiniteTableOutcomePath_prob
    {Expert Coordinate : Type*} [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate]
    {horizon : ℕ}
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate) :
    ∃ outcomes : Fin horizon → Coordinate,
      (Fintype.card (Fin horizon → Coordinate) : ℝ)⁻¹ ≤
        pmfProb (uniformPMF (Fin horizon → Expert → Coordinate))
          (fun table =>
            unitCoordinateVovkFiniteTableOutcomePath policy outcomeSelector table = outcomes) := by
  exact exists_pmfProb_preimage_ge_inv_card
    (uniformPMF (Fin horizon → Expert → Coordinate))
    (unitCoordinateVovkFiniteTableOutcomePath policy outcomeSelector)

/--
For some selected finite outcome path, the original policy's global bound
holds on the agreement-modified game with at least the suitable-path
probability.  This is the finite probability half of Vovk's Section-6
coupling; the complementary high-probability iid tail is handled separately.
-/
theorem exists_unitCoordinateAgreementModifiedBound_prob
    {Expert Coordinate : Type*} [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate] [Nontrivial Coordinate]
    {horizon : ℕ} (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (c a : ℝ) (hpolicyBound : UnitCoordinateDecisionPolicyBound policy c a) :
    ∃ outcomes : Fin horizon → Coordinate,
      (Fintype.card (Fin horizon → Coordinate) : ℝ)⁻¹ ≤
        pmfProb (uniformPMF (Fin horizon → Expert → Coordinate))
          (fun table =>
            unitCoordinateDecisionPolicyCumulativeLoss
                (unitCoordinateAgreementModification policy
                  (unitCoordinateExtendFiniteOutcomePath outcomes))
                (unitCoordinateVovkRounds
                  (unitCoordinateAgreementModification policy
                    (unitCoordinateExtendFiniteOutcomePath outcomes))
                  maxUnitCoordinateOutcomeSelector
                  (unitCoordinateExtendFiniteTable table) horizon) ≤
              c * finiteMin (unitCoordinateDecisionExpertCumulativeLoss
                (unitCoordinateVovkRounds
                  (unitCoordinateAgreementModification policy
                    (unitCoordinateExtendFiniteOutcomePath outcomes))
                  maxUnitCoordinateOutcomeSelector
                  (unitCoordinateExtendFiniteTable table) horizon)) +
                a * Real.log (Fintype.card Expert : ℝ)) := by
  obtain ⟨outcomes, hselected⟩ :=
    exists_unitCoordinateVovkFiniteTableOutcomePath_prob
      policy maxUnitCoordinateOutcomeSelector
  refine ⟨outcomes, hselected.trans ?_⟩
  apply pmfProb_le_of_imp
  intro table hpath
  have hagrees := unitCoordinateVovkFiniteTableOutcomePath_agrees
    policy maxUnitCoordinateOutcomeSelector table outcomes hpath
  have hrounds := unitCoordinateAgreementModification_rounds_eq_of_agrees
    policy (unitCoordinateExtendFiniteOutcomePath outcomes)
    (unitCoordinateExtendFiniteTable table) horizon hagrees
  have hloss := unitCoordinateAgreementModification_policyCumulativeLoss_eq_of_agrees
    policy (unitCoordinateExtendFiniteOutcomePath outcomes)
    (unitCoordinateExtendFiniteTable table) horizon hagrees
  rw [hloss, hrounds]
  exact hpolicyBound.2 _

/--
The suitable-path bound in the expert-major iid representation.  This is the
same finite uniform table law as
`exists_unitCoordinateAgreementModifiedBound_prob`, merely transposed so that
the independent-experts probability calculation can be applied directly.
-/
theorem exists_unitCoordinateAgreementModifiedBound_prob_iidColumns
    {Expert Coordinate : Type*} [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate] [Nontrivial Coordinate]
    {horizon : ℕ} (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (c a : ℝ) (hpolicyBound : UnitCoordinateDecisionPolicyBound policy c a) :
    ∃ outcomes : Fin horizon → Coordinate,
      (Fintype.card (Fin horizon → Coordinate) : ℝ)⁻¹ ≤
        pmfProb (pmfProduct Expert (Fin horizon → Coordinate)
          (uniformPMF (Fin horizon → Coordinate)))
          (fun expertPredictions =>
            unitCoordinateDecisionPolicyCumulativeLoss
                (unitCoordinateAgreementModification policy
                  (unitCoordinateExtendFiniteOutcomePath outcomes))
                (unitCoordinateVovkRounds
                  (unitCoordinateAgreementModification policy
                    (unitCoordinateExtendFiniteOutcomePath outcomes))
                  maxUnitCoordinateOutcomeSelector
                  (unitCoordinateExtendFiniteTable
                    (fun time expert => expertPredictions expert time)) horizon) ≤
              c * finiteMin (unitCoordinateDecisionExpertCumulativeLoss
                (unitCoordinateVovkRounds
                  (unitCoordinateAgreementModification policy
                    (unitCoordinateExtendFiniteOutcomePath outcomes))
                  maxUnitCoordinateOutcomeSelector
                  (unitCoordinateExtendFiniteTable
                    (fun time expert => expertPredictions expert time)) horizon)) +
                a * Real.log (Fintype.card Expert : ℝ)) := by
  classical
  obtain ⟨outcomes, houtcomes⟩ :=
    exists_unitCoordinateAgreementModifiedBound_prob policy c a hpolicyBound
  refine ⟨outcomes, ?_⟩
  rw [pmfProduct_uniformPMF_eq_uniformPMF_fun]
  have htranspose := pmfProb_uniformPMF_equiv
    (unitCoordinateFiniteTableTransposeEquiv (Expert := Expert)
      (Coordinate := Coordinate) (horizon := horizon))
    (fun table =>
      unitCoordinateDecisionPolicyCumulativeLoss
          (unitCoordinateAgreementModification policy
            (unitCoordinateExtendFiniteOutcomePath outcomes))
          (unitCoordinateVovkRounds
            (unitCoordinateAgreementModification policy
              (unitCoordinateExtendFiniteOutcomePath outcomes))
            maxUnitCoordinateOutcomeSelector
            (unitCoordinateExtendFiniteTable table) horizon) ≤
        c * finiteMin (unitCoordinateDecisionExpertCumulativeLoss
          (unitCoordinateVovkRounds
            (unitCoordinateAgreementModification policy
              (unitCoordinateExtendFiniteOutcomePath outcomes))
            maxUnitCoordinateOutcomeSelector
            (unitCoordinateExtendFiniteTable table) horizon)) +
          a * Real.log (Fintype.card Expert : ℝ))
    (fun expertPredictions =>
      unitCoordinateDecisionPolicyCumulativeLoss
          (unitCoordinateAgreementModification policy
            (unitCoordinateExtendFiniteOutcomePath outcomes))
          (unitCoordinateVovkRounds
            (unitCoordinateAgreementModification policy
              (unitCoordinateExtendFiniteOutcomePath outcomes))
            maxUnitCoordinateOutcomeSelector
            (unitCoordinateExtendFiniteTable
              (fun time expert => expertPredictions expert time)) horizon) ≤
        c * finiteMin (unitCoordinateDecisionExpertCumulativeLoss
          (unitCoordinateVovkRounds
            (unitCoordinateAgreementModification policy
              (unitCoordinateExtendFiniteOutcomePath outcomes))
            maxUnitCoordinateOutcomeSelector
            (unitCoordinateExtendFiniteTable
              (fun time expert => expertPredictions expert time)) horizon)) +
          a * Real.log (Fintype.card Expert : ℝ))
    (by
      intro expertPredictions
      rfl)
  exact houtcomes.trans htranspose.le

/-- The reciprocal finite-path count is the familiar `|Coordinate|^{-T}` factor. -/
theorem inv_card_unitCoordinateOutcomePaths
  {Coordinate : Type*} [Fintype Coordinate] (horizon : ℕ) :
    (Fintype.card (Fin horizon → Coordinate) : ℝ)⁻¹ =
      (Fintype.card Coordinate : ℝ)⁻¹ ^ horizon := by
  simp

/--
The cumulative loss of one pure-table expert along a Vovk game tree, written
recursively with the same history update as `unitCoordinateVovkRoundsFrom`.
This is the dynamic (outcome-adaptive) counterpart of the fixed-path sum used
by the iid calculation above.
-/
noncomputable def unitCoordinateVovkPureExpertCumulativeLossFrom
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (expert : Expert) :
    ℕ → List (UnitCoordinateDecisionRound Expert Coordinate) → ℝ
  | 0, _history => 0
  | time + 1, history =>
      let expertDecision := unitCoordinatePureExpertDecisions table history.length
      let learnerDecision := policy history expertDecision
      let outcome := outcomeSelector learnerDecision
      let round : UnitCoordinateDecisionRound Expert Coordinate :=
        { expertDecision := expertDecision
          expertDecision_mem := unitCoordinatePureExpertDecisions_mem table history.length
          outcome := outcome }
      unitCoordinateLoss (table history.length expert) outcome +
        unitCoordinateVovkPureExpertCumulativeLossFrom policy outcomeSelector table expert
          time (history ++ [round])

/--
The pure-expert loss along a prescribed outcome path, starting at a given
time.  This is the fixed-path quantity to which the agreement-modified game
reduces before the iid calculation.
-/
noncomputable def unitCoordinateTargetPureExpertCumulativeLossFrom
    {Expert Coordinate : Type*}
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (expert : Expert)
    (target : ℕ → Coordinate) : ℕ → ℕ → ℝ
  | _start, 0 => 0
  | start, horizon + 1 =>
      unitCoordinateLoss (table start expert) (target start) +
        unitCoordinateTargetPureExpertCumulativeLossFrom table expert target (start + 1) horizon

/--
The agreement-modified game evaluates each pure expert against the prescribed
outcome path exactly, even though the original game tree is adaptive.
-/
theorem unitCoordinateVovkPureExpertCumulativeLossFrom_agreementModification_eq_target
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate) (target : ℕ → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (expert : Expert) :
    ∀ (horizon : ℕ) (history : List (UnitCoordinateDecisionRound Expert Coordinate)),
      unitCoordinateVovkPureExpertCumulativeLossFrom
          (unitCoordinateAgreementModification policy target)
          maxUnitCoordinateOutcomeSelector table expert horizon history =
        unitCoordinateTargetPureExpertCumulativeLossFrom table expert target history.length horizon := by
  intro horizon
  induction horizon with
  | zero =>
      intro history
      rfl
  | succ horizon ih =>
      intro history
      let expertDecision := unitCoordinatePureExpertDecisions table history.length
      let learnerDecision :=
        unitCoordinateAgreementModification policy target history expertDecision
      let outcome := maxUnitCoordinateOutcomeSelector learnerDecision
      let round : UnitCoordinateDecisionRound Expert Coordinate :=
        { expertDecision := expertDecision
          expertDecision_mem := unitCoordinatePureExpertDecisions_mem table history.length
          outcome := outcome }
      have houtcome : outcome = target history.length := by
        dsimp [outcome, learnerDecision]
        exact maxUnitCoordinateOutcomeSelector_agreementModification
          policy target history expertDecision
      change unitCoordinateLoss (table history.length expert) outcome +
          unitCoordinateVovkPureExpertCumulativeLossFrom
            (unitCoordinateAgreementModification policy target)
            maxUnitCoordinateOutcomeSelector table expert horizon (history ++ [round]) =
          unitCoordinateLoss (table history.length expert) (target history.length) +
            unitCoordinateTargetPureExpertCumulativeLossFrom table expert target
              (history.length + 1) horizon
      rw [houtcome, ih (history ++ [round])]
      simp [List.length_append]

/-- The recursive prescribed-path loss is its finite indexed sum. -/
theorem unitCoordinateTargetPureExpertCumulativeLossFrom_eq_sum
    {Expert Coordinate : Type*}
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (expert : Expert)
    (target : ℕ → Coordinate) :
    ∀ (start horizon : ℕ),
      unitCoordinateTargetPureExpertCumulativeLossFrom table expert target start horizon =
        ∑ time : Fin horizon,
          unitCoordinateLoss (table (start + time) expert) (target (start + time)) := by
  intro start horizon
  induction horizon generalizing start with
  | zero =>
      simp [unitCoordinateTargetPureExpertCumulativeLossFrom]
  | succ horizon ih =>
      rw [unitCoordinateTargetPureExpertCumulativeLossFrom, Fin.sum_univ_succ,
        ih (start + 1)]
      simp [Nat.add_comm, Nat.add_left_comm]

/-- At time zero, the recursive prescribed-path loss is the ordinary finite path sum. -/
theorem unitCoordinateTargetPureExpertCumulativeLossFrom_zero_eq_cumulative
    {Expert Coordinate : Type*} {horizon : ℕ}
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (expert : Expert)
    (target : ℕ → Coordinate) :
    unitCoordinateTargetPureExpertCumulativeLossFrom table expert target 0 horizon =
      unitCoordinatePureExpertCumulativeLoss
        (fun time : Fin horizon => target time)
        (fun time : Fin horizon => table time expert) := by
  rw [unitCoordinateTargetPureExpertCumulativeLossFrom_eq_sum]
  unfold unitCoordinatePureExpertCumulativeLoss
  refine Finset.sum_congr rfl ?_
  intro time _htime
  simp

/--
The agreement-modified dynamic game has exactly the same pure-expert loss as
the corresponding fixed outcome path.  This is the bridge that makes the iid
tail calculation applicable after the source's policy modification.
-/
theorem unitCoordinateVovkPureExpertCumulativeLoss_agreementModification_eq_fixedPath
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate] {horizon : ℕ}
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate) (target : ℕ → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (expert : Expert) :
    unitCoordinateVovkPureExpertCumulativeLossFrom
        (unitCoordinateAgreementModification policy target)
        maxUnitCoordinateOutcomeSelector table expert horizon [] =
      unitCoordinatePureExpertCumulativeLoss
        (fun time : Fin horizon => target time)
        (fun time : Fin horizon => table time expert) := by
  calc
    unitCoordinateVovkPureExpertCumulativeLossFrom
        (unitCoordinateAgreementModification policy target)
        maxUnitCoordinateOutcomeSelector table expert horizon [] =
        unitCoordinateTargetPureExpertCumulativeLossFrom table expert target 0 horizon := by
          simpa using
            (unitCoordinateVovkPureExpertCumulativeLossFrom_agreementModification_eq_target
              policy target table expert horizon [])
    _ = unitCoordinatePureExpertCumulativeLoss
        (fun time : Fin horizon => target time)
        (fun time : Fin horizon => table time expert) :=
      unitCoordinateTargetPureExpertCumulativeLossFrom_zero_eq_cumulative table expert target

/--
Under the agreement modification, the independent-experts calculation has the
same exact no-good-expert probability as it has against a fixed outcome path.
This is the formal Section-6 bridge from the adaptive game tree to the iid
Cramer tail.
-/
theorem pmfProduct_uniform_noGoodAgreementModifiedExpert_prob
    {Expert Coordinate : Type*} [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate] [Nontrivial Coordinate]
    {horizon : ℕ} (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (outcomes : Fin horizon → Coordinate) (base : Coordinate) (z : ℝ) :
    pmfProb
        (pmfProduct Expert (Fin horizon → Coordinate)
          (uniformPMF (Fin horizon → Coordinate)))
        (fun expertPredictions =>
          ∀ expert,
            ¬ unitCoordinateVovkPureExpertCumulativeLossFrom
                (unitCoordinateAgreementModification policy
                  (unitCoordinateExtendFiniteOutcomePath outcomes))
                maxUnitCoordinateOutcomeSelector
                (unitCoordinateExtendFiniteTable
                  (fun time expert => expertPredictions expert time))
                expert horizon [] ≤ (horizon : ℝ) * z) =
      (1 - Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
        (fun coordinate => unitCoordinateLoss coordinate base - z) 0 horizon) ^
        Fintype.card Expert := by
  classical
  have hpred : ∀ (expertPredictions : Expert → Fin horizon → Coordinate) (expert : Expert),
      unitCoordinateVovkPureExpertCumulativeLossFrom
          (unitCoordinateAgreementModification policy
            (unitCoordinateExtendFiniteOutcomePath outcomes))
          maxUnitCoordinateOutcomeSelector
          (unitCoordinateExtendFiniteTable
            (fun time sourceExpert => expertPredictions sourceExpert time))
          expert horizon [] =
        unitCoordinatePureExpertCumulativeLoss outcomes (expertPredictions expert) := by
    intro expertPredictions expert
    rw [unitCoordinateVovkPureExpertCumulativeLoss_agreementModification_eq_fixedPath]
    refine Finset.sum_congr rfl ?_
    intro time _htime
    simp [unitCoordinateExtendFiniteTable, unitCoordinateExtendFiniteOutcomePath_apply,
      time.isLt]
  calc
    pmfProb
        (pmfProduct Expert (Fin horizon → Coordinate)
          (uniformPMF (Fin horizon → Coordinate)))
        (fun expertPredictions =>
          ∀ expert,
            ¬ unitCoordinateVovkPureExpertCumulativeLossFrom
                (unitCoordinateAgreementModification policy
                  (unitCoordinateExtendFiniteOutcomePath outcomes))
                maxUnitCoordinateOutcomeSelector
                (unitCoordinateExtendFiniteTable
                  (fun time expert => expertPredictions expert time))
                expert horizon [] ≤ (horizon : ℝ) * z) =
      pmfProb
        (pmfProduct Expert (Fin horizon → Coordinate)
          (uniformPMF (Fin horizon → Coordinate)))
        (fun expertPredictions =>
          ∀ expert,
            ¬ unitCoordinatePureExpertCenteredCumulativeLoss outcomes
                (expertPredictions expert) z ≤ 0) := by
          apply pmfProb_congr
          intro expertPredictions
          constructor <;> intro h expert hexpert
          · apply h expert
            rw [hpred expertPredictions expert]
            rw [unitCoordinatePureExpertCenteredCumulativeLoss_eq] at hexpert
            linarith
          · apply h expert
            rw [hpred expertPredictions expert] at hexpert
            rw [unitCoordinatePureExpertCenteredCumulativeLoss_eq]
            linarith
    _ = (1 - Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
        (fun coordinate => unitCoordinateLoss coordinate base - z) 0 horizon) ^
          Fintype.card Expert :=
      pmfProduct_uniform_noCenteredGoodExpert_prob outcomes base z

/-- The dynamic pure-expert sum equals the decision-game comparator loss exactly. -/
theorem unitCoordinateVovkPureExpertCumulativeLossFrom_eq
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (expert : Expert) :
    ∀ (horizon : ℕ) (history : List (UnitCoordinateDecisionRound Expert Coordinate)),
      unitCoordinateVovkPureExpertCumulativeLossFrom policy outcomeSelector table expert
        horizon history =
        unitCoordinateDecisionExpertCumulativeLoss
          (unitCoordinateVovkRoundsFrom policy outcomeSelector table horizon history) expert := by
  intro horizon
  induction horizon with
  | zero =>
      intro history
      rfl
  | succ horizon ih =>
      intro history
      let expertDecision := unitCoordinatePureExpertDecisions table history.length
      let learnerDecision := policy history expertDecision
      let outcome := outcomeSelector learnerDecision
      let round : UnitCoordinateDecisionRound Expert Coordinate :=
        { expertDecision := expertDecision
          expertDecision_mem := unitCoordinatePureExpertDecisions_mem table history.length
          outcome := outcome }
      change unitCoordinateLoss (table history.length expert) outcome +
          unitCoordinateVovkPureExpertCumulativeLossFrom policy outcomeSelector table expert
            horizon (history ++ [round]) =
        unitCoordinateDecisionExpertCumulativeLoss
          (round :: unitCoordinateVovkRoundsFrom policy outcomeSelector table horizon
            (history ++ [round])) expert
      rw [ih (history ++ [round])]
      simp only [unitCoordinateDecisionExpertCumulativeLoss, List.map_cons, List.sum_cons,
        UnitCoordinateDecisionRound.inducedLoss, unitCoordinateDecisionLoss]
      have hroundloss : unitCoordinateLoss (table history.length expert) outcome =
          round.expertDecision expert round.outcome := by
        simp [round, expertDecision, unitCoordinatePureExpertDecisions,
          unitCoordinatePureDecision, unitCoordinateLoss]
      rw [hroundloss]

/-- The empty-history pure-table sum is the decision-game expert cumulative loss. -/
theorem unitCoordinateVovkPureExpertCumulativeLoss_eq
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (expert : Expert)
    (horizon : ℕ) :
    unitCoordinateVovkPureExpertCumulativeLossFrom policy outcomeSelector table expert
      horizon [] =
      unitCoordinateDecisionExpertCumulativeLoss
        (unitCoordinateVovkRounds policy outcomeSelector table horizon) expert := by
  exact unitCoordinateVovkPureExpertCumulativeLossFrom_eq
    policy outcomeSelector table expert horizon []

/--
One dynamic pure-table expert below a proposed threshold witnesses the same
upper bound on the decision game's best-expert comparator.
-/
theorem finiteMin_unitCoordinateVovkRounds_expert_le
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Expert]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (expert : Expert)
    (horizon : ℕ) {bound : ℝ}
    (hexpert :
      unitCoordinateVovkPureExpertCumulativeLossFrom policy outcomeSelector table expert
        horizon [] ≤ bound) :
    finiteMin (unitCoordinateDecisionExpertCumulativeLoss
      (unitCoordinateVovkRounds policy outcomeSelector table horizon)) ≤ bound := by
  calc
    finiteMin (unitCoordinateDecisionExpertCumulativeLoss
        (unitCoordinateVovkRounds policy outcomeSelector table horizon)) ≤
      unitCoordinateDecisionExpertCumulativeLoss
        (unitCoordinateVovkRounds policy outcomeSelector table horizon) expert :=
          finiteMin_le _ expert
    _ = unitCoordinateVovkPureExpertCumulativeLossFrom policy outcomeSelector table expert
        horizon [] := (unitCoordinateVovkPureExpertCumulativeLoss_eq
          policy outcomeSelector table expert horizon).symm
    _ ≤ bound := hexpert

/--
If a selector enforces a strict per-round learner-loss floor on every simplex,
then the induced Vovk game tree has a strict cumulative floor at every positive
horizon.  This is the deterministic half of Vovk's Section 6 contradiction.
-/
theorem unitCoordinateVovkRoundsFrom_cumulativeLoss_gt
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Expert]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (hpolicy : UnitCoordinateDecisionPolicyAdmissible policy)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (floor : ℝ)
    (hselector : ∀ learnerDecision : Coordinate → ℝ,
      FiniteProbabilitySimplex learnerDecision →
        floor < unitCoordinateDecisionLoss learnerDecision (outcomeSelector learnerDecision)) :
    ∀ (horizon : ℕ) (history : List (UnitCoordinateDecisionRound Expert Coordinate)),
      (∀ round ∈ history, ∀ expert,
        FiniteProbabilitySimplex (round.expertDecision expert)) →
      0 < horizon →
      (horizon : ℝ) * floor <
        unitCoordinateDecisionPolicyCumulativeLossFrom policy history
          (unitCoordinateVovkRoundsFrom policy outcomeSelector table horizon history) := by
  intro horizon
  induction horizon with
  | zero =>
      intro _history _hvalid hpositive
      exact False.elim (Nat.not_lt_zero _ hpositive)
  | succ horizon ih =>
      intro history hvalid _hpositive
      let expertDecision := unitCoordinatePureExpertDecisions table history.length
      let learnerDecision := policy history expertDecision
      let outcome := outcomeSelector learnerDecision
      let round : UnitCoordinateDecisionRound Expert Coordinate :=
        { expertDecision := expertDecision
          expertDecision_mem := unitCoordinatePureExpertDecisions_mem table history.length
          outcome := outcome }
      have hlearnerDecision : FiniteProbabilitySimplex learnerDecision := by
        exact hpolicy history expertDecision
          (unitCoordinatePureExpertDecisions_mem table history.length)
      have hroundFloor : floor < unitCoordinateDecisionLoss learnerDecision outcome := by
        exact hselector learnerDecision hlearnerDecision
      have hvalidNext :
          ∀ previousRound ∈ history ++ [round], ∀ expert,
            FiniteProbabilitySimplex (previousRound.expertDecision expert) := by
        intro previousRound hpreviousRound expert
        rcases List.mem_append.mp hpreviousRound with hinHistory | hround
        · exact hvalid previousRound hinHistory expert
        · have hpreviousRound_eq : previousRound = round := by
            simpa using hround
          subst previousRound
          exact round.expertDecision_mem expert
      have htree :
          unitCoordinateVovkRoundsFrom policy outcomeSelector table (horizon + 1) history =
            round :: unitCoordinateVovkRoundsFrom policy outcomeSelector table horizon
              (history ++ [round]) := by
        rfl
      rw [htree]
      simp only [unitCoordinateDecisionPolicyCumulativeLossFrom]
      rw [Nat.cast_add, Nat.cast_one]
      change ((horizon : ℝ) + 1) * floor <
        unitCoordinateDecisionLoss learnerDecision outcome +
          unitCoordinateDecisionPolicyCumulativeLossFrom policy (history ++ [round])
            (unitCoordinateVovkRoundsFrom policy outcomeSelector table horizon
              (history ++ [round]))
      by_cases hzero : horizon = 0
      · subst horizon
        simpa [unitCoordinateVovkRoundsFrom, unitCoordinateDecisionPolicyCumulativeLossFrom]
          using hroundFloor
      · have htail := ih (history ++ [round]) hvalidNext (Nat.pos_of_ne_zero hzero)
        nlinarith

/-- The empty-history game tree inherits the selector's strict cumulative floor. -/
theorem unitCoordinateVovkRounds_cumulativeLoss_gt
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Expert]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (hpolicy : UnitCoordinateDecisionPolicyAdmissible policy)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (floor : ℝ)
    (hselector : ∀ learnerDecision : Coordinate → ℝ,
      FiniteProbabilitySimplex learnerDecision →
        floor < unitCoordinateDecisionLoss learnerDecision (outcomeSelector learnerDecision))
    (horizon : ℕ) (hpositive : 0 < horizon) :
    (horizon : ℝ) * floor <
      unitCoordinateDecisionPolicyCumulativeLoss policy
        (unitCoordinateVovkRounds policy outcomeSelector table horizon) := by
  exact unitCoordinateVovkRoundsFrom_cumulativeLoss_gt policy hpolicy outcomeSelector table floor
    hselector horizon [] (by simp) hpositive

/--
The weak version of the game-tree floor.  It is obtained from the strict
version by lowering the floor by a positive epsilon, which keeps the recursive
proof and the source's weak max-coordinate inequality in one common API.
-/
theorem unitCoordinateVovkRounds_cumulativeLoss_ge
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Expert]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (hpolicy : UnitCoordinateDecisionPolicyAdmissible policy)
    (outcomeSelector : (Coordinate → ℝ) → Coordinate)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (floor : ℝ)
    (hselector : ∀ learnerDecision : Coordinate → ℝ,
      FiniteProbabilitySimplex learnerDecision →
        floor ≤ unitCoordinateDecisionLoss learnerDecision (outcomeSelector learnerDecision))
    (horizon : ℕ) (hpositive : 0 < horizon) :
    (horizon : ℝ) * floor ≤
      unitCoordinateDecisionPolicyCumulativeLoss policy
        (unitCoordinateVovkRounds policy outcomeSelector table horizon) := by
  by_contra hnot
  have hstrict :
      unitCoordinateDecisionPolicyCumulativeLoss policy
          (unitCoordinateVovkRounds policy outcomeSelector table horizon) <
        (horizon : ℝ) * floor :=
    lt_of_not_ge hnot
  have hhorizon_pos : 0 < (horizon : ℝ) := by
    exact_mod_cast hpositive
  let epsilon : ℝ :=
    ((horizon : ℝ) * floor -
      unitCoordinateDecisionPolicyCumulativeLoss policy
        (unitCoordinateVovkRounds policy outcomeSelector table horizon)) /
      (2 * (horizon : ℝ))
  have hepsilon_pos : 0 < epsilon := by
    dsimp [epsilon]
    exact div_pos (sub_pos.mpr hstrict) (by positivity)
  have hselector_strict : ∀ learnerDecision : Coordinate → ℝ,
      FiniteProbabilitySimplex learnerDecision →
        floor - epsilon <
          unitCoordinateDecisionLoss learnerDecision (outcomeSelector learnerDecision) := by
    intro learnerDecision hlearnerDecision
    exact (sub_lt_self floor hepsilon_pos).trans_le
      (hselector learnerDecision hlearnerDecision)
  have hlower := unitCoordinateVovkRounds_cumulativeLoss_gt policy hpolicy
    outcomeSelector table (floor - epsilon) hselector_strict horizon hpositive
  dsimp [epsilon] at hlower
  field_simp at hlower
  nlinarith

/--
Against the literal Vovk max-coordinate environment, an admissible policy
loses at least `horizon / |Coordinate|` over every positive finite horizon.
This is the unit-coordinate form of the source quantity `R` in Eq. (44).
-/
theorem maxUnitCoordinateVovkRounds_cumulativeLoss_ge
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Expert] [Nonempty Coordinate]
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (hpolicy : UnitCoordinateDecisionPolicyAdmissible policy)
    (table : UnitCoordinatePureExpertTable Expert Coordinate)
    (horizon : ℕ) (hpositive : 0 < horizon) :
    (horizon : ℝ) * (Fintype.card Coordinate : ℝ)⁻¹ ≤
      unitCoordinateDecisionPolicyCumulativeLoss policy
        (unitCoordinateVovkRounds policy maxUnitCoordinateOutcomeSelector table horizon) := by
  exact unitCoordinateVovkRounds_cumulativeLoss_ge policy hpolicy
    maxUnitCoordinateOutcomeSelector table (Fintype.card Coordinate : ℝ)⁻¹
    unitCoordinateDecisionLoss_le_maxUnitCoordinateOutcomeSelector horizon hpositive

/--
The deterministic endpoint of Vovk's Section-6 argument for the literal
max-coordinate environment.  Once the probabilistic construction supplies a
pure table having one sufficiently low-loss expert, the alleged global
`(c,a)` guarantee contradicts the forced learner-loss floor.
-/
theorem maxUnitCoordinateVovkRounds_goodExpert_contradiction
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Expert] [Nonempty Coordinate]
    {c a comparatorBound : ℝ} (hc_nonneg : 0 ≤ c)
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (hbound : UnitCoordinateDecisionPolicyBound policy c a)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (expert : Expert)
    (horizon : ℕ) (hpositive : 0 < horizon)
    (hexpert :
      unitCoordinateVovkPureExpertCumulativeLossFrom policy
        maxUnitCoordinateOutcomeSelector table expert horizon [] ≤ comparatorBound)
    (hgap : c * comparatorBound + a * Real.log (Fintype.card Expert : ℝ) <
      (horizon : ℝ) * (Fintype.card Coordinate : ℝ)⁻¹) :
    False := by
  have hlower := maxUnitCoordinateVovkRounds_cumulativeLoss_ge
    policy hbound.1 table horizon hpositive
  have hupper := hbound.2
    (unitCoordinateVovkRounds policy maxUnitCoordinateOutcomeSelector table horizon)
  have hcomparator := finiteMin_unitCoordinateVovkRounds_expert_le
    policy maxUnitCoordinateOutcomeSelector table expert horizon hexpert
  have hcomparatorScaled :
      c * finiteMin (unitCoordinateDecisionExpertCumulativeLoss
        (unitCoordinateVovkRounds policy maxUnitCoordinateOutcomeSelector table horizon)) ≤
        c * comparatorBound :=
    mul_le_mul_of_nonneg_left hcomparator hc_nonneg
  nlinarith

/--
The per-realization form of the Section-6 endpoint.  Unlike
`maxUnitCoordinateVovkRounds_goodExpert_contradiction`, this lemma only asks
for the alleged `(c,a)` bound on the particular game tree at hand.  It is
therefore the form used after the agreement modification transfers the
original policy's bound to a selected outcome branch.
-/
theorem maxUnitCoordinateVovkRounds_bound_and_goodExpert_contradiction
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Expert] [Nonempty Coordinate]
    {c a comparatorBound : ℝ} (hc_nonneg : 0 ≤ c)
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (hpolicy : UnitCoordinateDecisionPolicyAdmissible policy)
    (table : UnitCoordinatePureExpertTable Expert Coordinate) (expert : Expert)
    (horizon : ℕ) (hpositive : 0 < horizon)
    (hbound :
      unitCoordinateDecisionPolicyCumulativeLoss policy
          (unitCoordinateVovkRounds policy maxUnitCoordinateOutcomeSelector table horizon) ≤
        c * finiteMin (unitCoordinateDecisionExpertCumulativeLoss
          (unitCoordinateVovkRounds policy maxUnitCoordinateOutcomeSelector table horizon)) +
          a * Real.log (Fintype.card Expert : ℝ))
    (hexpert :
      unitCoordinateVovkPureExpertCumulativeLossFrom policy
        maxUnitCoordinateOutcomeSelector table expert horizon [] ≤ comparatorBound)
    (hgap : c * comparatorBound + a * Real.log (Fintype.card Expert : ℝ) <
      (horizon : ℝ) * (Fintype.card Coordinate : ℝ)⁻¹) :
    False := by
  have hlower := maxUnitCoordinateVovkRounds_cumulativeLoss_ge
    policy hpolicy table horizon hpositive
  have hcomparator := finiteMin_unitCoordinateVovkRounds_expert_le
    policy maxUnitCoordinateOutcomeSelector table expert horizon hexpert
  have hcomparatorScaled :
      c * finiteMin (unitCoordinateDecisionExpertCumulativeLoss
        (unitCoordinateVovkRounds policy maxUnitCoordinateOutcomeSelector table horizon)) ≤
        c * comparatorBound :=
    mul_le_mul_of_nonneg_left hcomparator hc_nonneg
  nlinarith

/--
The finite-probability contradiction at the heart of Vovk's Section 6.  A
selected outcome path transfers the original policy bound to its agreement
modification with probability at least `|Coordinate|⁻¹ ^ horizon`; on every
such table a low-loss expert is impossible by the deterministic game-floor
argument.  The exact iid formula for the complementary no-good-expert event
therefore cannot be strictly smaller than that selected-path probability.
-/
theorem unitCoordinateSection6_finite_probability_contradiction
    {Expert Coordinate : Type*} [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Coordinate] [DecidableEq Coordinate] [Nonempty Coordinate] [Nontrivial Coordinate]
    {c a z : ℝ} (hc_nonneg : 0 ≤ c)
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (hpolicyBound : UnitCoordinateDecisionPolicyBound policy c a)
    (base : Coordinate) (horizon : ℕ) (hpositive : 0 < horizon)
    (hgap :
      c * ((horizon : ℝ) * z) + a * Real.log (Fintype.card Expert : ℝ) <
        (horizon : ℝ) * (Fintype.card Coordinate : ℝ)⁻¹)
    (hnoGood_lt :
      (1 - Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
          (fun coordinate => unitCoordinateLoss coordinate base - z) 0 horizon) ^
          Fintype.card Expert <
        (Fintype.card Coordinate : ℝ)⁻¹ ^ horizon) :
    False := by
  classical
  obtain ⟨outcomes, hselected⟩ :=
    exists_unitCoordinateAgreementModifiedBound_prob_iidColumns
      policy c a hpolicyBound
  have hbound_le_noGood :
      pmfProb (pmfProduct Expert (Fin horizon → Coordinate)
        (uniformPMF (Fin horizon → Coordinate)))
        (fun expertPredictions =>
          unitCoordinateDecisionPolicyCumulativeLoss
              (unitCoordinateAgreementModification policy
                (unitCoordinateExtendFiniteOutcomePath outcomes))
              (unitCoordinateVovkRounds
                (unitCoordinateAgreementModification policy
                  (unitCoordinateExtendFiniteOutcomePath outcomes))
                maxUnitCoordinateOutcomeSelector
                (unitCoordinateExtendFiniteTable
                  (fun time expert => expertPredictions expert time)) horizon) ≤
            c * finiteMin (unitCoordinateDecisionExpertCumulativeLoss
              (unitCoordinateVovkRounds
                (unitCoordinateAgreementModification policy
                  (unitCoordinateExtendFiniteOutcomePath outcomes))
                maxUnitCoordinateOutcomeSelector
                (unitCoordinateExtendFiniteTable
                  (fun time expert => expertPredictions expert time)) horizon)) +
              a * Real.log (Fintype.card Expert : ℝ)) ≤
        pmfProb (pmfProduct Expert (Fin horizon → Coordinate)
          (uniformPMF (Fin horizon → Coordinate)))
          (fun expertPredictions =>
            ∀ expert,
              ¬ unitCoordinateVovkPureExpertCumulativeLossFrom
                  (unitCoordinateAgreementModification policy
                    (unitCoordinateExtendFiniteOutcomePath outcomes))
                  maxUnitCoordinateOutcomeSelector
                  (unitCoordinateExtendFiniteTable
                    (fun time sourceExpert => expertPredictions sourceExpert time))
                  expert horizon [] ≤ (horizon : ℝ) * z) := by
    apply pmfProb_le_of_imp
    intro expertPredictions hbound expert hgood
    exact
      maxUnitCoordinateVovkRounds_bound_and_goodExpert_contradiction
        hc_nonneg
        (unitCoordinateAgreementModification policy
          (unitCoordinateExtendFiniteOutcomePath outcomes))
        (unitCoordinateAgreementModification_admissible policy hpolicyBound.1
          (unitCoordinateExtendFiniteOutcomePath outcomes))
        (unitCoordinateExtendFiniteTable
          (fun time sourceExpert => expertPredictions sourceExpert time))
        expert horizon hpositive hbound hgood hgap
  have hnoGood_eq := pmfProduct_uniform_noGoodAgreementModifiedExpert_prob
    policy outcomes base z
  have hselected_lower :
      (Fintype.card Coordinate : ℝ)⁻¹ ^ horizon ≤
        (1 - Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
          (fun coordinate => unitCoordinateLoss coordinate base - z) 0 horizon) ^
          Fintype.card Expert := by
    calc
      (Fintype.card Coordinate : ℝ)⁻¹ ^ horizon =
          (Fintype.card (Fin horizon → Coordinate) : ℝ)⁻¹ :=
            (inv_card_unitCoordinateOutcomePaths horizon).symm
      _ ≤ pmfProb (pmfProduct Expert (Fin horizon → Coordinate)
          (uniformPMF (Fin horizon → Coordinate)))
          (fun expertPredictions =>
            unitCoordinateDecisionPolicyCumulativeLoss
                (unitCoordinateAgreementModification policy
                  (unitCoordinateExtendFiniteOutcomePath outcomes))
                (unitCoordinateVovkRounds
                  (unitCoordinateAgreementModification policy
                    (unitCoordinateExtendFiniteOutcomePath outcomes))
                  maxUnitCoordinateOutcomeSelector
                  (unitCoordinateExtendFiniteTable
                    (fun time expert => expertPredictions expert time)) horizon) ≤
              c * finiteMin (unitCoordinateDecisionExpertCumulativeLoss
                (unitCoordinateVovkRounds
                  (unitCoordinateAgreementModification policy
                    (unitCoordinateExtendFiniteOutcomePath outcomes))
                  maxUnitCoordinateOutcomeSelector
                  (unitCoordinateExtendFiniteTable
                    (fun time expert => expertPredictions expert time)) horizon)) +
                a * Real.log (Fintype.card Expert : ℝ)) := hselected
      _ ≤ pmfProb (pmfProduct Expert (Fin horizon → Coordinate)
          (uniformPMF (Fin horizon → Coordinate)))
          (fun expertPredictions =>
            ∀ expert,
              ¬ unitCoordinateVovkPureExpertCumulativeLossFrom
                  (unitCoordinateAgreementModification policy
                    (unitCoordinateExtendFiniteOutcomePath outcomes))
                  maxUnitCoordinateOutcomeSelector
                  (unitCoordinateExtendFiniteTable
                    (fun time sourceExpert => expertPredictions sourceExpert time))
                  expert horizon [] ≤ (horizon : ℝ) * z) := hbound_le_noGood
      _ = (1 - Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
          (fun coordinate => unitCoordinateLoss coordinate base - z) 0 horizon) ^
          Fintype.card Expert := hnoGood_eq
  exact (not_lt_of_ge hselected_lower) hnoGood_lt

/--
Independent experts turn a lower bound on the expected number of good experts
into a strict upper bound on the probability that none is good.  This is the
elementary exponential estimate used in the final numerical choice in Vovk's
Section 6.
-/
theorem one_sub_pow_lt_inv_card_pow_of_log_lt_mul
    {Expert Coordinate : Type*} [Fintype Expert] [Nonempty Expert]
    [Fintype Coordinate] [Nonempty Coordinate]
    {q : ℝ} (horizon : ℕ) (hq_nonneg : 0 ≤ q) (hq_le_one : q ≤ 1)
    (hlog_lt : (horizon : ℝ) * Real.log (Fintype.card Coordinate : ℝ) <
      (Fintype.card Expert : ℝ) * q) :
    (1 - q) ^ Fintype.card Expert <
      (Fintype.card Coordinate : ℝ)⁻¹ ^ horizon := by
  have hbase_nonneg : 0 ≤ 1 - q := sub_nonneg.mpr hq_le_one
  have hbase_le_exp : 1 - q ≤ Real.exp (-q) := Real.one_sub_le_exp_neg q
  have hpow : (1 - q) ^ Fintype.card Expert ≤
      (Real.exp (-q)) ^ Fintype.card Expert :=
    pow_le_pow_left₀ hbase_nonneg hbase_le_exp _
  have hexp_pow : (Real.exp (-q)) ^ Fintype.card Expert =
      Real.exp (-((Fintype.card Expert : ℝ) * q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hcard_pos : 0 < (Fintype.card Coordinate : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Coordinate)
  have htarget_eq :
      Real.exp (-((horizon : ℝ) * Real.log (Fintype.card Coordinate : ℝ))) =
        (Fintype.card Coordinate : ℝ)⁻¹ ^ horizon := by
    calc
      Real.exp (-((horizon : ℝ) * Real.log (Fintype.card Coordinate : ℝ))) =
          Real.exp ((horizon : ℝ) * Real.log ((Fintype.card Coordinate : ℝ)⁻¹)) := by
            rw [Real.log_inv]
            ring_nf
      _ = (Real.exp (Real.log ((Fintype.card Coordinate : ℝ)⁻¹))) ^ horizon := by
            rw [Real.exp_nat_mul]
      _ = (Fintype.card Coordinate : ℝ)⁻¹ ^ horizon := by
            rw [Real.exp_log (inv_pos.mpr hcard_pos)]
  have hexp_lt : Real.exp (-((Fintype.card Expert : ℝ) * q)) <
      Real.exp (-((horizon : ℝ) * Real.log (Fintype.card Coordinate : ℝ))) := by
    apply Real.exp_lt_exp.mpr
    linarith
  calc
    (1 - q) ^ Fintype.card Expert ≤
        (Real.exp (-q)) ^ Fintype.card Expert := hpow
    _ = Real.exp (-((Fintype.card Expert : ℝ) * q)) := hexp_pow
    _ < Real.exp (-((horizon : ℝ) * Real.log (Fintype.card Coordinate : ℝ))) := hexp_lt
    _ = (Fintype.card Coordinate : ℝ)⁻¹ ^ horizon := htarget_eq

/--
Choose a finite number of experts with exponential size `exp (s * horizon)`.
Any iid good-expert probability with an eventual lower exponential bound at a
strictly smaller rate `r` then makes the expected number of good experts
dominate the selected-path cost `horizon * log k`.  This is the numerical
large-`n` choice made in Vovk's Section 6.
-/
theorem exists_nat_expertCount_for_expLowerBound
    {p : ℕ → ℝ} {k C r s : ℝ}
    (hk : 1 < k) (hC_pos : 0 < C) (hs_pos : 0 < s) (hrs : r < s)
    (hlower : ∀ᶠ horizon : ℕ in atTop,
      C * Real.exp (-(horizon : ℝ) * r) ≤ p horizon) :
    ∃ horizon expertCount : ℕ, 0 < horizon ∧ 0 < expertCount ∧
      Real.log (expertCount : ℝ) ≤ s * (horizon : ℝ) ∧
      (horizon : ℝ) * Real.log k < (expertCount : ℝ) * p horizon := by
  have hlogk_pos : 0 < Real.log k := Real.log_pos hk
  have hlogk_ne : Real.log k ≠ 0 := hlogk_pos.ne'
  have hdelta_pos : 0 < s - r := sub_pos.mpr hrs
  let rho : ℝ := Real.exp (-(s - r))
  have hrho_pos : 0 < rho := Real.exp_pos _
  have hrho_lt_one : rho < 1 := by
    dsimp [rho]
    rw [Real.exp_lt_one_iff]
    linarith
  have hdecay_base :=
    AppliedModelingLib.Math.rpow_mul_geometric_tendsto_zero (1 : ℝ) hrho_pos hrho_lt_one
  have hrho_pow : ∀ horizon : ℕ,
      rho ^ horizon = Real.exp (-(s - r) * (horizon : ℝ)) := by
    intro horizon
    dsimp [rho]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hdecay : Tendsto
      (fun horizon : ℕ => (horizon : ℝ) *
        Real.exp (-(s - r) * (horizon : ℝ))) atTop (nhds 0) := by
    refine hdecay_base.congr' ?_
    filter_upwards with horizon
    rw [Real.rpow_one, hrho_pow]
  have hsmall : ∀ᶠ horizon : ℕ in atTop,
      (horizon : ℝ) * Real.exp (-(s - r) * (horizon : ℝ)) <
        C / (2 * Real.log k) :=
    hdecay.eventually (eventually_lt_nhds (by positivity))
  have hgrowth : ∀ᶠ horizon : ℕ in atTop,
      (horizon : ℝ) * Real.log k <
        (C / 2) * Real.exp ((s - r) * (horizon : ℝ)) := by
    filter_upwards [hsmall] with horizon hsmall_horizon
    have hscaled := mul_lt_mul_of_pos_right hsmall_horizon hlogk_pos
    have hright : (C / (2 * Real.log k)) * Real.log k = C / 2 := by
      field_simp [hlogk_ne]
    rw [hright] at hscaled
    have hscaled_exp := mul_lt_mul_of_pos_right hscaled
      (Real.exp_pos ((s - r) * (horizon : ℝ)))
    have hexp_cancel :
        Real.exp (-(s - r) * (horizon : ℝ)) *
          Real.exp ((s - r) * (horizon : ℝ)) = 1 := by
      rw [← Real.exp_add]
      have hzero :
          -(s - r) * (horizon : ℝ) + (s - r) * (horizon : ℝ) = 0 := by ring
      rw [hzero, Real.exp_zero]
    calc
      (horizon : ℝ) * Real.log k =
          (((horizon : ℝ) * Real.exp (-(s - r) * (horizon : ℝ))) *
            Real.log k) * Real.exp ((s - r) * (horizon : ℝ)) := by
              calc
                (horizon : ℝ) * Real.log k =
                    ((horizon : ℝ) * Real.log k) * 1 := by ring
                _ = ((horizon : ℝ) * Real.log k) *
                    (Real.exp (-(s - r) * (horizon : ℝ)) *
                      Real.exp ((s - r) * (horizon : ℝ))) := by
                        rw [hexp_cancel]
                _ = (((horizon : ℝ) * Real.exp (-(s - r) * (horizon : ℝ))) *
                    Real.log k) * Real.exp ((s - r) * (horizon : ℝ)) := by ring
      _ < (C / 2) * Real.exp ((s - r) * (horizon : ℝ)) := hscaled_exp
  have hlinear : Tendsto (fun horizon : ℕ => s * (horizon : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hs_pos
  have hlargeExp : Tendsto
      (fun horizon : ℕ => Real.exp (s * (horizon : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlinear
  have htwo : ∀ᶠ horizon : ℕ in atTop,
      2 ≤ Real.exp (s * (horizon : ℝ)) :=
    tendsto_atTop.1 hlargeExp 2
  obtain ⟨horizon, htail, hgrowth_horizon, htwo_horizon, hpositive⟩ :=
    (hlower.and (hgrowth.and (htwo.and (eventually_gt_atTop 0)))).exists
  let expertCount : ℕ := Nat.floor (Real.exp (s * (horizon : ℝ)))
  have hfloor_le : (expertCount : ℝ) ≤ Real.exp (s * (horizon : ℝ)) := by
    exact Nat.floor_le (Real.exp_nonneg _)
  have hfloor_gt : Real.exp (s * (horizon : ℝ)) - 1 < (expertCount : ℝ) := by
    have hlt := Nat.lt_floor_add_one (Real.exp (s * (horizon : ℝ)))
    linarith
  have hfloor_half : Real.exp (s * (horizon : ℝ)) / 2 ≤ (expertCount : ℝ) := by
    nlinarith
  have hexpertCount_pos_real : 0 < (expertCount : ℝ) := by
    have hone : 1 ≤ (expertCount : ℝ) := by
      nlinarith
    linarith
  have hexpertCount_pos : 0 < expertCount := by
    exact_mod_cast hexpertCount_pos_real
  have hlog_expertCount : Real.log (expertCount : ℝ) ≤ s * (horizon : ℝ) := by
    have hlog := Real.log_le_log hexpertCount_pos_real hfloor_le
    rw [Real.log_exp] at hlog
    exact hlog
  have htail_scaled :
      (expertCount : ℝ) * (C * Real.exp (-(horizon : ℝ) * r)) ≤
        (expertCount : ℝ) * p horizon :=
    mul_le_mul_of_nonneg_left htail hexpertCount_pos_real.le
  have hexp_product :
      Real.exp (s * (horizon : ℝ)) * Real.exp (-(horizon : ℝ) * r) =
        Real.exp ((s - r) * (horizon : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfloor_scaled :
      (C / 2) * Real.exp ((s - r) * (horizon : ℝ)) ≤
        (expertCount : ℝ) * (C * Real.exp (-(horizon : ℝ) * r)) := by
    have hfactor_nonneg : 0 ≤ C * Real.exp (-(horizon : ℝ) * r) :=
      mul_nonneg hC_pos.le (Real.exp_pos (-(horizon : ℝ) * r)).le
    have hmul := mul_le_mul_of_nonneg_right hfloor_half hfactor_nonneg
    calc
      (C / 2) * Real.exp ((s - r) * (horizon : ℝ)) =
          (C / 2) * (Real.exp (s * (horizon : ℝ)) *
            Real.exp (-(horizon : ℝ) * r)) := by rw [hexp_product]
      _ = (Real.exp (s * (horizon : ℝ)) / 2) *
          (C * Real.exp (-(horizon : ℝ) * r)) := by ring
      _ ≤ (expertCount : ℝ) * (C * Real.exp (-(horizon : ℝ) * r)) := hmul
  refine ⟨horizon, expertCount, hpositive, hexpertCount_pos, hlog_expertCount, ?_⟩
  exact hgrowth_horizon.trans_le (hfloor_scaled.trans htail_scaled)

/--
At a stationary minimizer, the finite Chernoff exponent is nonnegative: the
log-MGF at that minimizer is no larger than its value zero at the origin.
This is the small analytic fact needed to leave positive rate slack in the
Section-6 choice of the number of experts.
-/
theorem finiteChernoffRate_nonneg_of_convex_stationary
    {Alphabet : Type*} [Fintype Alphabet] [DecidableEq Alphabet]
    (law : PMF Alphabet) (score : Alphabet → ℝ) {tilt : ℝ}
    (hstationary :
      (∑ signal : Alphabet,
        (law signal).toReal * (score signal * Real.exp (tilt * score signal))) = 0) :
    0 ≤ Probability.finiteChernoffRate law score := by
  have hderiv : HasDerivAt (fun t : ℝ => Probability.finiteLogMGF law score t) 0 tilt :=
    Probability.finiteLogMGF_hasDerivAt_zero_of_weighted_exp_score_sum_eq_zero
      law score hstationary
  have hminimum : ∀ t : ℝ,
      Probability.finiteLogMGF law score tilt ≤ Probability.finiteLogMGF law score t :=
    Probability.finiteLogMGF_global_min_of_convex_hasDerivAt_zero law score
      (Probability.finiteLogMGF_convex law score) hderiv
  have hminimum_zero : Probability.finiteLogMGF law score tilt ≤ 0 := by
    simpa [Probability.finiteLogMGF_zero] using hminimum 0
  rw [Probability.finiteChernoffRate_eq_neg_of_logMGF_global_min law score hminimum rfl]
  exact neg_nonneg.mpr hminimum_zero

/--
The completed finite Section-6 contradiction.  A Cramer lower certificate
for the fixed-path iid expert tail, together with a strict gap below the
uniform coordinate-loss floor, rules out a finite `(c,a)` game guarantee.

The two internally chosen rates retain separate slack: the first is used for
the Cramer lower bound and the second controls the exponentially many experts.
This is exactly the finite numerical choice in Vovk's proof, with the
adaptive policy handled by the agreement modification above.
-/
theorem not_finiteUnitCoordinateGameBounded_of_iidCramer_gap
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    {c a z : ℝ} (hc_nonneg : 0 ≤ c) (ha_pos : 0 < a)
    (base : Coordinate)
    (certificate : Probability.FiniteIidScoreCramerCertificate
      (uniformPMF Coordinate)
      (fun coordinate => unitCoordinateLoss coordinate base - z))
    (hrate_nonneg : 0 ≤ Probability.finiteChernoffRate (uniformPMF Coordinate)
      (fun coordinate => unitCoordinateLoss coordinate base - z))
    (hgap : c * z + a * Probability.finiteChernoffRate (uniformPMF Coordinate)
      (fun coordinate => unitCoordinateLoss coordinate base - z) <
        (Fintype.card Coordinate : ℝ)⁻¹) :
    ¬ finiteUnitCoordinateGameBounded Coordinate c a := by
  classical
  intro hbounded
  let rate : ℝ := Probability.finiteChernoffRate (uniformPMF Coordinate)
    (fun coordinate => unitCoordinateLoss coordinate base - z)
  let margin : ℝ :=
    ((Fintype.card Coordinate : ℝ)⁻¹ - (c * z + a * rate)) / (3 * a)
  let lowerRate : ℝ := rate + margin
  let expertRate : ℝ := rate + 2 * margin
  have hmargin_pos : 0 < margin := by
    dsimp [margin, rate]
    exact div_pos (sub_pos.mpr hgap) (mul_pos (by norm_num) ha_pos)
  have hrate_lt_lowerRate : rate < lowerRate := by
    dsimp [lowerRate]
    linarith
  have hlowerRate_lt_expertRate : lowerRate < expertRate := by
    dsimp [lowerRate, expertRate]
    linarith
  have hexpertRate_pos : 0 < expertRate := by
    dsimp [expertRate]
    linarith
  have hmargin_eq : (3 * a) * margin =
      (Fintype.card Coordinate : ℝ)⁻¹ - (c * z + a * rate) := by
    dsimp [margin]
    field_simp [ha_pos.ne']
  have hgap_expertRate : c * z + a * expertRate <
      (Fintype.card Coordinate : ℝ)⁻¹ := by
    dsimp [expertRate]
    nlinarith
  obtain ⟨prefactor, hprefactor_pos, hlower⟩ :=
    certificate.lower_bounds lowerRate hrate_lt_lowerRate
  have hcard_gt_one : 1 < (Fintype.card Coordinate : ℝ) := by
    exact_mod_cast Fintype.one_lt_card
  obtain ⟨horizon, expertCount, hhorizon_pos, hexpertCount_pos,
    hlog_expertCount, hmany_good⟩ :=
    exists_nat_expertCount_for_expLowerBound
      (k := (Fintype.card Coordinate : ℝ)) (C := prefactor)
      (r := lowerRate) (s := expertRate)
      hcard_gt_one hprefactor_pos hexpertRate_pos hlowerRate_lt_expertRate hlower
  letI : Nonempty (Fin expertCount) := ⟨⟨0, hexpertCount_pos⟩⟩
  obtain ⟨policy, hpolicyBound⟩ := hbounded (Fin expertCount)
  let tailProbability : ℝ :=
    Probability.finiteIidScoreLeftTailProb (uniformPMF Coordinate)
      (fun coordinate => unitCoordinateLoss coordinate base - z) 0 horizon
  have htail_nonneg : 0 ≤ tailProbability := by
    dsimp [tailProbability, Probability.finiteIidScoreLeftTailProb]
    exact pmfProb_nonneg _ _
  have htail_le_one : tailProbability ≤ 1 := by
    dsimp [tailProbability, Probability.finiteIidScoreLeftTailProb]
    exact pmfProb_le_one _ _
  have hno_good :
      (1 - tailProbability) ^ Fintype.card (Fin expertCount) <
        (Fintype.card Coordinate : ℝ)⁻¹ ^ horizon := by
    apply one_sub_pow_lt_inv_card_pow_of_log_lt_mul (Expert := Fin expertCount)
      (Coordinate := Coordinate) horizon htail_nonneg htail_le_one
    simpa using hmany_good
  have hhorizon_pos_real : 0 < (horizon : ℝ) := by
    exact_mod_cast hhorizon_pos
  have hlog_expertCard : Real.log (Fintype.card (Fin expertCount) : ℝ) ≤
      expertRate * (horizon : ℝ) := by
    simpa using hlog_expertCount
  have hlog_scaled : a * Real.log (Fintype.card (Fin expertCount) : ℝ) ≤
      a * (expertRate * (horizon : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog_expertCard ha_pos.le
  have hgap_horizon :
      c * ((horizon : ℝ) * z) +
          a * Real.log (Fintype.card (Fin expertCount) : ℝ) <
        (horizon : ℝ) * (Fintype.card Coordinate : ℝ)⁻¹ := by
    have hscaled := mul_lt_mul_of_pos_right hgap_expertRate hhorizon_pos_real
    calc
      c * ((horizon : ℝ) * z) +
          a * Real.log (Fintype.card (Fin expertCount) : ℝ) =
          (c * z) * (horizon : ℝ) +
            a * Real.log (Fintype.card (Fin expertCount) : ℝ) := by ring
      _ ≤ (c * z) * (horizon : ℝ) +
            a * (expertRate * (horizon : ℝ)) := by linarith
      _ = (c * z + a * expertRate) * (horizon : ℝ) := by ring
      _ < (horizon : ℝ) * (Fintype.card Coordinate : ℝ)⁻¹ := by
        linarith
  exact unitCoordinateSection6_finite_probability_contradiction
    (Expert := Fin expertCount) (Coordinate := Coordinate) hc_nonneg policy hpolicyBound
    base horizon hhorizon_pos hgap_horizon (by simpa [tailProbability] using hno_good)

/--
The Section-6 contradiction at Vovk's explicit stationary uniform tilt.  The
score is the centered unit-coordinate loss and the rate is the exact
`log β * z - log m` expression computed from that tilt.
-/
theorem not_finiteUnitCoordinateGameBounded_uniform_vovkCramer_gap
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    {β c a : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hc_nonneg : 0 ≤ c) (ha_pos : 0 < a) (base : Coordinate)
    (hgap :
      c * unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β +
        a * (Real.log β * unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β -
          Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)) <
        (Fintype.card Coordinate : ℝ)⁻¹) :
    ¬ finiteUnitCoordinateGameBounded Coordinate c a := by
  apply not_finiteUnitCoordinateGameBounded_of_iidCramer_gap hc_nonneg ha_pos base
    (finiteIidScoreCramerCertificate_uniform_unitCoordinateLoss_sub
      (Coordinate := Coordinate) hβ_pos hβ_lt_one base)
  · apply finiteChernoffRate_nonneg_of_convex_stationary
      (uniformPMF Coordinate)
      (fun coordinate => unitCoordinateLoss coordinate base -
        unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β)
    exact uniform_unitCoordinateLoss_sub_weightedExp_log_eq_zero hβ_pos base
  · rw [finiteChernoffRate_uniform_unitCoordinateLoss_sub hβ_pos base]
    exact hgap

/--
Finite Vovk alternative from the full game-tree and iid-expert argument.  If
a finite unit-coordinate game has a source `(c,a)` guarantee, then either the
one-step coefficient threshold or the additive threshold is met.
-/
theorem finiteUnitCoordinateGameBounded_vovk_alternative
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    [Nonempty Coordinate] [Nontrivial Coordinate]
    {β c a : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hc_nonneg : 0 ≤ c) (ha_pos : 0 < a)
    (hbounded : finiteUnitCoordinateGameBounded Coordinate c a) :
    (-Real.log β) /
        ((Fintype.card Coordinate : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)) ≤ c ∨
      1 /
        ((Fintype.card Coordinate : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)) ≤ a := by
  by_contra halternative
  push Not at halternative
  rcases halternative with ⟨hc_lt, ha_lt⟩
  have hthreshold_pos := unitCoordinateVovkCramerThreshold_pos_lt_one
    (Coordinate := Coordinate) hβ_pos hβ_lt_one
  have hrate_nonneg : 0 ≤
      Real.log β * unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β -
        Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) := by
    have hrate := finiteChernoffRate_nonneg_of_convex_stationary
      (uniformPMF Coordinate)
      (fun coordinate => unitCoordinateLoss coordinate (Classical.choice inferInstance) -
        unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β)
      (uniform_unitCoordinateLoss_sub_weightedExp_log_eq_zero hβ_pos
        (Classical.choice inferInstance))
    rw [finiteChernoffRate_uniform_unitCoordinateLoss_sub hβ_pos
      (Classical.choice inferInstance)] at hrate
    exact hrate
  have hfirst :
      c * unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β <
        ((-Real.log β) /
          ((Fintype.card Coordinate : ℝ) *
            -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β))) *
          unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β :=
    mul_lt_mul_of_pos_right hc_lt hthreshold_pos.1
  have hsecond :
      a * (Real.log β * unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β -
        Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)) ≤
        (1 /
          ((Fintype.card Coordinate : ℝ) *
            -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β))) *
          (Real.log β * unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β -
            Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)) :=
    mul_le_mul_of_nonneg_right ha_lt.le hrate_nonneg
  have hcard_pos : 0 < (Fintype.card Coordinate : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Coordinate)
  have hden_pos : 0 < (Fintype.card Coordinate : ℝ) *
      -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) :=
    mul_pos hcard_pos
      (vovkUniformUnitExpert_neg_log_mixMass_pos hβ_pos hβ_lt_one)
  have hlog_mix_ne : Real.log
      (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) ≠ 0 := by
    linarith [vovkUniformUnitExpert_neg_log_mixMass_pos
      (Coordinate := Coordinate) hβ_pos hβ_lt_one]
  have hidentity :
      ((-Real.log β) /
          ((Fintype.card Coordinate : ℝ) *
            -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β))) *
          unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β +
        (1 /
          ((Fintype.card Coordinate : ℝ) *
            -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β))) *
          (Real.log β * unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β -
            Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)) =
        (Fintype.card Coordinate : ℝ)⁻¹ := by
    field_simp [hcard_pos.ne', hden_pos.ne', hlog_mix_ne]
    ring
  have hgap :
      c * unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β +
        a * (Real.log β * unitCoordinateVovkCramerThreshold (Coordinate := Coordinate) β -
          Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)) <
        (Fintype.card Coordinate : ℝ)⁻¹ := by
    linarith
  exact (not_finiteUnitCoordinateGameBounded_uniform_vovkCramer_gap
    hβ_pos hβ_lt_one hc_nonneg ha_pos (Classical.choice inferInstance) hgap) hbounded

/--
The total outcome selector obtained from the uniform Vovk witness.  Its
otherwise branch is immaterial in the game tree: admissibility proves that the
learner decision is a simplex before the selector is used in a round.
-/
noncomputable def uniformUnitCoordinateVovkOutcomeSelector
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β c : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hc_lt : c < (-Real.log β) /
      ((Fintype.card Coordinate : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β))) :
    (Coordinate → ℝ) → Coordinate := by
  classical
  intro learnerMass
  if hlearnerMass : FiniteProbabilitySimplex learnerMass then
    exact uniformUnitCoordinateViolatingOutcome hβ_pos hβ_lt_one hc_lt learnerMass hlearnerMass
  else
    exact Classical.choice (inferInstance : Nonempty Coordinate)

/-- The uniform selector enforces the strict failed-one-step inequality on a simplex. -/
theorem uniformUnitCoordinateVovkOutcomeSelector_spec
    {Coordinate : Type*} [Fintype Coordinate] [Nonempty Coordinate]
    {β c : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hc_lt : c < (-Real.log β) /
      ((Fintype.card Coordinate : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)))
    (learnerMass : Coordinate → ℝ) (hlearnerMass : FiniteProbabilitySimplex learnerMass) :
    c * (Real.log (unitCoordinateDiscountedMixMass β
      (fun _expert : Coordinate => (Fintype.card Coordinate : ℝ)⁻¹)
      (uniformUnitCoordinateVovkOutcomeSelector hβ_pos hβ_lt_one hc_lt learnerMass)) /
        Real.log β) <
      unitCoordinateDecisionLoss learnerMass
        (uniformUnitCoordinateVovkOutcomeSelector hβ_pos hβ_lt_one hc_lt learnerMass) := by
  rw [uniformUnitCoordinateVovkOutcomeSelector, dif_pos hlearnerMass]
  exact uniformUnitCoordinateViolatingOutcome_spec hβ_pos hβ_lt_one hc_lt learnerMass
    hlearnerMass

/--
Under a coefficient below the Appendix Eq. (31) threshold, the uniform Vovk
selector forces a strict cumulative learner-loss lower bound against every
admissible policy and every pure-expert table.  The probabilistic part of
Vovk's Section 6 will supply the table with a sufficiently good expert.
-/
theorem uniformUnitCoordinateVovkRounds_cumulativeLoss_gt
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Expert] [Nonempty Coordinate]
    {β c : ℝ} (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hc_lt : c < (-Real.log β) /
      ((Fintype.card Coordinate : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)))
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (hpolicy : UnitCoordinateDecisionPolicyAdmissible policy)
    (table : UnitCoordinatePureExpertTable Expert Coordinate)
    (horizon : ℕ) (hpositive : 0 < horizon) :
    (horizon : ℝ) *
        (c * (Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) /
          Real.log β)) <
      unitCoordinateDecisionPolicyCumulativeLoss policy
        (unitCoordinateVovkRounds policy
          (uniformUnitCoordinateVovkOutcomeSelector hβ_pos hβ_lt_one hc_lt)
          table horizon) := by
  apply unitCoordinateVovkRounds_cumulativeLoss_gt policy hpolicy
    (uniformUnitCoordinateVovkOutcomeSelector hβ_pos hβ_lt_one hc_lt) table
    (c * (Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) /
      Real.log β))
  · intro learnerDecision hlearnerDecision
    simpa [unitCoordinateDecisionLoss, unitCoordinateDiscountedMixMass_uniform] using
      (uniformUnitCoordinateVovkOutcomeSelector_spec hβ_pos hβ_lt_one hc_lt
        learnerDecision hlearnerDecision)
  · exact hpositive

/--
A pure-expert table whose best expert beats a proposed comparator threshold
contradicts a global decision-game bound whenever the uniform Vovk selector's
cumulative floor is strictly larger than that threshold's source right-hand
side.  The iid/Cramer layer need only produce the table and its comparator
certificate to invoke this deterministic endpoint.
-/
theorem uniformUnitCoordinateVovkRounds_goodExpert_contradiction
    {Expert Coordinate : Type*} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Expert] [Nonempty Coordinate]
    {β c a comparatorBound : ℝ} (hc_nonneg : 0 ≤ c)
    (hβ_pos : 0 < β) (hβ_lt_one : β < 1)
    (hc_lt : c < (-Real.log β) /
      ((Fintype.card Coordinate : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β)))
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (hbound : UnitCoordinateDecisionPolicyBound policy c a)
    (table : UnitCoordinatePureExpertTable Expert Coordinate)
    (horizon : ℕ) (hpositive : 0 < horizon)
    (hcomparator :
      finiteMin (unitCoordinateDecisionExpertCumulativeLoss
        (unitCoordinateVovkRounds policy
          (uniformUnitCoordinateVovkOutcomeSelector hβ_pos hβ_lt_one hc_lt)
          table horizon)) ≤ comparatorBound)
    (hgap : c * comparatorBound + a * Real.log (Fintype.card Expert : ℝ) <
      (horizon : ℝ) *
        (c * (Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) β) /
          Real.log β))) :
    False := by
  have hlower := uniformUnitCoordinateVovkRounds_cumulativeLoss_gt
    hβ_pos hβ_lt_one hc_lt policy hbound.1 table horizon hpositive
  have hupper := hbound.2
    (unitCoordinateVovkRounds policy
      (uniformUnitCoordinateVovkOutcomeSelector hβ_pos hβ_lt_one hc_lt)
      table horizon)
  have hcomparatorScaled :
      c * finiteMin (unitCoordinateDecisionExpertCumulativeLoss
        (unitCoordinateVovkRounds policy
          (uniformUnitCoordinateVovkOutcomeSelector hβ_pos hβ_lt_one hc_lt)
          table horizon)) ≤ c * comparatorBound := by
    exact mul_le_mul_of_nonneg_left hcomparator hc_nonneg
  nlinarith

end Online
end Learning
end AppliedModelingLib
