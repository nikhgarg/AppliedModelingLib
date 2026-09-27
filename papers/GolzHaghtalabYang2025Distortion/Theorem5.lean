import AppliedModelingLib.Alignment.Welfare.Borda
import AppliedModelingLib.Foundations.Probability.Weighted
import GolzHaghtalabYang2025Distortion.Theorem3
import Mathlib.Tactic

/-!
# Theorem 12: Borda lower-bound population

Appendix E.2 supplies the formal version of Theorem 5.  Its three-type
population is parameterized by `ε`, `ε₀`, and `γ`; this file starts from the
literal displayed weights and utility vectors before establishing the Borda
score separation and the limiting Eq. (10) ratio.
-/

namespace GolzHaghtalabYang2025Distortion

open AppliedModelingLib
open AppliedModelingLib.Alignment.Welfare
open scoped Topology

/-- The first type's displayed mass in Appendix E.2. -/
noncomputable def theorem12TypeAMass (beta epsilon : ℝ) : ℝ :=
  theorem3SpecialTypeMass beta epsilon

/-- The second type's displayed mass in Appendix E.2. -/
noncomputable def theorem12TypeBMass (beta epsilon gamma : ℝ) : ℝ :=
  theorem12TypeAMass beta epsilon *
    (Real.sigmoid (beta * gamma) - (1 : ℝ) / 2) /
      (Real.sigmoid beta - (1 : ℝ) / 2)

/-- The three source type weights, indexed as `A`, `B`, and `C`. -/
noncomputable def theorem12TypeWeight (beta epsilon gamma : ℝ) : Fin 3 → ℝ
  | 0 => theorem12TypeAMass beta epsilon
  | 1 => theorem12TypeBMass beta epsilon gamma
  | 2 => 1 - theorem12TypeAMass beta epsilon - theorem12TypeBMass beta epsilon gamma

/-- The three utility vectors `(a,b,c)` printed in Appendix E.2. -/
def theorem12Utility (epsilon epsilonZero gamma : ℝ) : FiniteUtilityProfile (Fin 3) (Fin 3)
  | 0, 0 => 1 - gamma
  | 0, 1 => 1
  | 0, 2 => 0
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => epsilon
  | 2, 0 => 0
  | 2, 1 => 0
  | 2, 2 => epsilon + epsilonZero

/-- The diagonal `ε₀ = ε²` source population has unit-interval utilities for small `ε`. -/
theorem theorem12DiagonalUtility_unitInterval
    {epsilon gamma : ℝ} (hepsilon : 0 < epsilon) (hepsilon_lt_half : epsilon < (1 : ℝ) / 2)
    (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    UnitIntervalUtilityProfile (theorem12Utility epsilon (epsilon ^ 2) gamma) := by
  have hsquare_lt : epsilon ^ 2 < epsilon / 2 := by
    nlinarith [mul_lt_mul_of_pos_left hepsilon_lt_half hepsilon]
  have hsum_le_one : epsilon + epsilon ^ 2 ≤ 1 := by linarith
  intro user alternative
  fin_cases user
  · fin_cases alternative
    · change 0 ≤ 1 - gamma ∧ 1 - gamma ≤ 1
      constructor <;> linarith
    · norm_num [theorem12Utility]
    · norm_num [theorem12Utility]
  · fin_cases alternative
    · norm_num [theorem12Utility]
    · norm_num [theorem12Utility]
    · change 0 ≤ epsilon ∧ epsilon ≤ 1
      constructor <;> linarith
  · fin_cases alternative
    · norm_num [theorem12Utility]
    · norm_num [theorem12Utility]
    · change 0 ≤ epsilon + epsilon ^ 2 ∧ epsilon + epsilon ^ 2 ≤ 1
      constructor
      · nlinarith [sq_nonneg epsilon]
      · exact hsum_le_one

theorem theorem12TypeAMass_pos
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    0 < theorem12TypeAMass beta epsilon := by
  exact (theorem3TypeMasses_pos hbeta hepsilon).1

theorem theorem12_centeredSigmoid_pos {x : ℝ} (hx : 0 < x) :
    0 < Real.sigmoid x - (1 : ℝ) / 2 := by
  apply sub_pos.mpr
  calc
    (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
    _ < Real.sigmoid x := Real.sigmoid_lt hx

theorem theorem12TypeBMass_pos
    {beta epsilon gamma : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hgamma : 0 < gamma) :
    0 < theorem12TypeBMass beta epsilon gamma := by
  unfold theorem12TypeBMass
  apply div_pos
  · exact mul_pos (theorem12TypeAMass_pos hbeta hepsilon)
      (theorem12_centeredSigmoid_pos (mul_pos hbeta hgamma))
  · exact theorem12_centeredSigmoid_pos hbeta

theorem theorem12TypeAMass_lt_half
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) :
    theorem12TypeAMass beta epsilon < (1 : ℝ) / 2 := by
  have hbeta_eps : beta * epsilon < beta := by
    nlinarith [mul_pos hbeta hepsilon]
  have hcentered_lt :
      Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2 <
        Real.sigmoid beta - (1 : ℝ) / 2 := by
    exact sub_lt_sub_right (Real.sigmoid_lt hbeta_eps) _
  have hden : 0 < theorem3BalanceDenominator beta epsilon :=
    theorem3BalanceDenominator_pos hbeta hepsilon
  unfold theorem12TypeAMass theorem3SpecialTypeMass
  apply (div_lt_iff₀ hden).mpr
  unfold theorem3BalanceDenominator
  linarith

theorem theorem12TypeBMass_lt_typeAMass
    {beta epsilon gamma : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hgamma_lt_one : gamma < 1) :
    theorem12TypeBMass beta epsilon gamma < theorem12TypeAMass beta epsilon := by
  have hbeta_gamma : beta * gamma < beta := by
    nlinarith [mul_pos hbeta (sub_pos.mpr hgamma_lt_one)]
  have hnum_lt :
      Real.sigmoid (beta * gamma) - (1 : ℝ) / 2 <
        Real.sigmoid beta - (1 : ℝ) / 2 := by
    exact sub_lt_sub_right (Real.sigmoid_lt hbeta_gamma) _
  have hden_pos : 0 < Real.sigmoid beta - (1 : ℝ) / 2 :=
    theorem12_centeredSigmoid_pos hbeta
  have hratio_lt_one :
      (Real.sigmoid (beta * gamma) - (1 : ℝ) / 2) /
          (Real.sigmoid beta - (1 : ℝ) / 2) < 1 := by
    rw [div_lt_one hden_pos]
    exact hnum_lt
  unfold theorem12TypeBMass
  rw [mul_div_assoc]
  simpa using
    (mul_lt_mul_of_pos_left hratio_lt_one (theorem12TypeAMass_pos hbeta hepsilon))

theorem theorem12TypeCMass_pos
    {beta epsilon gamma : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma_lt_one : gamma < 1) :
    0 < theorem12TypeWeight beta epsilon gamma (2 : Fin 3) := by
  change 0 < 1 - theorem12TypeAMass beta epsilon - theorem12TypeBMass beta epsilon gamma
  have hA_lt_half := theorem12TypeAMass_lt_half hbeta hepsilon hepsilon_lt_one
  have hB_lt_A := theorem12TypeBMass_lt_typeAMass hbeta hepsilon hgamma_lt_one
  linarith

theorem theorem12TypeWeight_nonneg
    {beta epsilon gamma : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    ∀ type : Fin 3, 0 ≤ theorem12TypeWeight beta epsilon gamma type := by
  intro type
  fin_cases type
  · exact (theorem12TypeAMass_pos hbeta hepsilon).le
  · exact (theorem12TypeBMass_pos hbeta hepsilon hgamma).le
  · have hA_lt_half := theorem12TypeAMass_lt_half hbeta hepsilon hepsilon_lt_one
    have hB_lt_A := theorem12TypeBMass_lt_typeAMass
      hbeta hepsilon hgamma_lt_one
    change 0 ≤ 1 - theorem12TypeAMass beta epsilon - theorem12TypeBMass beta epsilon gamma
    linarith

theorem theorem12TypeWeight_sum_one (beta epsilon gamma : ℝ) :
    (∑ type : Fin 3, theorem12TypeWeight beta epsilon gamma type) = 1 := by
  simp [Fin.sum_univ_succ, theorem12TypeWeight]

/-- The normalized finite PMF of source user types. -/
noncomputable def theorem12Population
    (beta epsilon gamma : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    PMF (Fin 3) :=
  finiteWeightedPMF (theorem12TypeWeight beta epsilon gamma)
    (theorem12TypeWeight_nonneg hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
    (by
      have hsum := theorem12TypeWeight_sum_one beta epsilon gamma
      rw [hsum]
      norm_num)

@[simp] theorem theorem12Population_weight_toReal
    (beta epsilon gamma : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (type : Fin 3) :
    (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one
      type).toReal = theorem12TypeWeight beta epsilon gamma type := by
  unfold theorem12Population
  rw [finiteWeightedPMF_apply_toReal]
  rw [theorem12TypeWeight_sum_one]
  ring

/-- The source's exact balance `p(b ≻ c) = 1/2` when `ε₀ = 0`. -/
theorem theorem12_b_vs_c_unbiased
    {beta epsilon gamma : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    (populationBradleyTerryPreference
      (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
      (theorem12Utility epsilon 0 gamma) beta).prob PUnit.unit.{1} (1 : Fin 3) (2 : Fin 3) =
        (1 : ℝ) / 2 := by
  change pmfExp
      (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
      (fun user => Real.sigmoid
        (beta * (theorem12Utility epsilon 0 gamma user (1 : Fin 3) -
          theorem12Utility epsilon 0 gamma user (2 : Fin 3)))) = (1 : ℝ) / 2
  rw [show
    pmfExp
        (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
        (fun user => Real.sigmoid
          (beta * (theorem12Utility epsilon 0 gamma user (1 : Fin 3) -
            theorem12Utility epsilon 0 gamma user (2 : Fin 3)))) =
      theorem12TypeAMass beta epsilon * Real.sigmoid beta +
        (theorem12TypeBMass beta epsilon gamma +
          (1 - theorem12TypeAMass beta epsilon - theorem12TypeBMass beta epsilon gamma)) *
            Real.sigmoid (-(beta * epsilon)) by
      unfold pmfExp
      simp [Fin.sum_univ_succ, theorem12Population_weight_toReal, theorem12TypeWeight,
        theorem12Utility]
      ring]
  have hbalanced := theorem3_balanced_pairwise_probability hbeta hepsilon
  unfold theorem12TypeAMass
  rw [Real.sigmoid_neg] at hbalanced
  rw [Real.sigmoid_neg]
  have hsum := theorem3TypeMasses_sum_one hbeta hepsilon
  have hcoefficient :
      theorem12TypeBMass beta epsilon gamma +
          (1 - theorem3SpecialTypeMass beta epsilon - theorem12TypeBMass beta epsilon gamma) =
        theorem3OrdinaryTypeMass beta epsilon := by
    linarith
  rw [hcoefficient]
  exact hbalanced

/-- The source's other exact balance `p(a ≻ b) = 1/2`. -/
theorem theorem12_a_vs_b_unbiased
    {beta epsilon gamma : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    (populationBradleyTerryPreference
      (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
      (theorem12Utility epsilon 0 gamma) beta).prob PUnit.unit.{1} (0 : Fin 3) (1 : Fin 3) =
        (1 : ℝ) / 2 := by
  change pmfExp
      (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
      (fun user => Real.sigmoid
        (beta * (theorem12Utility epsilon 0 gamma user (0 : Fin 3) -
          theorem12Utility epsilon 0 gamma user (1 : Fin 3)))) = (1 : ℝ) / 2
  rw [show
    pmfExp
        (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
        (fun user => Real.sigmoid
          (beta * (theorem12Utility epsilon 0 gamma user (0 : Fin 3) -
            theorem12Utility epsilon 0 gamma user (1 : Fin 3)))) =
      theorem12TypeAMass beta epsilon * Real.sigmoid (-(beta * gamma)) +
        theorem12TypeBMass beta epsilon gamma * Real.sigmoid beta +
          (1 - theorem12TypeAMass beta epsilon - theorem12TypeBMass beta epsilon gamma) /
            2 by
      unfold pmfExp
      simp [Fin.sum_univ_succ, theorem12Population_weight_toReal, theorem12TypeWeight,
        theorem12Utility, Real.sigmoid_zero]
      ring]
  have hden_pos : 0 < Real.sigmoid beta - (1 : ℝ) / 2 :=
    theorem12_centeredSigmoid_pos hbeta
  have hrelation :
      theorem12TypeAMass beta epsilon *
          (Real.sigmoid (beta * gamma) - (1 : ℝ) / 2) =
        theorem12TypeBMass beta epsilon gamma *
          (Real.sigmoid beta - (1 : ℝ) / 2) := by
    unfold theorem12TypeBMass
    have htwice_ne : 2 * Real.sigmoid beta - 1 ≠ 0 := by linarith
    field_simp [hden_pos.ne', htwice_ne]
  rw [Real.sigmoid_neg]
  linarith

/-- With positive `ε₀`, the source population satisfies `p(c ≻ b) > 1/2`. -/
theorem theorem12_c_vs_b_gt_half_of_epsilonZero_pos
    {beta epsilon epsilonZero gamma : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hepsilonZero_pos : 0 < epsilonZero)
    (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    (1 : ℝ) / 2 <
      (populationBradleyTerryPreference
        (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
        (theorem12Utility epsilon epsilonZero gamma) beta).prob PUnit.unit.{1}
          (2 : Fin 3) (1 : Fin 3) := by
  let population := theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma
    hgamma_lt_one
  let preferenceZero := populationBradleyTerryPreference population
    (theorem12Utility epsilon 0 gamma) beta
  have hbase : preferenceZero.prob PUnit.unit.{1} (2 : Fin 3) (1 : Fin 3) = (1 : ℝ) / 2 := by
    have hforward := theorem12_b_vs_c_unbiased hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one
    have hcomplement := preferenceZero.complementary PUnit.unit.{1} (1 : Fin 3) (2 : Fin 3)
    simpa [preferenceZero, population] using (show
      (populationBradleyTerryPreference population (theorem12Utility epsilon 0 gamma) beta).prob
          PUnit.unit (2 : Fin 3) (1 : Fin 3) = (1 : ℝ) / 2 by linarith)
  have hcenter_pos : 0 < theorem12TypeWeight beta epsilon gamma (2 : Fin 3) :=
    theorem12TypeCMass_pos hbeta hepsilon hepsilon_lt_one hgamma_lt_one
  have hargument : beta * epsilon < beta * (epsilon + epsilonZero) := by
    nlinarith [mul_pos hbeta hepsilonZero_pos]
  have hsigmoid : Real.sigmoid (beta * epsilon) <
      Real.sigmoid (beta * (epsilon + epsilonZero)) := Real.sigmoid_lt hargument
  have hstrictTerm := mul_lt_mul_of_pos_left hsigmoid hcenter_pos
  change pmfExp population (fun user => Real.sigmoid
      (beta * (theorem12Utility epsilon epsilonZero gamma user (2 : Fin 3) -
        theorem12Utility epsilon epsilonZero gamma user (1 : Fin 3)))) > (1 : ℝ) / 2
  have hvalue :
      pmfExp population (fun user => Real.sigmoid
        (beta * (theorem12Utility epsilon epsilonZero gamma user (2 : Fin 3) -
          theorem12Utility epsilon epsilonZero gamma user (1 : Fin 3)))) =
        theorem12TypeAMass beta epsilon * Real.sigmoid (-beta) +
          theorem12TypeBMass beta epsilon gamma * Real.sigmoid (beta * epsilon) +
            theorem12TypeWeight beta epsilon gamma (2 : Fin 3) *
              Real.sigmoid (beta * (epsilon + epsilonZero)) := by
    unfold pmfExp
    simp [population, Fin.sum_univ_succ, theorem12Population_weight_toReal, theorem12TypeWeight,
      theorem12Utility]
    ring
  have hvalueZero :
      preferenceZero.prob PUnit.unit.{1} (2 : Fin 3) (1 : Fin 3) =
        theorem12TypeAMass beta epsilon * Real.sigmoid (-beta) +
          theorem12TypeBMass beta epsilon gamma * Real.sigmoid (beta * epsilon) +
            theorem12TypeWeight beta epsilon gamma (2 : Fin 3) *
              Real.sigmoid (beta * epsilon) := by
    change pmfExp population (fun user => Real.sigmoid
      (beta * (theorem12Utility epsilon 0 gamma user (2 : Fin 3) -
        theorem12Utility epsilon 0 gamma user (1 : Fin 3)))) = _
    unfold pmfExp
    simp [population, Fin.sum_univ_succ, theorem12Population_weight_toReal, theorem12TypeWeight,
      theorem12Utility]
    ring
  rw [hvalue]
  rw [hvalueZero] at hbase
  linarith

/-- The strictly positive population gap by which `c` defeats `b`. -/
noncomputable def theorem12CvsBGap
    (beta epsilon epsilonZero gamma : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) : ℝ :=
  (populationBradleyTerryPreference
    (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
    (theorem12Utility epsilon epsilonZero gamma) beta).prob PUnit.unit.{1}
      (2 : Fin 3) (1 : Fin 3) - (1 : ℝ) / 2

theorem theorem12CvsBGap_pos
    {beta epsilon epsilonZero gamma : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hepsilonZero_pos : 0 < epsilonZero)
    (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    0 < theorem12CvsBGap beta epsilon epsilonZero gamma hbeta hepsilon hepsilon_lt_one hgamma
      hgamma_lt_one := by
  unfold theorem12CvsBGap
  exact sub_pos.mpr (theorem12_c_vs_b_gt_half_of_epsilonZero_pos
    hbeta hepsilon hepsilon_lt_one hepsilonZero_pos hgamma hgamma_lt_one)

theorem theorem12CvsBGap_le_half
    (beta epsilon epsilonZero gamma : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    theorem12CvsBGap beta epsilon epsilonZero gamma hbeta hepsilon hepsilon_lt_one hgamma
      hgamma_lt_one ≤ (1 : ℝ) / 2 := by
  unfold theorem12CvsBGap
  have hle := (populationBradleyTerryPreference
    (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
    (theorem12Utility epsilon epsilonZero gamma) beta).le_one PUnit.unit.{1}
      (2 : Fin 3) (1 : Fin 3)
  linarith

/-- An explicit full-support Borda opponent distribution of the source's "small enough" form. -/
noncomputable def theorem12BordaSamplingWeight (gap : ℝ) : Fin 3 → ℝ
  | 0 => gap / 4
  | 1 => 1 - gap / 2
  | 2 => gap / 4

theorem theorem12BordaSamplingWeight_nonneg {gap : ℝ}
    (hgap : 0 ≤ gap) (hgap_le_half : gap ≤ (1 : ℝ) / 2) :
    ∀ alternative : Fin 3, 0 ≤ theorem12BordaSamplingWeight gap alternative := by
  intro alternative
  fin_cases alternative
  · exact div_nonneg hgap (by norm_num)
  · dsimp [theorem12BordaSamplingWeight]
    linarith
  · exact div_nonneg hgap (by norm_num)

theorem theorem12BordaSamplingWeight_sum_one (gap : ℝ) :
    (∑ alternative : Fin 3, theorem12BordaSamplingWeight gap alternative) = 1 := by
  simp [Fin.sum_univ_succ, theorem12BordaSamplingWeight]
  ring

/-- The concrete source sampling PMF used to force the Borda winner to be `c`. -/
noncomputable def theorem12BordaSampling (gap : ℝ)
    (hgap : 0 ≤ gap) (hgap_le_half : gap ≤ (1 : ℝ) / 2) : PMF (Fin 3) :=
  finiteWeightedPMF (theorem12BordaSamplingWeight gap)
    (theorem12BordaSamplingWeight_nonneg hgap hgap_le_half)
    (by
      rw [theorem12BordaSamplingWeight_sum_one]
      norm_num)

@[simp] theorem theorem12BordaSampling_toReal
    (gap : ℝ) (hgap : 0 ≤ gap) (hgap_le_half : gap ≤ (1 : ℝ) / 2)
    (alternative : Fin 3) :
    (theorem12BordaSampling gap hgap hgap_le_half alternative).toReal =
      theorem12BordaSamplingWeight gap alternative := by
  unfold theorem12BordaSampling
  rw [finiteWeightedPMF_apply_toReal]
  rw [theorem12BordaSamplingWeight_sum_one]
  ring

/-- The explicit Appendix-E.2 sampling PMF has full support when its score gap is positive. -/
theorem theorem12BordaSampling_toReal_pos
    {gap : ℝ} (hgap : 0 < gap) (hgap_le_half : gap ≤ (1 : ℝ) / 2)
    (alternative : Fin 3) :
    0 < (theorem12BordaSampling gap hgap.le hgap_le_half alternative).toReal := by
  rw [theorem12BordaSampling_toReal]
  fin_cases alternative
  · exact div_pos hgap (by norm_num)
  · dsimp [theorem12BordaSamplingWeight]
    linarith
  · exact div_pos hgap (by norm_num)

/-- Every valid pairwise preference assigns probability one half to self-comparison. -/
theorem pairwisePreference_self_eq_half
    {Alternative : Type*} (preference : AppliedModelingLib.Learning.HumanFeedback.PairwisePreference
      PUnit Alternative) (alternative : Alternative) :
    preference.prob PUnit.unit alternative alternative = (1 : ℝ) / 2 := by
  have hcomplement := preference.complementary PUnit.unit alternative alternative
  linarith

/-- The `a`--`b` balance is unaffected by the third coordinate `ε₀`. -/
theorem theorem12_a_vs_b_unbiased_of_epsilonZero
    {beta epsilon epsilonZero gamma : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    (populationBradleyTerryPreference
      (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
      (theorem12Utility epsilon epsilonZero gamma) beta).prob PUnit.unit.{1} (0 : Fin 3) (1 : Fin 3) =
        (1 : ℝ) / 2 := by
  change pmfExp
      (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
      (fun user => Real.sigmoid
        (beta * (theorem12Utility epsilon epsilonZero gamma user (0 : Fin 3) -
          theorem12Utility epsilon epsilonZero gamma user (1 : Fin 3)))) = (1 : ℝ) / 2
  simpa [theorem12Utility] using
    theorem12_a_vs_b_unbiased hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one

/--
The explicit full-support sampling distribution makes `c` the unique
population Borda maximizer.  This replaces Appendix E.2's existential
"small enough" sampling choice by a concrete source-faithful choice.
-/
theorem theorem12_c_is_strict_populationBordaWinner
    {beta epsilon epsilonZero gamma : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hepsilonZero_pos : 0 < epsilonZero)
    (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    let population := theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma
      hgamma_lt_one
    let preference := populationBradleyTerryPreference population
      (theorem12Utility epsilon epsilonZero gamma) beta
    let gap := theorem12CvsBGap beta epsilon epsilonZero gamma hbeta hepsilon hepsilon_lt_one
      hgamma hgamma_lt_one
    let sampling := theorem12BordaSampling gap
      (theorem12CvsBGap_pos (epsilonZero := epsilonZero) hbeta hepsilon hepsilon_lt_one
        hepsilonZero_pos hgamma hgamma_lt_one).le
      (theorem12CvsBGap_le_half beta epsilon epsilonZero gamma hbeta hepsilon hepsilon_lt_one
        hgamma hgamma_lt_one)
    pairwiseBordaScore sampling preference (0 : Fin 3) <
      pairwiseBordaScore sampling preference (2 : Fin 3) ∧
      pairwiseBordaScore sampling preference (1 : Fin 3) <
        pairwiseBordaScore sampling preference (2 : Fin 3) := by
  dsimp
  let population := theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma
    hgamma_lt_one
  let preference := populationBradleyTerryPreference population
    (theorem12Utility epsilon epsilonZero gamma) beta
  let gap := theorem12CvsBGap beta epsilon epsilonZero gamma hbeta hepsilon hepsilon_lt_one
    hgamma hgamma_lt_one
  have hgap_pos : 0 < gap := by
    exact theorem12CvsBGap_pos (epsilonZero := epsilonZero)
      hbeta hepsilon hepsilon_lt_one hepsilonZero_pos hgamma hgamma_lt_one
  have hgap_le : gap ≤ (1 : ℝ) / 2 := by
    exact theorem12CvsBGap_le_half beta epsilon epsilonZero gamma hbeta hepsilon hepsilon_lt_one
      hgamma hgamma_lt_one
  let sampling := theorem12BordaSampling gap hgap_pos.le hgap_le
  have hcb : preference.prob PUnit.unit.{1} (2 : Fin 3) (1 : Fin 3) =
      (1 : ℝ) / 2 + gap := by
    unfold gap theorem12CvsBGap
    ring
  have hbc : preference.prob PUnit.unit.{1} (1 : Fin 3) (2 : Fin 3) =
      (1 : ℝ) / 2 - gap := by
    have hcomplement := preference.complementary PUnit.unit.{1} (1 : Fin 3) (2 : Fin 3)
    linarith
  have hab : preference.prob PUnit.unit.{1} (0 : Fin 3) (1 : Fin 3) = (1 : ℝ) / 2 := by
    exact theorem12_a_vs_b_unbiased_of_epsilonZero
      hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one
  have hba : preference.prob PUnit.unit.{1} (1 : Fin 3) (0 : Fin 3) = (1 : ℝ) / 2 := by
    have hcomplement := preference.complementary PUnit.unit.{1} (0 : Fin 3) (1 : Fin 3)
    linarith
  have hselfA := pairwisePreference_self_eq_half preference (0 : Fin 3)
  have hselfB := pairwisePreference_self_eq_half preference (1 : Fin 3)
  have hselfC := pairwisePreference_self_eq_half preference (2 : Fin 3)
  have hca_nonneg : 0 ≤ preference.prob PUnit.unit.{1} (2 : Fin 3) (0 : Fin 3) :=
    preference.nonneg PUnit.unit.{1} (2 : Fin 3) (0 : Fin 3)
  have hac : preference.prob PUnit.unit.{1} (0 : Fin 3) (2 : Fin 3) =
      1 - preference.prob PUnit.unit.{1} (2 : Fin 3) (0 : Fin 3) := by
    have hcomplement := preference.complementary PUnit.unit.{1} (0 : Fin 3) (2 : Fin 3)
    linarith
  have hscoreA : pairwiseBordaScore sampling preference (0 : Fin 3) =
      gap / 4 * ((1 : ℝ) / 2) +
        (1 - gap / 2) * ((1 : ℝ) / 2) +
          gap / 4 * preference.prob PUnit.unit.{1} (0 : Fin 3) (2 : Fin 3) := by
    unfold pairwiseBordaScore pmfExp
    simp [sampling, theorem12BordaSampling_toReal, Fin.sum_univ_succ,
      theorem12BordaSamplingWeight, hselfA, hab]
    ring
  have hscoreB : pairwiseBordaScore sampling preference (1 : Fin 3) =
      gap / 4 * ((1 : ℝ) / 2) +
        (1 - gap / 2) * ((1 : ℝ) / 2) +
          gap / 4 * ((1 : ℝ) / 2 - gap) := by
    unfold pairwiseBordaScore pmfExp
    simp [sampling, theorem12BordaSampling_toReal, Fin.sum_univ_succ,
      theorem12BordaSamplingWeight, hselfB, hba, hbc]
    ring
  have hscoreC : pairwiseBordaScore sampling preference (2 : Fin 3) =
      gap / 4 * preference.prob PUnit.unit.{1} (2 : Fin 3) (0 : Fin 3) +
        (1 - gap / 2) * ((1 : ℝ) / 2 + gap) +
          gap / 4 * ((1 : ℝ) / 2) := by
    unfold pairwiseBordaScore pmfExp
    simp [sampling, theorem12BordaSampling_toReal, Fin.sum_univ_succ,
      theorem12BordaSamplingWeight, hselfC, hcb]
    ring
  change pairwiseBordaScore sampling preference (0 : Fin 3) <
      pairwiseBordaScore sampling preference (2 : Fin 3) ∧
      pairwiseBordaScore sampling preference (1 : Fin 3) <
        pairwiseBordaScore sampling preference (2 : Fin 3)
  rw [hscoreA, hscoreB, hscoreC, hac]
  constructor <;> nlinarith [sq_nonneg gap]

/-- Average welfare of `a` in the literal three-type Appendix-E.2 population. -/
theorem theorem12_a_averageUtility
    (beta epsilon epsilonZero gamma : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    populationAverageUtility
      (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
      (theorem12Utility epsilon epsilonZero gamma) (0 : Fin 3) =
        theorem12TypeAMass beta epsilon * (1 - gamma) + theorem12TypeBMass beta epsilon gamma := by
  unfold populationAverageUtility pmfExp
  simp [Fin.sum_univ_succ, theorem12Population_weight_toReal, theorem12TypeWeight,
    theorem12Utility]

/-- Average welfare of `c` in the literal three-type Appendix-E.2 population. -/
theorem theorem12_c_averageUtility
    (beta epsilon epsilonZero gamma : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    populationAverageUtility
      (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
      (theorem12Utility epsilon epsilonZero gamma) (2 : Fin 3) =
        theorem12TypeBMass beta epsilon gamma * epsilon +
          (1 - theorem12TypeAMass beta epsilon - theorem12TypeBMass beta epsilon gamma) *
            (epsilon + epsilonZero) := by
  unfold populationAverageUtility pmfExp
  simp [Fin.sum_univ_succ, theorem12Population_weight_toReal, theorem12TypeWeight,
    theorem12Utility]

/--
The paper's Eq. (9) welfare ratio after the strict Borda-selection result,
written with its literal type weights and utilities.
-/
theorem theorem12_bordaSelectedC_welfareRatio
    (beta epsilon epsilonZero gamma : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_lt_one : epsilon < 1) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    populationAverageUtility
        (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
        (theorem12Utility epsilon epsilonZero gamma) (0 : Fin 3) /
      populationAverageUtility
        (theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one hgamma hgamma_lt_one)
        (theorem12Utility epsilon epsilonZero gamma) (2 : Fin 3) =
      (theorem12TypeAMass beta epsilon * (1 - gamma) + theorem12TypeBMass beta epsilon gamma) /
        (theorem12TypeBMass beta epsilon gamma * epsilon +
          (1 - theorem12TypeAMass beta epsilon - theorem12TypeBMass beta epsilon gamma) *
            (epsilon + epsilonZero)) := by
  rw [theorem12_a_averageUtility, theorem12_c_averageUtility]

/-- The first type mass has the source's first-order right-hand limit. -/
theorem theorem12_typeAMass_div_epsilon_limit
    {beta : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun epsilon : ℝ => theorem12TypeAMass beta epsilon / epsilon)
      (𝓝[>] 0)
      (𝓝 ((beta / 4) / (Real.sigmoid beta - (1 : ℝ) / 2))) := by
  let centered : ℝ → ℝ := fun epsilon => Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2
  let B : ℝ := Real.sigmoid beta - (1 : ℝ) / 2
  have hepsilon : Filter.Tendsto (fun epsilon : ℝ => epsilon) (𝓝[>] 0) (𝓝 0) := by
    exact continuousAt_id.tendsto.mono_left inf_le_left
  have hargument : Filter.Tendsto (fun epsilon : ℝ => beta * epsilon) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hepsilon)
  have hcentered : Filter.Tendsto centered (𝓝[>] 0) (𝓝 0) := by
    have hsigmoid := (continuous_sigmoid.continuousAt.tendsto).comp hargument
    simpa [centered, Real.sigmoid_zero] using hsigmoid.sub
      (tendsto_const_nhds (x := (1 : ℝ) / 2))
  have hdenominator : Filter.Tendsto
      (fun epsilon : ℝ => theorem3BalanceDenominator beta epsilon)
      (𝓝[>] 0) (𝓝 B) := by
    have hsum : Filter.Tendsto (fun epsilon : ℝ => centered epsilon + B)
        (𝓝[>] 0) (𝓝 B) := by
      simpa using hcentered.add (tendsto_const_nhds (x := B))
    refine hsum.congr' ?_
    filter_upwards with epsilon
    dsimp [centered, B, theorem3BalanceDenominator]
    ring
  have hB_ne : B ≠ 0 := by
    exact (theorem12_centeredSigmoid_pos hbeta).ne'
  have hquotient :=
    (theorem3_sigmoid_scaled_centered_slope_limit beta).div hdenominator hB_ne
  refine hquotient.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon_pos
  change 0 < epsilon at hepsilon_pos
  unfold theorem12TypeAMass theorem3SpecialTypeMass
  change
      ((Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) / epsilon) /
        theorem3BalanceDenominator beta epsilon =
      ((Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) /
        theorem3BalanceDenominator beta epsilon) / epsilon
  field_simp [hepsilon_pos.ne', theorem3BalanceDenominator_ne hbeta hepsilon_pos]

/-- The second type mass has the corresponding first-order right-hand limit. -/
theorem theorem12_typeBMass_div_epsilon_limit
    {beta gamma : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun epsilon : ℝ => theorem12TypeBMass beta epsilon gamma / epsilon)
      (𝓝[>] 0)
      (𝓝 (((beta / 4) / (Real.sigmoid beta - (1 : ℝ) / 2)) *
        ((Real.sigmoid (beta * gamma) - (1 : ℝ) / 2) /
          (Real.sigmoid beta - (1 : ℝ) / 2)))) := by
  let B : ℝ := Real.sigmoid beta - (1 : ℝ) / 2
  let G : ℝ := Real.sigmoid (beta * gamma) - (1 : ℝ) / 2
  have hscaled := theorem12_typeAMass_div_epsilon_limit hbeta
  have hconstant : Filter.Tendsto (fun _ : ℝ => G / B) (𝓝[>] 0) (𝓝 (G / B)) :=
    tendsto_const_nhds
  have hproduct := hscaled.mul hconstant
  refine hproduct.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon_pos
  change 0 < epsilon at hepsilon_pos
  unfold theorem12TypeBMass
  change
    (theorem12TypeAMass beta epsilon / epsilon) * (G / B) =
    (theorem12TypeAMass beta epsilon *
        (Real.sigmoid (beta * gamma) - (1 : ℝ) / 2) /
      (Real.sigmoid beta - (1 : ℝ) / 2)) / epsilon
  dsimp [B, G]
  field_simp [hepsilon_pos.ne', (theorem12_centeredSigmoid_pos hbeta).ne']

/-- Both vanishing source type masses converge to zero as `ε → 0⁺`. -/
theorem theorem12_typeAMass_tendsto_zero
    {beta : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto (fun epsilon : ℝ => theorem12TypeAMass beta epsilon) (𝓝[>] 0) (𝓝 0) := by
  have hscaled := theorem12_typeAMass_div_epsilon_limit hbeta
  have hepsilon : Filter.Tendsto (fun epsilon : ℝ => epsilon) (𝓝[>] 0) (𝓝 0) := by
    exact continuousAt_id.tendsto.mono_left inf_le_left
  have hproduct := hscaled.mul hepsilon
  simpa only [mul_zero] using hproduct.congr' (by
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon_pos
    change 0 < epsilon at hepsilon_pos
    field_simp [hepsilon_pos.ne'])

theorem theorem12_typeBMass_tendsto_zero
    {beta gamma : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto (fun epsilon : ℝ => theorem12TypeBMass beta epsilon gamma) (𝓝[>] 0) (𝓝 0) := by
  have hscaled := theorem12_typeBMass_div_epsilon_limit (gamma := gamma) hbeta
  have hepsilon : Filter.Tendsto (fun epsilon : ℝ => epsilon) (𝓝[>] 0) (𝓝 0) := by
    exact continuousAt_id.tendsto.mono_left inf_le_left
  have hproduct := hscaled.mul hepsilon
  simpa only [mul_zero] using hproduct.congr' (by
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon_pos
    change 0 < epsilon at hepsilon_pos
    field_simp [hepsilon_pos.ne'])

/-- Sigmoid is strictly concave between the two endpoints used in Appendix E.2. -/
theorem theorem12_strictConcaveSigmoidOn_Icc_zero
    (beta : ℝ) :
    StrictConcaveOn ℝ (Set.Icc 0 beta) Real.sigmoid := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) continuous_sigmoid.continuousOn
  intro z hz
  rw [interior_Icc] at hz
  rw [deriv2_sigmoid]
  have hpositive_factor : 0 < Real.sigmoid z * (1 - Real.sigmoid z) := by
    exact mul_pos (Real.sigmoid_pos _) (sub_pos.mpr (Real.sigmoid_lt_one _))
  have hgreater_than_half : (1 : ℝ) / 2 < Real.sigmoid z := by
    calc
      (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
      _ < Real.sigmoid z := Real.sigmoid_lt hz.1
  have hnegative_factor : 1 - 2 * Real.sigmoid z < 0 := by
    linarith
  exact mul_neg_of_pos_of_neg hpositive_factor hnegative_factor

/--
For an interior `γ`, the Appendix-E.2 sigmoid numerator lies strictly above
the chord joining `0` to `β`.  This is the strict-concavity step in the
source comparison with the generic lower-bound coefficient.
-/
theorem theorem12_strict_sigmoid_chord
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    gamma * (Real.sigmoid beta - (1 : ℝ) / 2) <
      Real.sigmoid (beta * gamma) - (1 : ℝ) / 2 := by
  have hconcave := theorem12_strictConcaveSigmoidOn_Icc_zero beta
  have hbeta_mem : beta ∈ Set.Icc (0 : ℝ) beta := ⟨hbeta.le, le_rfl⟩
  have hzero_mem : (0 : ℝ) ∈ Set.Icc 0 beta := ⟨le_rfl, hbeta.le⟩
  have hcomplement : 0 < 1 - gamma := sub_pos.mpr hgamma_lt_one
  have hstrict := hconcave.2 hbeta_mem hzero_mem (ne_of_gt hbeta) hgamma hcomplement (by ring)
  have hargument : gamma • beta + (1 - gamma) • (0 : ℝ) = beta * gamma := by
    simp only [smul_eq_mul, mul_zero, add_zero]
    ring
  rw [hargument, Real.sigmoid_zero] at hstrict
  norm_num at hstrict ⊢
  linarith

/-- The limiting coefficient in Eq. (10) of Appendix E.2. -/
noncomputable def theorem12Eq10Coefficient (beta gamma : ℝ) : ℝ :=
  (beta / 4) / (Real.sigmoid beta - (1 : ℝ) / 2) *
    (1 - gamma +
      (Real.sigmoid (beta * gamma) - (1 : ℝ) / 2) /
        (Real.sigmoid beta - (1 : ℝ) / 2))

/--
At every interior `γ`, the Appendix-E.2 Eq. (10) coefficient is strictly
larger than the generic Theorem-3 coefficient.  The strict inequality is
exactly the source's strict-concavity comparison.
-/
theorem theorem12_eq10Coefficient_gt_theorem3Coefficient
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1) :
    beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) <
      theorem12Eq10Coefficient beta gamma := by
  let B : ℝ := Real.sigmoid beta - (1 : ℝ) / 2
  let G : ℝ := Real.sigmoid (beta * gamma) - (1 : ℝ) / 2
  let L : ℝ := (beta / 4) / B
  have hB_pos : 0 < B := theorem12_centeredSigmoid_pos hbeta
  have hL_pos : 0 < L := by
    dsimp [L]
    exact div_pos (by positivity) hB_pos
  have hchord : gamma * B < G := by
    simpa [B, G] using theorem12_strict_sigmoid_chord hbeta hgamma hgamma_lt_one
  have hratio : gamma < G / B := (lt_div_iff₀ hB_pos).mpr (by
    simpa [mul_comm] using hchord)
  have hfactor : 1 < 1 - gamma + G / B := by linarith
  have hstrict : L < L * (1 - gamma + G / B) := by
    simpa using (mul_lt_mul_of_pos_left hfactor hL_pos)
  calc
    beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) = L := by
      dsimp [L, B]
      symm
      exact theorem3_eq11_limit_coefficient hbeta
    _ < L * (1 - gamma + G / B) := hstrict
    _ = theorem12Eq10Coefficient beta gamma := by
      rfl

/-- The parameter choice `γ = log (β + 1) / β` made at the end of Appendix E.2. -/
noncomputable def theorem12LogChoice (beta : ℝ) : ℝ := Real.log (beta + 1) / beta

/-- The source's logarithmic parameter choice tends to zero at large `β`. -/
theorem theorem12_logChoice_tendsto_zero :
    Filter.Tendsto theorem12LogChoice Filter.atTop (𝓝 0) := by
  have hshift : Filter.Tendsto (fun beta : ℝ => beta + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 Filter.tendsto_id
  have hsmall : Filter.Tendsto (fun beta : ℝ => Real.log (beta + 1) / (beta + 1))
      Filter.atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hshift
  have hinv : Filter.Tendsto (fun beta : ℝ => beta⁻¹) Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hfactor : Filter.Tendsto (fun beta : ℝ => (beta + 1) / beta)
      Filter.atTop (𝓝 1) := by
    have hsum : Filter.Tendsto (fun beta : ℝ => 1 + beta⁻¹) Filter.atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hinv
    refine hsum.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with beta hbeta
    field_simp [hbeta.ne']
  have hproduct : Filter.Tendsto
      (fun beta : ℝ => (Real.log (beta + 1) / (beta + 1)) * ((beta + 1) / beta))
      Filter.atTop (𝓝 0) := by
    simpa using hsmall.mul hfactor
  refine hproduct.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with beta hbeta
  unfold theorem12LogChoice
  field_simp [hbeta.ne', (by linarith : beta + 1 ≠ 0)]

/-- The source's logarithmic parameter choice is eventually an interior `γ`. -/
theorem theorem12_logChoice_eventually_interior :
    ∀ᶠ beta : ℝ in Filter.atTop, 0 < theorem12LogChoice beta ∧ theorem12LogChoice beta < 1 := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with beta hbeta
  constructor
  · unfold theorem12LogChoice
    exact div_pos (Real.log_pos (by linarith)) hbeta
  · unfold theorem12LogChoice
    apply (div_lt_iff₀ hbeta).mpr
    simpa using Real.log_lt_sub_one_of_pos (by linarith : 0 < beta + 1) (by linarith : beta + 1 ≠ 1)

/-- The scaled argument of the source's logarithmic parameter choice diverges to `+∞`. -/
theorem theorem12_scaled_logChoice_tendsto_atTop :
    Filter.Tendsto (fun beta : ℝ => beta * theorem12LogChoice beta)
      Filter.atTop Filter.atTop := by
  have hshift : Filter.Tendsto (fun beta : ℝ => beta + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 Filter.tendsto_id
  have hlog : Filter.Tendsto (fun beta : ℝ => Real.log (beta + 1))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hshift
  refine hlog.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with beta hbeta
  unfold theorem12LogChoice
  field_simp [hbeta.ne']

/--
With the logarithmic `γ` from Appendix E.2, the Eq. (10) coefficient is
asymptotic to `β`.  This is the source's `(1 - o(1)) β` conclusion in its
equivalent ratio-limit form.
-/
theorem theorem12_eq10Coefficient_logChoice_ratio_limit :
    Filter.Tendsto
      (fun beta : ℝ => theorem12Eq10Coefficient beta (theorem12LogChoice beta) / beta)
      Filter.atTop (𝓝 1) := by
  have hgamma := theorem12_logChoice_tendsto_zero
  have hargument := theorem12_scaled_logChoice_tendsto_atTop
  have hbase : Filter.Tendsto
      (fun beta : ℝ => Real.sigmoid beta - (1 : ℝ) / 2)
      Filter.atTop (𝓝 ((1 : ℝ) / 2)) := by
    convert Real.tendsto_sigmoid_atTop.sub (tendsto_const_nhds (x := (1 : ℝ) / 2)) using 1
    all_goals norm_num
  have hscaled : Filter.Tendsto
      (fun beta : ℝ => Real.sigmoid (beta * theorem12LogChoice beta) - (1 : ℝ) / 2)
      Filter.atTop (𝓝 ((1 : ℝ) / 2)) := by
    convert (Real.tendsto_sigmoid_atTop.comp hargument).sub
      (tendsto_const_nhds (x := (1 : ℝ) / 2)) using 1
    all_goals norm_num
  have hratio := hscaled.div hbase (by norm_num : ((1 : ℝ) / 2) ≠ 0)
  have hfactor := (tendsto_const_nhds (x := (1 : ℝ))).sub hgamma |>.add hratio
  have hprefactor := (tendsto_const_nhds (x := (1 : ℝ) / 4)).div hbase
    (by norm_num : ((1 : ℝ) / 2) ≠ 0)
  have hproduct := hprefactor.mul hfactor
  norm_num at hproduct
  refine hproduct.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with beta hbeta
  unfold theorem12Eq10Coefficient theorem12LogChoice
  field_simp [hbeta.ne']

/--
The explicit Eq. (9) welfare ratio with `ε₀ = ε²` converges to the published
Eq. (10) coefficient as `ε → 0⁺`.
-/
theorem theorem12_eq9_diagonal_ratio_limit
    {beta gamma : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        (theorem12TypeAMass beta epsilon * (1 - gamma) + theorem12TypeBMass beta epsilon gamma) /
          (theorem12TypeBMass beta epsilon gamma * epsilon +
            (1 - theorem12TypeAMass beta epsilon - theorem12TypeBMass beta epsilon gamma) *
              (epsilon + epsilon ^ 2)))
      (𝓝[>] 0) (𝓝 (theorem12Eq10Coefficient beta gamma)) := by
  let B : ℝ := Real.sigmoid beta - (1 : ℝ) / 2
  let G : ℝ := Real.sigmoid (beta * gamma) - (1 : ℝ) / 2
  let L : ℝ := (beta / 4) / B
  let numeratorScaled : ℝ → ℝ := fun epsilon =>
    (theorem12TypeAMass beta epsilon / epsilon) * (1 - gamma) +
      theorem12TypeBMass beta epsilon gamma / epsilon
  let denominatorScaled : ℝ → ℝ := fun epsilon =>
    theorem12TypeBMass beta epsilon gamma +
      (1 - theorem12TypeAMass beta epsilon - theorem12TypeBMass beta epsilon gamma) *
        (1 + epsilon)
  have hA_scaled := theorem12_typeAMass_div_epsilon_limit hbeta
  have hB_scaled := theorem12_typeBMass_div_epsilon_limit (gamma := gamma) hbeta
  have hA_zero := theorem12_typeAMass_tendsto_zero hbeta
  have hB_zero := theorem12_typeBMass_tendsto_zero (gamma := gamma) hbeta
  have hepsilon : Filter.Tendsto (fun epsilon : ℝ => epsilon) (𝓝[>] 0) (𝓝 0) := by
    exact continuousAt_id.tendsto.mono_left inf_le_left
  have hnumerator : Filter.Tendsto numeratorScaled (𝓝[>] 0)
      (𝓝 (L * (1 - gamma) + L * (G / B))) := by
    have hfirst := hA_scaled.mul (tendsto_const_nhds (x := 1 - gamma))
    have hsecond := hB_scaled
    refine hfirst.add hsecond |>.congr' ?_
    filter_upwards with epsilon
    dsimp [numeratorScaled, L, G, B]
  have hdenominator : Filter.Tendsto denominatorScaled (𝓝[>] 0) (𝓝 1) := by
    have hweight : Filter.Tendsto
        (fun epsilon : ℝ => 1 - theorem12TypeAMass beta epsilon -
          theorem12TypeBMass beta epsilon gamma)
        (𝓝[>] 0) (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hA_zero).sub hB_zero
    have hfactor : Filter.Tendsto (fun epsilon : ℝ => 1 + epsilon) (𝓝[>] 0) (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hepsilon
    simpa [denominatorScaled] using hB_zero.add (hweight.mul hfactor)
  have hquotient := hnumerator.div hdenominator (by norm_num : (1 : ℝ) ≠ 0)
  have hlimit_eq : (L * (1 - gamma) + L * (G / B)) / 1 =
      theorem12Eq10Coefficient beta gamma := by
    dsimp [L, G, B, theorem12Eq10Coefficient]
    ring
  rw [hlimit_eq] at hquotient
  refine hquotient.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon_pos
  change 0 < epsilon at hepsilon_pos
  dsimp [numeratorScaled, denominatorScaled]
  change
    ((theorem12TypeAMass beta epsilon / epsilon) * (1 - gamma) +
        theorem12TypeBMass beta epsilon gamma / epsilon) /
      (theorem12TypeBMass beta epsilon gamma +
        (1 - theorem12TypeAMass beta epsilon - theorem12TypeBMass beta epsilon gamma) *
          (1 + epsilon)) =
      (theorem12TypeAMass beta epsilon * (1 - gamma) + theorem12TypeBMass beta epsilon gamma) /
        (theorem12TypeBMass beta epsilon gamma * epsilon +
          (1 - theorem12TypeAMass beta epsilon - theorem12TypeBMass beta epsilon gamma) *
            (epsilon + epsilon ^ 2))
  field_simp [hepsilon_pos.ne']

/--
Three-alternative, population-Borda form of Appendix-E.2's lower-bound
construction.  Every strict sub-bound below Eq. (10) is attained by a
unit-interval instance with `ε₀ = ε²`, where `c` is the unique Borda winner
and the displayed welfare ratio exceeds that sub-bound.
-/
theorem theorem12_threeAlternative_populationBorda_lower_bound
    {beta gamma q : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (hq : q < theorem12Eq10Coefficient beta gamma) :
    ∃ (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_lt_half : epsilon < (1 : ℝ) / 2)
      (sampling : PMF (Fin 3)),
      epsilon ^ 2 < 1 - epsilon ∧
        UnitIntervalUtilityProfile (theorem12Utility epsilon (epsilon ^ 2) gamma) ∧
        (∀ alternative : Fin 3, 0 < (sampling alternative).toReal) ∧
        pairwiseBordaScore sampling
            (populationBradleyTerryPreference
              (theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
                hgamma hgamma_lt_one)
              (theorem12Utility epsilon (epsilon ^ 2) gamma) beta)
            (0 : Fin 3) <
          pairwiseBordaScore sampling
            (populationBradleyTerryPreference
              (theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
                hgamma hgamma_lt_one)
              (theorem12Utility epsilon (epsilon ^ 2) gamma) beta)
            (2 : Fin 3) ∧
        pairwiseBordaScore sampling
            (populationBradleyTerryPreference
              (theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
                hgamma hgamma_lt_one)
              (theorem12Utility epsilon (epsilon ^ 2) gamma) beta)
            (1 : Fin 3) <
          pairwiseBordaScore sampling
            (populationBradleyTerryPreference
              (theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
                hgamma hgamma_lt_one)
              (theorem12Utility epsilon (epsilon ^ 2) gamma) beta)
            (2 : Fin 3) ∧
        q <
          populationAverageUtility
            (theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
              hgamma hgamma_lt_one)
            (theorem12Utility epsilon (epsilon ^ 2) gamma) (0 : Fin 3) /
          populationAverageUtility
            (theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
              hgamma hgamma_lt_one)
            (theorem12Utility epsilon (epsilon ^ 2) gamma) (2 : Fin 3) := by
  have hlimit := theorem12_eq9_diagonal_ratio_limit (gamma := gamma) hbeta
  have hratio_eventually : ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      q <
        (theorem12TypeAMass beta epsilon * (1 - gamma) + theorem12TypeBMass beta epsilon gamma) /
          (theorem12TypeBMass beta epsilon gamma * epsilon +
            (1 - theorem12TypeAMass beta epsilon - theorem12TypeBMass beta epsilon gamma) *
              (epsilon + epsilon ^ 2)) :=
    hlimit.eventually_const_lt hq
  have hsmall_eventually : ∀ᶠ epsilon : ℝ in 𝓝[>] 0,
      epsilon ∈ Set.Ioo 0 ((1 : ℝ) / 2) := by
    exact Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨epsilon, hratio, hepsilon_mem⟩ :=
    (hratio_eventually.and hsmall_eventually).exists
  have hepsilon : 0 < epsilon := hepsilon_mem.1
  have hepsilon_lt_half : epsilon < (1 : ℝ) / 2 := hepsilon_mem.2
  have hepsilon_lt_one : epsilon < 1 := by linarith
  have hepsilonZero_pos : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hepsilonZero_lt : epsilon ^ 2 < 1 - epsilon := by
    nlinarith [mul_lt_mul_of_pos_left hepsilon_lt_half hepsilon]
  have hunit := theorem12DiagonalUtility_unitInterval hepsilon hepsilon_lt_half hgamma hgamma_lt_one
  let gap := theorem12CvsBGap beta epsilon (epsilon ^ 2) gamma hbeta hepsilon hepsilon_lt_one
    hgamma hgamma_lt_one
  have hgap_pos : 0 < gap := by
    exact theorem12CvsBGap_pos (epsilonZero := epsilon ^ 2) hbeta hepsilon hepsilon_lt_one
      hepsilonZero_pos hgamma hgamma_lt_one
  have hgap_le_half : gap ≤ (1 : ℝ) / 2 := by
    exact theorem12CvsBGap_le_half beta epsilon (epsilon ^ 2) gamma hbeta hepsilon hepsilon_lt_one
      hgamma hgamma_lt_one
  let sampling := theorem12BordaSampling gap hgap_pos.le hgap_le_half
  refine ⟨epsilon, hepsilon, hepsilon_lt_half, sampling, hepsilonZero_lt, hunit, ?_, ?_, ?_, ?_⟩
  · intro alternative
    simpa [sampling, gap] using theorem12BordaSampling_toReal_pos hgap_pos hgap_le_half alternative
  · simpa [sampling, gap] using
      (theorem12_c_is_strict_populationBordaWinner (epsilonZero := epsilon ^ 2)
        hbeta hepsilon hepsilon_lt_one hepsilonZero_pos hgamma hgamma_lt_one).1
  · simpa [sampling, gap] using
      (theorem12_c_is_strict_populationBordaWinner (epsilonZero := epsilon ^ 2)
        hbeta hepsilon hepsilon_lt_one hepsilonZero_pos hgamma hgamma_lt_one).2
  · rw [theorem12_bordaSelectedC_welfareRatio beta epsilon (epsilon ^ 2) gamma hbeta hepsilon
      hepsilon_lt_one hgamma hgamma_lt_one]
    exact hratio

universe u v w

/--
The utility profile induced by splitting alternatives along a collapse map.
Every clone has exactly the utility of the alternative to which it collapses.
-/
def theorem12SplitUtility {User : Type u} {OldAlternative : Type v} {NewAlternative : Type w}
    (utility : FiniteUtilityProfile User OldAlternative) (collapse : NewAlternative → OldAlternative) :
    FiniteUtilityProfile User NewAlternative := fun user alternative => utility user (collapse alternative)

/-- Population Bradley--Terry probabilities are invariant under cloned alternatives. -/
theorem theorem12_split_populationPreference_apply
    {User : Type u} {OldAlternative : Type v} {NewAlternative : Type w}
    [Fintype User] [DecidableEq User]
    (population : PMF User) (utility : FiniteUtilityProfile User OldAlternative)
    (collapse : NewAlternative → OldAlternative) (beta : ℝ) (first second : NewAlternative) :
    (populationBradleyTerryPreference.{u, w, 0}
      population (theorem12SplitUtility utility collapse) beta).prob
        PUnit.unit.{1} first second =
      (populationBradleyTerryPreference.{u, v, 0} population utility beta).prob PUnit.unit.{1}
        (collapse first) (collapse second) := by
  rfl

/--
If a split sampling law pushes forward to the original law, Borda gives every
clone the score of its source alternative.  This is the invariant used by the
candidate-splitting step of Appendix E.2.
-/
theorem theorem12_split_pairwiseBordaScore
    {User : Type u} {OldAlternative : Type v} {NewAlternative : Type w}
    [Fintype User] [DecidableEq User]
    [Fintype OldAlternative] [DecidableEq OldAlternative]
    [Fintype NewAlternative] [DecidableEq NewAlternative]
    (population : PMF User) (utility : FiniteUtilityProfile User OldAlternative)
    (beta : ℝ) (collapse : NewAlternative → OldAlternative)
    (oldSampling : PMF OldAlternative) (newSampling : PMF NewAlternative)
    (hpushforward : newSampling.map collapse = oldSampling) (alternative : NewAlternative) :
    pairwiseBordaScore.{w, 0} newSampling
        (populationBradleyTerryPreference.{u, w, 0}
          population (theorem12SplitUtility utility collapse) beta)
        alternative =
      pairwiseBordaScore.{v, 0} oldSampling
        (populationBradleyTerryPreference.{u, v, 0} population utility beta)
        (collapse alternative) := by
  unfold pairwiseBordaScore
  calc
    pmfExp newSampling (fun opponent =>
        (populationBradleyTerryPreference.{u, w, 0}
          population (theorem12SplitUtility utility collapse) beta).prob
          PUnit.unit.{1} alternative opponent) =
      pmfExp newSampling (fun opponent =>
        (populationBradleyTerryPreference.{u, v, 0} population utility beta).prob PUnit.unit.{1}
          (collapse alternative) (collapse opponent)) := by
        apply pmfExp_congr
        intro opponent
        exact theorem12_split_populationPreference_apply population utility collapse beta alternative opponent
    _ = pmfExp (newSampling.map collapse) (fun opponent =>
        (populationBradleyTerryPreference.{u, v, 0} population utility beta).prob PUnit.unit.{1}
          (collapse alternative) opponent) := by
        symm
        exact pmfExp_map newSampling collapse _
    _ = pairwiseBordaScore.{v, 0} oldSampling
        (populationBradleyTerryPreference.{u, v, 0} population utility beta) (collapse alternative) := by
        rw [hpushforward]
        rfl

/-- Collapsing the original alternative and its new clones back to one source alternative. -/
def theorem12CloneCollapse {Alternative : Type v} (split : Alternative) (clones : ℕ) :
    Alternative ⊕ Fin clones → Alternative
  | Sum.inl alternative => alternative
  | Sum.inr _ => split

/-- The `clones + 1` alternatives that replace one source alternative. -/
def theorem12CloneEmbedding {Alternative : Type v} (split : Alternative) (clones : ℕ) :
    Fin (clones + 1) → Alternative ⊕ Fin clones :=
  Fin.cases (Sum.inl split) Sum.inr

/-- Conditional law that replaces one sampled alternative by a uniform clone. -/
noncomputable def theorem12CloneKernel {Alternative : Type v} [DecidableEq Alternative]
    (split : Alternative) (clones : ℕ) (alternative : Alternative) :
    PMF (Alternative ⊕ Fin clones) :=
  if alternative = split then
    (uniformPMF (Fin (clones + 1))).map (theorem12CloneEmbedding split clones)
  else PMF.pure (Sum.inl alternative)

/-- Each conditional clone law collapses exactly to its source alternative. -/
theorem theorem12CloneKernel_map_collapse {Alternative : Type v} [DecidableEq Alternative]
    (split alternative : Alternative) (clones : ℕ) :
    (theorem12CloneKernel split clones alternative).map (theorem12CloneCollapse split clones) =
      PMF.pure alternative := by
  classical
  unfold theorem12CloneKernel
  by_cases hsplit : alternative = split
  · subst alternative
    rw [if_pos rfl, PMF.map_comp]
    have hconstant : theorem12CloneCollapse split clones ∘ theorem12CloneEmbedding split clones =
        Function.const (Fin (clones + 1)) split := by
      funext clone
      refine Fin.cases ?_ ?_ clone
      · rfl
      · intro additionalClone
        rfl
    rw [hconstant, PMF.map_const]
  · rw [if_neg hsplit, PMF.pure_map]
    rfl

/-- The source sampling law after uniformly splitting one alternative into clones. -/
noncomputable def theorem12SplitSampling {Alternative : Type v} [DecidableEq Alternative]
    (sampling : PMF Alternative) (split : Alternative) (clones : ℕ) :
    PMF (Alternative ⊕ Fin clones) :=
  sampling.bind (theorem12CloneKernel split clones)

/-- A clone kernel gives positive mass to every target that collapses to its source. -/
theorem theorem12CloneKernel_toReal_pos_of_collapse_eq
    {Alternative : Type v} [Fintype Alternative] [DecidableEq Alternative]
    (split source : Alternative) (clones : ℕ) (target : Alternative ⊕ Fin clones)
    (hcollapse : theorem12CloneCollapse split clones target = source) :
    0 < (theorem12CloneKernel split clones source target).toReal := by
  classical
  by_cases hsource : source = split
  · subst source
    rw [theorem12CloneKernel, if_pos hsource, pmf_map_apply_toReal_eq_pmfProb_preimage]
    cases target with
    | inl original =>
        have horiginal : original = split := by
          simpa [theorem12CloneCollapse] using hsource
        subst original
        apply pmfProb_pos_of_mass (uniformPMF (Fin (clones + 1)))
          (fun clone => theorem12CloneEmbedding split clones clone = Sum.inl split)
          (0 : Fin (clones + 1))
        · rfl
        · exact uniformPMF_apply_toReal_pos _
    | inr clone =>
        apply pmfProb_pos_of_mass (uniformPMF (Fin (clones + 1)))
          (fun candidate => theorem12CloneEmbedding split clones candidate = Sum.inr clone)
          (Fin.succ clone)
        · rfl
        · exact uniformPMF_apply_toReal_pos _
  · rw [theorem12CloneKernel, if_neg hsource]
    cases target with
    | inl original =>
        have horiginal : original = source := by
          simpa [theorem12CloneCollapse] using hcollapse
        subst original
        simp
    | inr clone =>
        have hsplit_eq_source : split = source := by
          simpa [theorem12CloneCollapse] using hcollapse
        exact (hsource hsplit_eq_source.symm).elim

/-- Full support is preserved by the source's uniform candidate-splitting sampling law. -/
theorem theorem12SplitSampling_toReal_pos
    {Alternative : Type v} [Fintype Alternative] [DecidableEq Alternative]
    (sampling : PMF Alternative) (split : Alternative) (clones : ℕ)
    (hsampling : ∀ alternative, 0 < (sampling alternative).toReal)
    (target : Alternative ⊕ Fin clones) :
    0 < (theorem12SplitSampling sampling split clones target).toReal := by
  classical
  unfold theorem12SplitSampling
  rw [PMF.bind_apply, tsum_fintype]
  have hne_top : ∀ alternative ∈ (Finset.univ : Finset Alternative),
      sampling alternative * theorem12CloneKernel split clones alternative target ≠ ⊤ := by
    intro alternative _
    exact ENNReal.mul_ne_top (sampling.apply_ne_top alternative)
      ((theorem12CloneKernel split clones alternative).apply_ne_top target)
  rw [ENNReal.toReal_sum hne_top]
  simp only [ENNReal.toReal_mul]
  let source := theorem12CloneCollapse split clones target
  have hkernel_pos :
      0 < (theorem12CloneKernel split clones source target).toReal := by
    apply theorem12CloneKernel_toReal_pos_of_collapse_eq split source clones target
    rfl
  have hterm_pos :
      0 < (sampling source).toReal *
        (theorem12CloneKernel split clones source target).toReal :=
    mul_pos (hsampling source) hkernel_pos
  exact lt_of_lt_of_le hterm_pos
    (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun alternative : Alternative =>
        (sampling alternative).toReal *
          (theorem12CloneKernel split clones alternative target).toReal)
      (fun alternative _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (Finset.mem_univ source))

/-- Splitting and then collapsing the sampling law is exactly distribution preserving. -/
theorem theorem12SplitSampling_map_collapse {Alternative : Type v} [DecidableEq Alternative]
    (sampling : PMF Alternative) (split : Alternative) (clones : ℕ) :
    (theorem12SplitSampling sampling split clones).map (theorem12CloneCollapse split clones) =
      sampling := by
  unfold theorem12SplitSampling
  calc
    (sampling.bind (theorem12CloneKernel split clones)).map (theorem12CloneCollapse split clones) =
      sampling.bind fun alternative =>
        (theorem12CloneKernel split clones alternative).map (theorem12CloneCollapse split clones) :=
      PMF.map_bind (p := sampling) (theorem12CloneKernel split clones)
        (theorem12CloneCollapse split clones)
    _ = sampling.bind PMF.pure := by
      congr 1
      funext alternative
      exact theorem12CloneKernel_map_collapse split alternative clones
    _ = sampling := PMF.bind_pure sampling

/-- Population welfare is unchanged when an alternative is replaced by one of its clones. -/
theorem theorem12_split_populationAverageUtility
    {User : Type u} {OldAlternative : Type v} {NewAlternative : Type w}
    [Fintype User] [DecidableEq User]
    (population : PMF User) (utility : FiniteUtilityProfile User OldAlternative)
    (collapse : NewAlternative → OldAlternative) (alternative : NewAlternative) :
    populationAverageUtility population (theorem12SplitUtility utility collapse) alternative =
      populationAverageUtility population utility (collapse alternative) := by
  rfl

/-- Unit-interval normalization is preserved under candidate splitting. -/
theorem theorem12SplitUtility_unitInterval
    {User : Type u} {OldAlternative : Type v} {NewAlternative : Type w}
    (utility : FiniteUtilityProfile User OldAlternative) (collapse : NewAlternative → OldAlternative)
    (hutility : UnitIntervalUtilityProfile utility) :
    UnitIntervalUtilityProfile (theorem12SplitUtility utility collapse) := by
  intro user alternative
  exact hutility user (collapse alternative)

/--
Splitting a nonwinning alternative preserves a strict population-Borda winner,
including against every newly introduced clone.
-/
theorem theorem12Split_preserves_strictBordaWinner
    {User : Type u} {Alternative : Type v} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative) (beta : ℝ)
    (sampling : PMF Alternative) (winner split : Alternative) (clones : ℕ)
    (hsplit_ne_winner : split ≠ winner)
    (hwinning : ∀ alternative, alternative ≠ winner →
      pairwiseBordaScore.{v, 0} sampling
          (populationBradleyTerryPreference.{u, v, 0} population utility beta) alternative <
        pairwiseBordaScore.{v, 0} sampling
          (populationBradleyTerryPreference.{u, v, 0} population utility beta) winner) :
    let collapse := theorem12CloneCollapse split clones
    let splitSampling := theorem12SplitSampling sampling split clones
    let splitUtility := theorem12SplitUtility utility collapse
    ∀ alternative : Alternative ⊕ Fin clones, alternative ≠ Sum.inl winner →
      pairwiseBordaScore.{max v 0, 0} splitSampling
          (populationBradleyTerryPreference.{u, max v 0, 0} population splitUtility beta)
          alternative <
        pairwiseBordaScore.{max v 0, 0} splitSampling
          (populationBradleyTerryPreference.{u, max v 0, 0} population splitUtility beta)
          (Sum.inl winner) := by
  dsimp
  intro alternative halternative
  have hpushforward := theorem12SplitSampling_map_collapse sampling split clones
  have hcollapsed_ne : theorem12CloneCollapse split clones alternative ≠ winner := by
    cases alternative with
    | inl original =>
        intro hcollapsed
        apply halternative
        simpa [theorem12CloneCollapse] using hcollapsed
    | inr clone =>
        simpa [theorem12CloneCollapse] using hsplit_ne_winner
  have hscoreAlternative := theorem12_split_pairwiseBordaScore
    population utility beta (theorem12CloneCollapse split clones) sampling
    (theorem12SplitSampling sampling split clones) hpushforward alternative
  have hscoreWinner := theorem12_split_pairwiseBordaScore
    population utility beta (theorem12CloneCollapse split clones) sampling
    (theorem12SplitSampling sampling split clones) hpushforward (Sum.inl winner)
  calc
    pairwiseBordaScore.{max v 0, 0} (theorem12SplitSampling sampling split clones)
        (populationBradleyTerryPreference.{u, max v 0, 0} population
          (theorem12SplitUtility utility (theorem12CloneCollapse split clones)) beta) alternative =
      pairwiseBordaScore.{v, 0} sampling
        (populationBradleyTerryPreference.{u, v, 0} population utility beta)
        (theorem12CloneCollapse split clones alternative) := hscoreAlternative
    _ < pairwiseBordaScore.{v, 0} sampling
        (populationBradleyTerryPreference.{u, v, 0} population utility beta) winner :=
      hwinning _ hcollapsed_ne
    _ = pairwiseBordaScore.{max v 0, 0} (theorem12SplitSampling sampling split clones)
        (populationBradleyTerryPreference.{u, max v 0, 0} population
          (theorem12SplitUtility utility (theorem12CloneCollapse split clones)) beta)
        (Sum.inl winner) := hscoreWinner.symm

/--
Candidate-splitting extension of the Appendix-E.2 lower-bound instance.  For
every source cardinality `m ≥ 3`, each strict sub-bound below Eq. (10) occurs
on an `m`-alternative unit-interval instance whose unique population-Borda
winner is the low-welfare alternative represented by `c`.
-/
theorem theorem12_populationBorda_lower_bound_all_m
    {beta gamma q : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) (hgamma_lt_one : gamma < 1)
    (hq : q < theorem12Eq10Coefficient beta gamma) (m : ℕ) (hm : 3 ≤ m) :
    ∃ (epsilon : ℝ) (hepsilon : 0 < epsilon) (hepsilon_lt_half : epsilon < (1 : ℝ) / 2)
      (sampling : PMF (Fin 3 ⊕ Fin (m - 3))),
      epsilon ^ 2 < 1 - epsilon ∧ Fintype.card (Fin 3 ⊕ Fin (m - 3)) = m ∧
        let collapse := theorem12CloneCollapse (1 : Fin 3) (m - 3)
        let splitUtility := theorem12SplitUtility (theorem12Utility epsilon (epsilon ^ 2) gamma)
          collapse
        let population := theorem12Population beta epsilon gamma hbeta hepsilon (by linarith)
          hgamma hgamma_lt_one
        let preference := populationBradleyTerryPreference population splitUtility beta
        UnitIntervalUtilityProfile splitUtility ∧
          (∀ alternative : Fin 3 ⊕ Fin (m - 3), 0 < (sampling alternative).toReal) ∧
          (∀ alternative : Fin 3 ⊕ Fin (m - 3), alternative ≠ Sum.inl (2 : Fin 3) →
            pairwiseBordaScore sampling preference alternative <
              pairwiseBordaScore sampling preference (Sum.inl (2 : Fin 3))) ∧
          q <
            populationAverageUtility population splitUtility (Sum.inl (0 : Fin 3)) /
              populationAverageUtility population splitUtility (Sum.inl (2 : Fin 3)) := by
  obtain ⟨epsilon, hepsilon, hepsilon_lt_half, baseSampling, hepsilonZero_lt, hunit,
    hsupport, hscoreA, hscoreB, hratio⟩ :=
    theorem12_threeAlternative_populationBorda_lower_bound hbeta hgamma hgamma_lt_one hq
  have hepsilon_lt_one : epsilon < 1 := by linarith
  let baseUtility := theorem12Utility epsilon (epsilon ^ 2) gamma
  let population := theorem12Population beta epsilon gamma hbeta hepsilon hepsilon_lt_one
    hgamma hgamma_lt_one
  have hbase_winner : ∀ alternative : Fin 3, alternative ≠ (2 : Fin 3) →
      pairwiseBordaScore baseSampling
          (populationBradleyTerryPreference population baseUtility beta) alternative <
        pairwiseBordaScore baseSampling
          (populationBradleyTerryPreference population baseUtility beta) (2 : Fin 3) := by
    intro alternative halternative
    fin_cases alternative
    · simpa [population, baseUtility] using hscoreA
    · simpa [population, baseUtility] using hscoreB
    · exact (halternative rfl).elim
  have hsplit_ne_winner : (1 : Fin 3) ≠ (2 : Fin 3) := by decide
  let collapse := theorem12CloneCollapse (1 : Fin 3) (m - 3)
  let splitSampling := theorem12SplitSampling baseSampling (1 : Fin 3) (m - 3)
  refine ⟨epsilon, hepsilon, hepsilon_lt_half, splitSampling, hepsilonZero_lt, ?_, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · dsimp only
    refine ⟨theorem12SplitUtility_unitInterval baseUtility collapse hunit, ?_, ?_, ?_⟩
    · intro alternative
      simpa [splitSampling] using
        (theorem12SplitSampling_toReal_pos baseSampling (1 : Fin 3) (m - 3) hsupport alternative)
    · simpa [population, baseUtility, collapse, splitSampling] using
        (theorem12Split_preserves_strictBordaWinner population baseUtility beta baseSampling
          (2 : Fin 3) (1 : Fin 3) (m - 3) hsplit_ne_winner hbase_winner)
    · have haverageA := theorem12_split_populationAverageUtility population baseUtility collapse
        (Sum.inl (0 : Fin 3))
      have haverageC := theorem12_split_populationAverageUtility population baseUtility collapse
        (Sum.inl (2 : Fin 3))
      rw [haverageA, haverageC]
      simpa [population, baseUtility] using hratio

end GolzHaghtalabYang2025Distortion
