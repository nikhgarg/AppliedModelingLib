import AppliedModelingLib.Alignment.Welfare.BradleyTerry
import AppliedModelingLib.Alignment.Welfare.SigmoidBounds
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Tactic

/-!
# Theorem 3 lower-bound instance: balanced two-type calculation

Appendix E.3 of Gölz--Haghtalab--Yang (2025) starts from a two-type user
population.  At `ξ = 1`, its displayed masses make every comparison between
the distinguished alternative and an ordinary alternative a fair Bernoulli
trial.  This file formalizes that exact algebraic calculation before adding
the source's finite observation and asymptotic selection arguments.

The official source is the already pinned NeurIPS 2025 PDF and its cached
text transcript recorded in `docs/AML_001_FIRST_WAVE_SOURCE_PIN_LEDGER.md`.
-/

namespace GolzHaghtalabYang2025Distortion

open AppliedModelingLib.Alignment.Welfare
open scoped Topology

/-- The common denominator in the Appendix-E.3 two-type population. -/
noncomputable def theorem3BalanceDenominator (beta epsilon : ℝ) : ℝ :=
  Real.sigmoid beta + Real.sigmoid (beta * epsilon) - 1

/-- Mass of users valuing the distinguished alternative at one. -/
noncomputable def theorem3SpecialTypeMass (beta epsilon : ℝ) : ℝ :=
  (Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) /
    theorem3BalanceDenominator beta epsilon

/-- Mass of users valuing every ordinary alternative at `epsilon`. -/
noncomputable def theorem3OrdinaryTypeMass (beta epsilon : ℝ) : ℝ :=
  (Real.sigmoid beta - (1 : ℝ) / 2) /
    theorem3BalanceDenominator beta epsilon

/-- The source denominator is strictly positive for positive scale and perturbation. -/
theorem theorem3BalanceDenominator_pos
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    0 < theorem3BalanceDenominator beta epsilon := by
  unfold theorem3BalanceDenominator
  have hbeta_half : (1 : ℝ) / 2 < Real.sigmoid beta := by
    calc
      (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
      _ < Real.sigmoid beta := Real.sigmoid_lt hbeta
  have hbeta_epsilon : 0 < beta * epsilon := mul_pos hbeta hepsilon
  have hbeta_epsilon_half : (1 : ℝ) / 2 < Real.sigmoid (beta * epsilon) := by
    calc
      (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
      _ < Real.sigmoid (beta * epsilon) := Real.sigmoid_lt hbeta_epsilon
  linarith

/-- The source denominator is nonzero on its stated positive-parameter domain. -/
theorem theorem3BalanceDenominator_ne
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    theorem3BalanceDenominator beta epsilon ≠ 0 :=
  (theorem3BalanceDenominator_pos hbeta hepsilon).ne'

/-- Both displayed two-type population weights are nonnegative. -/
theorem theorem3TypeMasses_nonneg
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    0 ≤ theorem3SpecialTypeMass beta epsilon ∧
      0 ≤ theorem3OrdinaryTypeMass beta epsilon := by
  constructor
  · unfold theorem3SpecialTypeMass
    exact div_nonneg
      (sub_nonneg.mpr (by
        calc
          (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
          _ ≤ Real.sigmoid (beta * epsilon) :=
            Real.sigmoid_le (mul_nonneg hbeta.le hepsilon.le)))
      (theorem3BalanceDenominator_pos hbeta hepsilon).le
  · unfold theorem3OrdinaryTypeMass
    exact div_nonneg
      (sub_nonneg.mpr (by
        calc
          (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
          _ ≤ Real.sigmoid beta := Real.sigmoid_le hbeta.le))
      (theorem3BalanceDenominator_pos hbeta hepsilon).le

/-- Both source population weights are strictly positive on the interior parameter domain. -/
theorem theorem3TypeMasses_pos
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    0 < theorem3SpecialTypeMass beta epsilon ∧
      0 < theorem3OrdinaryTypeMass beta epsilon := by
  constructor
  · unfold theorem3SpecialTypeMass
    apply div_pos
    · apply sub_pos.mpr
      calc
        (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
        _ < Real.sigmoid (beta * epsilon) := Real.sigmoid_lt (mul_pos hbeta hepsilon)
    · exact theorem3BalanceDenominator_pos hbeta hepsilon
  · unfold theorem3OrdinaryTypeMass
    apply div_pos
    · apply sub_pos.mpr
      calc
        (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
        _ < Real.sigmoid beta := Real.sigmoid_lt hbeta
    · exact theorem3BalanceDenominator_pos hbeta hepsilon

/-- The two displayed source masses sum to one. -/
theorem theorem3TypeMasses_sum_one
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    theorem3SpecialTypeMass beta epsilon + theorem3OrdinaryTypeMass beta epsilon = 1 := by
  unfold theorem3SpecialTypeMass theorem3OrdinaryTypeMass
  rw [← add_div]
  have hnumerator :
      Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2 +
          (Real.sigmoid beta - (1 : ℝ) / 2) =
        theorem3BalanceDenominator beta epsilon := by
    unfold theorem3BalanceDenominator
    ring
  rw [hnumerator]
  exact div_self (theorem3BalanceDenominator_ne hbeta hepsilon)

/--
At `ξ = 1`, the source's two-type mixture makes the distinguished-versus-
ordinary Bradley--Terry comparison probability exactly one half.
-/
theorem theorem3_balanced_pairwise_probability
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    theorem3SpecialTypeMass beta epsilon * Real.sigmoid beta +
        theorem3OrdinaryTypeMass beta epsilon * Real.sigmoid (- (beta * epsilon)) =
      (1 : ℝ) / 2 := by
  unfold theorem3SpecialTypeMass theorem3OrdinaryTypeMass
  rw [Real.sigmoid_neg]
  have hdenominator := theorem3BalanceDenominator_ne hbeta hepsilon
  have hnumerator :
      (Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) * Real.sigmoid beta +
          (Real.sigmoid beta - (1 : ℝ) / 2) *
            (1 - Real.sigmoid (beta * epsilon)) =
        theorem3BalanceDenominator beta epsilon / 2 := by
    unfold theorem3BalanceDenominator
    ring
  calc
    (Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) /
          theorem3BalanceDenominator beta epsilon * Real.sigmoid beta +
        (Real.sigmoid beta - (1 : ℝ) / 2) /
          theorem3BalanceDenominator beta epsilon *
            (1 - Real.sigmoid (beta * epsilon)) =
        ((Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) * Real.sigmoid beta +
          (Real.sigmoid beta - (1 : ℝ) / 2) *
            (1 - Real.sigmoid (beta * epsilon))) /
          theorem3BalanceDenominator beta epsilon := by ring
    _ = (theorem3BalanceDenominator beta epsilon / 2) /
          theorem3BalanceDenominator beta epsilon := by rw [hnumerator]
    _ = (1 : ℝ) / 2 := by
      apply (div_eq_iff hdenominator).mpr
      ring

/-- The literal two-type user population used in the first part of Appendix E.3. -/
noncomputable def theorem3TwoTypePopulation
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon) : PMF Bool :=
  PMF.bernoulli
    ⟨theorem3SpecialTypeMass beta epsilon,
      (theorem3TypeMasses_nonneg hbeta hepsilon).1⟩
    (by
      change theorem3SpecialTypeMass beta epsilon ≤ 1
      nlinarith [theorem3TypeMasses_sum_one hbeta hepsilon,
        (theorem3TypeMasses_nonneg hbeta hepsilon).2])

/-- User utilities for the two-type, two-alternative core of Appendix E.3. -/
def theorem3TwoTypeUtility (epsilon xi : ℝ) : FiniteUtilityProfile Bool Bool
  | true, true => 1
  | true, false => 0
  | false, true => 0
  | false, false => xi * epsilon

@[simp] theorem theorem3TwoTypePopulation_true_toReal
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    (theorem3TwoTypePopulation beta epsilon hbeta hepsilon true).toReal =
      theorem3SpecialTypeMass beta epsilon := by
  simp [theorem3TwoTypePopulation]
  rfl

@[simp] theorem theorem3TwoTypePopulation_false_toReal
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    (theorem3TwoTypePopulation beta epsilon hbeta hepsilon false).toReal =
      theorem3OrdinaryTypeMass beta epsilon := by
  have hsum := AppliedModelingLib.pmfToRealSum
    (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
  rw [Fintype.sum_bool, theorem3TwoTypePopulation_true_toReal] at hsum
  nlinarith [theorem3TypeMasses_sum_one hbeta hepsilon]

/--
The source two-type population with `ξ = 1` induces a fair aggregated
Bradley--Terry comparison between its distinguished and ordinary alternative.
-/
theorem theorem3TwoTypePopulation_preference_unbiased
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    (AppliedModelingLib.Alignment.Welfare.populationBradleyTerryPreference
      (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3TwoTypeUtility epsilon 1) beta).prob PUnit.unit.{1} true false =
      (1 : ℝ) / 2 := by
  change AppliedModelingLib.pmfExp (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
    (fun user => Real.sigmoid
      (beta * (theorem3TwoTypeUtility epsilon 1 user true -
        theorem3TwoTypeUtility epsilon 1 user false))) = (1 : ℝ) / 2
  simpa [AppliedModelingLib.pmfExp, theorem3TwoTypeUtility] using
    theorem3_balanced_pairwise_probability hbeta hepsilon

/-- Average utility of the distinguished alternative in the two-type source instance. -/
theorem theorem3TwoType_special_averageUtility
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3TwoTypeUtility epsilon 1) true = theorem3SpecialTypeMass beta epsilon := by
  simp [populationAverageUtility, AppliedModelingLib.pmfExp, theorem3TwoTypeUtility]

/-- Average utility of either ordinary alternative in the two-type source instance. -/
theorem theorem3TwoType_ordinary_averageUtility
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3TwoTypeUtility epsilon 1) false =
        epsilon * theorem3OrdinaryTypeMass beta epsilon := by
  simp [populationAverageUtility, AppliedModelingLib.pmfExp, theorem3TwoTypeUtility]
  ring

/--
Selection-probability part of the Appendix-E.3 lower-bound argument for the
two-alternative core: if a rule selects the special alternative with mass at
most `q`, its achieved welfare is at most `q` times the special welfare plus
one ordinary-alternative welfare.
-/
theorem theorem3TwoType_policyAverageUtility_le_of_special_mass_le
    {beta epsilon q : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (policy : PMF Bool) (hselection : (policy true).toReal ≤ q) :
    policyAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3TwoTypeUtility epsilon 1) policy ≤
        q * theorem3SpecialTypeMass beta epsilon +
          epsilon * theorem3OrdinaryTypeMass beta epsilon := by
  rw [policyAverageUtility, AppliedModelingLib.pmfExp, Fintype.sum_bool,
    theorem3TwoType_special_averageUtility,
    theorem3TwoType_ordinary_averageUtility]
  have hspecial_nonneg := (theorem3TypeMasses_nonneg hbeta hepsilon).1
  have hordinary_nonneg := (theorem3TypeMasses_nonneg hbeta hepsilon).2
  have hordinary_welfare_nonneg : 0 ≤ epsilon * theorem3OrdinaryTypeMass beta epsilon :=
    mul_nonneg hepsilon.le hordinary_nonneg
  have hspecial_term :
      (policy true).toReal * theorem3SpecialTypeMass beta epsilon ≤
        q * theorem3SpecialTypeMass beta epsilon :=
    mul_le_mul_of_nonneg_right hselection hspecial_nonneg
  have hordinary_term :
      (policy false).toReal * (epsilon * theorem3OrdinaryTypeMass beta epsilon) ≤
        epsilon * theorem3OrdinaryTypeMass beta epsilon :=
    by
      simpa [mul_comm] using
        (mul_le_of_le_one_right hordinary_welfare_nonneg
          (AppliedModelingLib.pmf_apply_toReal_le_one policy false))
  linarith

/--
Finite distortion consequence of the source selection argument.  Once the
observation argument establishes that a rule selects the special alternative
with mass at most `q`, this gives the exact finite ratio preceding Eq. (11).
-/
theorem theorem3TwoType_distortion_lower_bound_of_special_mass_le
    {beta epsilon q : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (policy : PMF Bool) (hselection : (policy true).toReal ≤ q)
    (hdenominator : 0 < q * theorem3SpecialTypeMass beta epsilon +
      epsilon * theorem3OrdinaryTypeMass beta epsilon)
    (hpolicy_welfare : 0 < policyAverageUtility
      (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3TwoTypeUtility epsilon 1) policy) :
    theorem3SpecialTypeMass beta epsilon /
        (q * theorem3SpecialTypeMass beta epsilon +
          epsilon * theorem3OrdinaryTypeMass beta epsilon) ≤
      theorem3SpecialTypeMass beta epsilon /
        policyAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
          (theorem3TwoTypeUtility epsilon 1) policy := by
  apply (div_le_div_iff₀ hdenominator hpolicy_welfare).mpr
  exact mul_le_mul_of_nonneg_left
    (theorem3TwoType_policyAverageUtility_le_of_special_mass_le
      hbeta hepsilon policy hselection)
    (theorem3TypeMasses_nonneg hbeta hepsilon).1

/--
Finite pigeonhole step used by the source after its indistinguishability
argument: every randomized rule over a nonempty finite alternative set has
an alternative selected with at most uniform probability.
-/
theorem exists_selection_mass_le_uniform
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    [Nonempty Alternative] (selection : PMF Alternative) :
    ∃ alternative : Alternative,
      (selection alternative).toReal ≤ (Fintype.card Alternative : ℝ)⁻¹ := by
  classical
  by_contra h
  simp only [not_exists, not_le] at h
  have hstrict :
      (∑ _alternative : Alternative, (Fintype.card Alternative : ℝ)⁻¹) <
        ∑ alternative : Alternative, (selection alternative).toReal := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty
    intro alternative _
    exact h alternative
  have hcard : (Fintype.card Alternative : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hconstant :
      (∑ _alternative : Alternative, (Fintype.card Alternative : ℝ)⁻¹) = 1 := by
    calc
      (∑ _alternative : Alternative, (Fintype.card Alternative : ℝ)⁻¹) =
          (Fintype.card Alternative : ℝ) * (Fintype.card Alternative : ℝ)⁻¹ := by
        simp [nsmul_eq_mul]
      _ = 1 := by field_simp
  have hsum := AppliedModelingLib.pmfToRealSum selection
  linarith

/--
Selection-welfare inequality underlying source Eq. (11).  All nonspecial
alternatives receive the common welfare `ordinaryWelfare`; it is enough to
control the selection mass of the special alternative.
-/
theorem selection_welfare_le_of_special_mass_le
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (selection : PMF Alternative) (special : Alternative)
    (specialWelfare ordinaryWelfare q : ℝ)
    (hspecial_nonneg : 0 ≤ specialWelfare)
    (hordinary_nonneg : 0 ≤ ordinaryWelfare)
    (hselection : (selection special).toReal ≤ q) :
    AppliedModelingLib.pmfExp selection
      (fun alternative => if alternative = special then specialWelfare else ordinaryWelfare) ≤
        q * specialWelfare + ordinaryWelfare := by
  rw [AppliedModelingLib.pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    selection (fun alternative => alternative = special)
    (fun alternative => if alternative = special then specialWelfare else ordinaryWelfare)
    specialWelfare ordinaryWelfare (fun _ => rfl),
    AppliedModelingLib.pmfProb_singleton]
  have hspecial_term :
      (selection special).toReal * specialWelfare ≤ q * specialWelfare :=
    mul_le_mul_of_nonneg_right hselection hspecial_nonneg
  have hordinary_term :
      (1 - (selection special).toReal) * ordinaryWelfare ≤ ordinaryWelfare := by
    simpa [mul_comm] using
      (mul_le_of_le_one_right hordinary_nonneg (by
        have hmass_nonneg : 0 ≤ (selection special).toReal := ENNReal.toReal_nonneg
        linarith))
  linarith

/-- The unconditional output law of a randomized voting rule after an observation law. -/
noncomputable def theorem3ObservationSelectionLaw
    {Observation Alternative : Type*}
    (observationLaw : PMF Observation) (rule : Observation → PMF Alternative) : PMF Alternative :=
  observationLaw.bind rule

/--
The source's probabilistic Condorcet-loser axiom for a randomized rule: when
the supplied observation certifies an alternative as a Condorcet loser, the
rule assigns it at most uniform probability mass.
-/
def theorem3ProbabilisticCondorcetLoserCriterion
    {Observation Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (rule : Observation → PMF Alternative) (isCondorcetLoser : Observation → Alternative → Prop) :
    Prop :=
  ∀ observation alternative, isCondorcetLoser observation alternative →
    (rule observation alternative).toReal ≤ (Fintype.card Alternative : ℝ)⁻¹

/--
An observation-level Condorcet-loser certificate that fails with probability
at most `η` forces the unconditional selection mass to be at most uniform
mass plus `η`. This separates the source's behavioral axiom from the
probability-convergence argument for the empirical certificate.
-/
theorem theorem3_selectionMass_le_uniform_add_condorcetCertificateError
    {Observation Alternative : Type*} [Fintype Observation] [DecidableEq Observation]
    [Fintype Alternative] [DecidableEq Alternative]
    (observationLaw : PMF Observation) (rule : Observation → PMF Alternative)
    (isCondorcetLoser : Observation → Alternative → Prop)
    [∀ observation alternative, Decidable (isCondorcetLoser observation alternative)]
    (hcriterion : theorem3ProbabilisticCondorcetLoserCriterion rule isCondorcetLoser)
    (special : Alternative) (eta : ℝ)
    (hbad : AppliedModelingLib.pmfProb observationLaw
      (fun observation => ¬isCondorcetLoser observation special) ≤ eta) :
    (theorem3ObservationSelectionLaw observationLaw rule special).toReal ≤
      (Fintype.card Alternative : ℝ)⁻¹ + eta := by
  rw [← AppliedModelingLib.pmfProb_singleton]
  unfold theorem3ObservationSelectionLaw
  rw [AppliedModelingLib.pmfProb_bind]
  simp_rw [AppliedModelingLib.pmfProb_singleton]
  calc
    AppliedModelingLib.pmfExp observationLaw (fun observation => (rule observation special).toReal) ≤
        AppliedModelingLib.pmfExp observationLaw
          (fun observation => (Fintype.card Alternative : ℝ)⁻¹ +
            if ¬isCondorcetLoser observation special then (1 : ℝ) else 0) := by
              apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
              intro observation
              by_cases hgood : isCondorcetLoser observation special
              · simpa [hgood] using hcriterion observation special hgood
              · simp [hgood]
                exact le_trans
                  (AppliedModelingLib.pmf_apply_toReal_le_one (rule observation) special)
                  (by
                    have hinv_nonneg : 0 ≤ (Fintype.card Alternative : ℝ)⁻¹ :=
                      inv_nonneg.mpr (Nat.cast_nonneg _)
                    linarith)
    _ = (Fintype.card Alternative : ℝ)⁻¹ +
        AppliedModelingLib.pmfProb observationLaw
          (fun observation => ¬isCondorcetLoser observation special) := by
            rw [AppliedModelingLib.pmfExp_add, AppliedModelingLib.pmfExp_const]
            rfl
    _ ≤ (Fintype.card Alternative : ℝ)⁻¹ + eta := by linarith

/--
If the empirical Condorcet-loser certificate has vanishing failure
probability, the source's behavioral axiom makes the unconditional mass on
that alternative asymptotically no larger than uniform mass. Observation
spaces may vary with the sample horizon, as in the source's user-report model.
-/
theorem theorem3_eventually_selectionMass_le_uniform_add_of_condorcetCertificateTendsto
    {Observation : ℕ → Type*} {Alternative : Type*}
    [Fintype Alternative] [DecidableEq Alternative]
    [∀ horizon, Fintype (Observation horizon)] [∀ horizon, DecidableEq (Observation horizon)]
    (observationLaw : ∀ horizon, PMF (Observation horizon))
    (rule : ∀ horizon, Observation horizon → PMF Alternative)
    (isCondorcetLoser : ∀ horizon, Observation horizon → Alternative → Prop)
    [∀ horizon observation alternative,
      Decidable (isCondorcetLoser horizon observation alternative)]
    (hcriterion : ∀ horizon,
      theorem3ProbabilisticCondorcetLoserCriterion (rule horizon)
        (isCondorcetLoser horizon))
    (special : Alternative)
    (hcertificate : Filter.Tendsto
      (fun horizon => AppliedModelingLib.pmfProb (observationLaw horizon)
        (fun observation => ¬isCondorcetLoser horizon observation special))
      Filter.atTop (𝓝 0))
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ horizon : ℕ in Filter.atTop,
      (theorem3ObservationSelectionLaw (observationLaw horizon) (rule horizon) special).toReal ≤
        (Fintype.card Alternative : ℝ)⁻¹ + delta := by
  filter_upwards [hcertificate.eventually_lt_const hdelta] with horizon hfailure
  exact le_trans
    (theorem3_selectionMass_le_uniform_add_condorcetCertificateError
      (observationLaw horizon) (rule horizon) (isCondorcetLoser horizon)
      (hcriterion horizon) special delta (le_of_lt hfailure))
    le_rfl

/-- A least-likely output selected from a finite randomized rule. -/
noncomputable def theorem3LowSelectionAlternative
    {Observation Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    [Nonempty Alternative]
    (observationLaw : PMF Observation) (rule : Observation → PMF Alternative) : Alternative :=
  (exists_selection_mass_le_uniform
    (theorem3ObservationSelectionLaw observationLaw rule)).choose

/-- The selected least-likely output has mass at most the uniform mass. -/
theorem theorem3LowSelectionAlternative_spec
    {Observation Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    [Nonempty Alternative]
    (observationLaw : PMF Observation) (rule : Observation → PMF Alternative) :
    (theorem3ObservationSelectionLaw observationLaw rule
      (theorem3LowSelectionAlternative observationLaw rule)).toReal ≤
        (Fintype.card Alternative : ℝ)⁻¹ :=
  (exists_selection_mass_le_uniform
    (theorem3ObservationSelectionLaw observationLaw rule)).choose_spec

/--
One observed special-versus-ordinary comparison from the two-type source
instance.  At `ξ = 1` its success probability is proved below to be one half.
-/
noncomputable def theorem3TwoTypePairwiseObservationLaw
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon) : PMF Bool :=
  let preference := populationBradleyTerryPreference
    (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
    (theorem3TwoTypeUtility epsilon 1) beta
  PMF.bernoulli
    ⟨preference.prob PUnit.unit.{1} true false,
      preference.nonneg PUnit.unit.{1} true false⟩
    (preference.le_one PUnit.unit.{1} true false)

/-- The source one-comparison law is the uniform fair-bit law. -/
theorem theorem3TwoTypePairwiseObservationLaw_eq_uniform
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    theorem3TwoTypePairwiseObservationLaw beta epsilon hbeta hepsilon =
      AppliedModelingLib.uniformPMF Bool := by
  apply PMF.ext
  intro outcome
  have hhalf :
      ENNReal.ofNNReal ⟨(2 : ℝ)⁻¹, by positivity⟩ = (2 : ENNReal)⁻¹ := by
    rw [ENNReal.coe_nnreal_eq]
    change ENNReal.ofReal ((2 : ℝ)⁻¹) = (2 : ENNReal)⁻¹
    rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  cases outcome
  · simp [theorem3TwoTypePairwiseObservationLaw, AppliedModelingLib.uniformPMF,
      theorem3TwoTypePopulation_preference_unbiased hbeta hepsilon]
    rw [hhalf]
    exact ENNReal.one_sub_inv_two
  · simp [theorem3TwoTypePairwiseObservationLaw, AppliedModelingLib.uniformPMF,
      theorem3TwoTypePopulation_preference_unbiased hbeta hepsilon]
    exact hhalf

/-- The `n` independent one-comparison observations in the source lower-bound model. -/
noncomputable def theorem3TwoTypeObservationLaw
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (horizon : ℕ) : PMF (Fin horizon → Bool) :=
  AppliedModelingLib.pmfProduct (Fin horizon) Bool
    (theorem3TwoTypePairwiseObservationLaw beta epsilon hbeta hepsilon)

/-- The finite source observation table is uniform once all comparisons are balanced. -/
theorem theorem3TwoTypeObservationLaw_eq_uniform
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (horizon : ℕ) :
    theorem3TwoTypeObservationLaw beta epsilon hbeta hepsilon horizon =
      AppliedModelingLib.uniformPMF (Fin horizon → Bool) := by
  unfold theorem3TwoTypeObservationLaw
  rw [theorem3TwoTypePairwiseObservationLaw_eq_uniform hbeta hepsilon,
    AppliedModelingLib.pmfProduct_uniformPMF_eq_uniformPMF_fun]

/--
Finite pigeonhole across infinitely many sample horizons.  This formalizes
the Appendix-E.3 move from one low-probability output at each horizon to one
fixed alternative that is low-probability along infinitely many horizons,
provided the observation law is independent of which alternative is declared
special.
-/
theorem theorem3_exists_fixed_low_selection_alternative
    {Observation : ℕ → Type*} {Alternative : Type*}
    [Fintype Alternative] [DecidableEq Alternative]
    [Nonempty Alternative]
    (observationLaw : ∀ horizon, PMF (Observation horizon))
    (rule : ∀ horizon, Observation horizon → PMF Alternative) :
    ∃ alternative : Alternative,
      Set.Infinite {horizon : ℕ |
        (theorem3ObservationSelectionLaw (observationLaw horizon) (rule horizon)
          alternative).toReal ≤ (Fintype.card Alternative : ℝ)⁻¹} := by
  classical
  let lowAlternative : ℕ → Alternative := fun horizon =>
    theorem3LowSelectionAlternative (observationLaw horizon) (rule horizon)
  obtain ⟨alternative, hfiber⟩ := Finite.exists_infinite_fiber lowAlternative
  have hfiber' : Set.Infinite (lowAlternative ⁻¹' {alternative}) :=
    Set.infinite_coe_iff.mp hfiber
  refine ⟨alternative, hfiber'.mono ?_⟩
  intro horizon hhorizon
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hhorizon
  rw [← hhorizon]
  exact theorem3LowSelectionAlternative_spec (observationLaw horizon) (rule horizon)

/--
For the source two-type instance, a rule's output law is unchanged if its
comparison table is replaced by the explicit uniform fair-bit table.  This is
the finite indistinguishability premise used in Appendix E.3.
-/
theorem theorem3TwoTypeObservationSelectionLaw_eq_uniform_input
    {Alternative : Type*} (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (horizon : ℕ) (rule : (Fin horizon → Bool) → PMF Alternative) :
    theorem3ObservationSelectionLaw
      (theorem3TwoTypeObservationLaw beta epsilon hbeta hepsilon horizon) rule =
      theorem3ObservationSelectionLaw (AppliedModelingLib.uniformPMF (Fin horizon → Bool)) rule := by
  rw [theorem3TwoTypeObservationLaw_eq_uniform hbeta hepsilon horizon]

/--
The source two-type observation law, together with the finite pigeonhole
argument, supplies one fixed alternative whose selection mass is at most
uniform along infinitely many sample horizons.  The preceding theorem makes
explicit that this law is the same fair-bit law for every distinguished
alternative in the eventual many-alternative construction.
-/
theorem theorem3TwoType_exists_fixed_low_selection_alternative
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    [Nonempty Alternative]
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (rule : ∀ horizon, (Fin horizon → Bool) → PMF Alternative) :
    ∃ alternative : Alternative,
      Set.Infinite {horizon : ℕ |
        (theorem3ObservationSelectionLaw
          (theorem3TwoTypeObservationLaw beta epsilon hbeta hepsilon horizon)
          (rule horizon) alternative).toReal ≤ (Fintype.card Alternative : ℝ)⁻¹} := by
  exact theorem3_exists_fixed_low_selection_alternative
    (Observation := fun horizon => Fin horizon → Bool)
    (fun horizon => theorem3TwoTypeObservationLaw beta epsilon hbeta hepsilon horizon) rule

/--
The Appendix-E.3 utility profile with an arbitrary designated special
alternative.  The `true` user type values only `special`; the `false` type
values every other alternative equally.
-/
def theorem3ManyAlternativeUtility
    {Alternative : Type*} [DecidableEq Alternative]
    (epsilon xi : ℝ) (special : Alternative) : FiniteUtilityProfile Bool Alternative
  | true, alternative => if alternative = special then 1 else 0
  | false, alternative => if alternative = special then 0 else xi * epsilon

/-- Average utility of the special alternative in the many-alternative source instance. -/
theorem theorem3ManyAlternative_special_averageUtility
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (beta epsilon xi : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special : Alternative) :
    populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon xi special) special =
        theorem3SpecialTypeMass beta epsilon := by
  simp [populationAverageUtility, AppliedModelingLib.pmfExp, theorem3ManyAlternativeUtility]

/-- Every nonspecial alternative has the common source welfare. -/
theorem theorem3ManyAlternative_ordinary_averageUtility
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (beta epsilon xi : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special ordinary : Alternative) (hordinary : ordinary ≠ special) :
    populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon xi special) ordinary =
        xi * epsilon * theorem3OrdinaryTypeMass beta epsilon := by
  simp [populationAverageUtility, AppliedModelingLib.pmfExp, theorem3ManyAlternativeUtility, hordinary]
  ring

/-- At `ξ = 1`, a special-versus-ordinary comparison is a fair coin flip. -/
theorem theorem3ManyAlternative_special_vs_ordinary_unbiased
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special ordinary : Alternative) (hordinary : ordinary ≠ special) :
    (populationBradleyTerryPreference
      (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon 1 special) beta).prob PUnit.unit.{1}
        special ordinary = (1 : ℝ) / 2 := by
  change AppliedModelingLib.pmfExp (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
    (fun user => Real.sigmoid
      (beta * (theorem3ManyAlternativeUtility epsilon 1 special user special -
        theorem3ManyAlternativeUtility epsilon 1 special user ordinary))) = (1 : ℝ) / 2
  simpa [AppliedModelingLib.pmfExp, theorem3ManyAlternativeUtility, hordinary] using
    theorem3_balanced_pairwise_probability hbeta hepsilon

/--
For the `ξ > 1` perturbation used in the multi-comparison branch of Appendix
E.3, every ordinary alternative defeats the special alternative in population
comparison probability. Thus the special alternative is a strict population
Condorcet loser.
-/
theorem theorem3ManyAlternative_special_vs_ordinary_lt_half_of_one_lt_xi
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {beta epsilon xi : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hxi : 1 < xi) (special ordinary : Alternative) (hordinary : ordinary ≠ special) :
    (populationBradleyTerryPreference
      (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon xi special) beta).prob PUnit.unit.{1}
        special ordinary < (1 : ℝ) / 2 := by
  have hxi_eps : epsilon < xi * epsilon := by
    nlinarith [mul_pos (sub_pos.mpr hxi) hepsilon]
  have hargument : -(beta * (xi * epsilon)) < -(beta * epsilon) := by
    exact neg_lt_neg (mul_lt_mul_of_pos_left hxi_eps hbeta)
  have hsigmoid : Real.sigmoid (-(beta * (xi * epsilon))) <
      Real.sigmoid (-(beta * epsilon)) := Real.sigmoid_lt hargument
  have hordinary_mass : 0 < theorem3OrdinaryTypeMass beta epsilon :=
    (theorem3TypeMasses_pos hbeta hepsilon).2
  change AppliedModelingLib.pmfExp (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
    (fun user => Real.sigmoid
      (beta * (theorem3ManyAlternativeUtility epsilon xi special user special -
        theorem3ManyAlternativeUtility epsilon xi special user ordinary))) < (1 : ℝ) / 2
  calc
    AppliedModelingLib.pmfExp (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
        (fun user => Real.sigmoid
          (beta * (theorem3ManyAlternativeUtility epsilon xi special user special -
            theorem3ManyAlternativeUtility epsilon xi special user ordinary))) =
        theorem3SpecialTypeMass beta epsilon * Real.sigmoid beta +
          theorem3OrdinaryTypeMass beta epsilon * Real.sigmoid (-(beta * (xi * epsilon))) := by
            simp [AppliedModelingLib.pmfExp, theorem3ManyAlternativeUtility, hordinary]
    _ < theorem3SpecialTypeMass beta epsilon * Real.sigmoid beta +
          theorem3OrdinaryTypeMass beta epsilon * Real.sigmoid (-(beta * epsilon)) := by
            gcongr
    _ = (1 : ℝ) / 2 := by
      simpa [Real.sigmoid_neg] using theorem3_balanced_pairwise_probability hbeta hepsilon

/-- The equivalent ordinary-versus-special direction used by the Condorcet-loser branch. -/
theorem theorem3ManyAlternative_ordinary_vs_special_gt_half_of_one_lt_xi
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {beta epsilon xi : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hxi : 1 < xi) (special ordinary : Alternative) (hordinary : ordinary ≠ special) :
    (1 : ℝ) / 2 <
      (populationBradleyTerryPreference
        (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
        (theorem3ManyAlternativeUtility epsilon xi special) beta).prob PUnit.unit.{1}
          ordinary special := by
  have hforward := theorem3ManyAlternative_special_vs_ordinary_lt_half_of_one_lt_xi
    hbeta hepsilon hxi special ordinary hordinary
  have hcomplement :=
    (populationBradleyTerryPreference
      (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon xi special) beta).complementary
        PUnit.unit.{1} ordinary special
  linarith

/-- Strict population Condorcet-loser predicate for the source's comparison model. -/
def theorem3IsStrictPopulationCondorcetLoser
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (beta epsilon xi : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special : Alternative) : Prop :=
  ∀ ordinary, ordinary ≠ special →
    (1 : ℝ) / 2 <
      (populationBradleyTerryPreference
        (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
        (theorem3ManyAlternativeUtility epsilon xi special) beta).prob PUnit.unit.{1}
          ordinary special

/-- The `ξ > 1` source instance makes its special alternative a strict population loser. -/
theorem theorem3ManyAlternative_special_is_strictPopulationCondorcetLoser_of_one_lt_xi
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {beta epsilon xi : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) (hxi : 1 < xi)
    (special : Alternative) :
    theorem3IsStrictPopulationCondorcetLoser beta epsilon xi hbeta hepsilon special := by
  intro ordinary hordinary
  exact theorem3ManyAlternative_ordinary_vs_special_gt_half_of_one_lt_xi
    hbeta hepsilon hxi special ordinary hordinary

/-- Comparisons between two nonspecial alternatives are fair for every `ξ`. -/
theorem theorem3ManyAlternative_ordinary_vs_ordinary_unbiased
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (beta epsilon xi : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special first second : Alternative)
    (hfirst : first ≠ special) (hsecond : second ≠ special) :
    (populationBradleyTerryPreference
      (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon xi special) beta).prob PUnit.unit.{1}
        first second = (1 : ℝ) / 2 := by
  change AppliedModelingLib.pmfExp (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
    (fun user => Real.sigmoid
      (beta * (theorem3ManyAlternativeUtility epsilon xi special user first -
        theorem3ManyAlternativeUtility epsilon xi special user second))) = (1 : ℝ) / 2
  calc
    AppliedModelingLib.pmfExp (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
        (fun user => Real.sigmoid
          (beta * (theorem3ManyAlternativeUtility epsilon xi special user first -
            theorem3ManyAlternativeUtility epsilon xi special user second))) =
      AppliedModelingLib.pmfExp (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
        (fun _ : Bool => Real.sigmoid 0) := by
          apply AppliedModelingLib.pmfExp_congr
          intro user
          cases user <;>
            simp [theorem3ManyAlternativeUtility, hfirst, hsecond]
    _ = (1 : ℝ) / 2 := by simp [Real.sigmoid_zero]

/-- A special alternative compared with itself also gives the fair value. -/
theorem theorem3ManyAlternative_special_vs_self_unbiased
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (beta epsilon xi : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special : Alternative) :
    (populationBradleyTerryPreference
      (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon xi special) beta).prob PUnit.unit.{1}
        special special = (1 : ℝ) / 2 := by
  change AppliedModelingLib.pmfExp (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
    (fun user => Real.sigmoid
      (beta * (theorem3ManyAlternativeUtility epsilon xi special user special -
        theorem3ManyAlternativeUtility epsilon xi special user special))) = (1 : ℝ) / 2
  simp [Real.sigmoid_zero]

/--
At `ξ = 1`, every ordered pair has the same aggregate comparison law.  This
is the precise finite form of the source's observation indistinguishability
claim before independent samples are drawn.
-/
theorem theorem3ManyAlternative_all_pairwise_unbiased
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special first second : Alternative) :
    (populationBradleyTerryPreference
      (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon 1 special) beta).prob PUnit.unit.{1}
        first second = (1 : ℝ) / 2 := by
  by_cases hfirst : first = special
  · subst first
    by_cases hsecond : second = special
    · subst second
      exact theorem3ManyAlternative_special_vs_self_unbiased
        beta epsilon 1 hbeta hepsilon special
    · exact theorem3ManyAlternative_special_vs_ordinary_unbiased
        hbeta hepsilon special second hsecond
  · by_cases hsecond : second = special
    · subst second
      have hforward := theorem3ManyAlternative_special_vs_ordinary_unbiased
        hbeta hepsilon special first hfirst
      have hcomplement :=
        (populationBradleyTerryPreference
          (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
          (theorem3ManyAlternativeUtility epsilon 1 special) beta).complementary
            PUnit.unit.{1} first special
      linarith
    · exact theorem3ManyAlternative_ordinary_vs_ordinary_unbiased
        beta epsilon 1 hbeta hepsilon special first second hfirst hsecond

/-- A Bernoulli PMF whose real success mass is one half is the uniform bit law. -/
theorem bernoulli_eq_uniformPMF_bool_of_toReal_eq_half
    (success : NNReal) (hsuccess : success ≤ 1)
    (hsuccess_half : success.toReal = (1 : ℝ) / 2) :
    PMF.bernoulli success hsuccess = AppliedModelingLib.uniformPMF Bool := by
  have hsuccess_eq : success = ⟨(2 : ℝ)⁻¹, by positivity⟩ := by
    apply Subtype.ext
    change success.toReal = (2 : ℝ)⁻¹
    exact hsuccess_half.trans (by norm_num)
  subst success
  apply PMF.ext
  intro outcome
  have hhalf :
      ENNReal.ofNNReal ⟨(2 : ℝ)⁻¹, by positivity⟩ = (2 : ENNReal)⁻¹ := by
    rw [ENNReal.coe_nnreal_eq]
    change ENNReal.ofReal ((2 : ℝ)⁻¹) = (2 : ENNReal)⁻¹
    rw [ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  cases outcome
  · simp [AppliedModelingLib.uniformPMF]
    rw [hhalf]
    exact ENNReal.one_sub_inv_two
  · simp [AppliedModelingLib.uniformPMF]
    exact hhalf

/--
One source observation contains its sampled ordered comparison pair and its
binary outcome.  This is the `d = 1` observation model of Appendix E.3.
-/
noncomputable def theorem3ManyAlternativeOneComparisonLaw
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (pairSampling : PMF (Alternative × Alternative))
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special : Alternative) : PMF ((Alternative × Alternative) × Bool) :=
  pairSampling.bind fun pair =>
    let preference := populationBradleyTerryPreference
      (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon 1 special) beta
    (PMF.bernoulli
      ⟨preference.prob PUnit.unit.{1} pair.1 pair.2,
        preference.nonneg PUnit.unit.{1} pair.1 pair.2⟩
      (preference.le_one PUnit.unit.{1} pair.1 pair.2)).map
        (fun outcome => (pair, outcome))

/-- The comparison-pair sampling law followed by an explicit fair bit. -/
noncomputable def theorem3FairOneComparisonLaw
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (pairSampling : PMF (Alternative × Alternative)) : PMF ((Alternative × Alternative) × Bool) :=
  pairSampling.bind fun pair =>
    (AppliedModelingLib.uniformPMF Bool).map (fun outcome => (pair, outcome))

/--
The full one-comparison observation distribution is independent of which
alternative is special.  Pair labels remain visible, exactly as in the source
model; only their outcomes are replaced by fair bits.
-/
theorem theorem3ManyAlternativeOneComparisonLaw_eq_fair
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (pairSampling : PMF (Alternative × Alternative))
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special : Alternative) :
    theorem3ManyAlternativeOneComparisonLaw pairSampling beta epsilon hbeta hepsilon special =
      theorem3FairOneComparisonLaw pairSampling := by
  unfold theorem3ManyAlternativeOneComparisonLaw theorem3FairOneComparisonLaw
  apply congrArg (fun kernel => pairSampling.bind kernel)
  funext pair
  dsimp
  exact congrArg (PMF.map (fun outcome : Bool => (pair, outcome)))
    (bernoulli_eq_uniformPMF_bool_of_toReal_eq_half _ _
    (theorem3ManyAlternative_all_pairwise_unbiased hbeta hepsilon special pair.1 pair.2)
    )

/-- Independent one-comparison observations from the source `d = 1` model. -/
noncomputable def theorem3ManyAlternativeObservationLaw
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (pairSampling : PMF (Alternative × Alternative))
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special : Alternative) (horizon : ℕ) :
    PMF (Fin horizon → ((Alternative × Alternative) × Bool)) :=
  AppliedModelingLib.pmfProduct (Fin horizon) ((Alternative × Alternative) × Bool)
    (theorem3ManyAlternativeOneComparisonLaw pairSampling beta epsilon hbeta hepsilon special)

/-- The source observation table with the special alternative hidden. -/
noncomputable def theorem3FairObservationLaw
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (pairSampling : PMF (Alternative × Alternative)) (horizon : ℕ) :
    PMF (Fin horizon → ((Alternative × Alternative) × Bool)) :=
  AppliedModelingLib.pmfProduct (Fin horizon) ((Alternative × Alternative) × Bool)
    (theorem3FairOneComparisonLaw pairSampling)

/-- The full finite observation table is independent of the special alternative. -/
theorem theorem3ManyAlternativeObservationLaw_eq_fair
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (pairSampling : PMF (Alternative × Alternative))
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (special : Alternative) (horizon : ℕ) :
    theorem3ManyAlternativeObservationLaw pairSampling beta epsilon hbeta hepsilon special horizon =
      theorem3FairObservationLaw pairSampling horizon := by
  unfold theorem3ManyAlternativeObservationLaw theorem3FairObservationLaw
  rw [theorem3ManyAlternativeOneComparisonLaw_eq_fair pairSampling hbeta hepsilon special]

/--
The source's permutation/pigeonhole step for `d = 1`: some choice of the
special alternative has selection probability at most uniform on infinitely
many sample horizons, even when the rule randomizes after seeing all labelled
comparison observations.
-/
theorem theorem3ManyAlternative_exists_fixed_low_selection_alternative
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    [Nonempty Alternative]
    (pairSampling : PMF (Alternative × Alternative))
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (rule : ∀ horizon,
      (Fin horizon → ((Alternative × Alternative) × Bool)) → PMF Alternative) :
    ∃ special : Alternative,
      Set.Infinite {horizon : ℕ |
        (theorem3ObservationSelectionLaw
          (theorem3ManyAlternativeObservationLaw pairSampling beta epsilon hbeta hepsilon
            special horizon)
          (rule horizon) special).toReal ≤ (Fintype.card Alternative : ℝ)⁻¹} := by
  obtain ⟨special, hspecial⟩ := theorem3_exists_fixed_low_selection_alternative
    (Observation := fun horizon => Fin horizon → ((Alternative × Alternative) × Bool))
    (fun horizon => theorem3FairObservationLaw pairSampling horizon) rule
  refine ⟨special, ?_⟩
  have hset :
      {horizon : ℕ |
        (theorem3ObservationSelectionLaw
          (theorem3ManyAlternativeObservationLaw pairSampling beta epsilon hbeta hepsilon
            special horizon)
          (rule horizon) special).toReal ≤ (Fintype.card Alternative : ℝ)⁻¹} =
        {horizon : ℕ |
          (theorem3ObservationSelectionLaw
            (theorem3FairObservationLaw pairSampling horizon)
            (rule horizon) special).toReal ≤ (Fintype.card Alternative : ℝ)⁻¹} := by
    ext horizon
    simp only [Set.mem_setOf_eq]
    rw [theorem3ManyAlternativeObservationLaw_eq_fair pairSampling hbeta hepsilon special horizon]
  rw [hset]
  exact hspecial

/--
The source's Eq. (11) welfare estimate for its many-alternative population.
Only the probability assigned to the distinguished alternative needs to be
controlled because all other alternatives have the common welfare shown here.
-/
theorem theorem3ManyAlternative_policyAverageUtility_le_of_special_mass_le
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {beta epsilon xi q : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hxi : 0 ≤ xi) (special : Alternative) (policy : PMF Alternative)
    (hselection : (policy special).toReal ≤ q) :
    policyAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon xi special) policy ≤
        q * theorem3SpecialTypeMass beta epsilon +
          xi * epsilon * theorem3OrdinaryTypeMass beta epsilon := by
  have havg :
      (fun alternative =>
        populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
          (theorem3ManyAlternativeUtility epsilon xi special) alternative) =
        (fun alternative => if alternative = special then theorem3SpecialTypeMass beta epsilon
          else xi * epsilon * theorem3OrdinaryTypeMass beta epsilon) := by
    funext alternative
    by_cases halternative : alternative = special
    · subst alternative
      simp [theorem3ManyAlternative_special_averageUtility]
    · simp [halternative,
      theorem3ManyAlternative_ordinary_averageUtility beta epsilon xi hbeta hepsilon
        special alternative halternative]
  unfold policyAverageUtility
  change AppliedModelingLib.pmfExp policy
    (fun alternative =>
      populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
        (theorem3ManyAlternativeUtility epsilon xi special) alternative) ≤ _
  rw [havg]
  apply selection_welfare_le_of_special_mass_le policy special
    (theorem3SpecialTypeMass beta epsilon)
    (xi * epsilon * theorem3OrdinaryTypeMass beta epsilon)
  · exact (theorem3TypeMasses_nonneg hbeta hepsilon).1
  · exact mul_nonneg (mul_nonneg hxi hepsilon.le)
      (theorem3TypeMasses_nonneg hbeta hepsilon).2
  · exact hselection

/--
If a policy does not put all of its mass on the distinguished alternative,
then the Appendix-E.3 instance has strictly positive achieved welfare whenever
the ordinary alternatives have strictly positive utility.
-/
theorem theorem3ManyAlternative_policyAverageUtility_pos_of_special_mass_lt_one
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {beta epsilon xi : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hxi : 0 < xi) (special : Alternative) (policy : PMF Alternative)
    (hselection : (policy special).toReal < 1) :
    0 < policyAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon xi special) policy := by
  have havg :
      (fun alternative =>
        populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
          (theorem3ManyAlternativeUtility epsilon xi special) alternative) =
        (fun alternative => if alternative = special then theorem3SpecialTypeMass beta epsilon
          else xi * epsilon * theorem3OrdinaryTypeMass beta epsilon) := by
    funext alternative
    by_cases halternative : alternative = special
    · subst alternative
      simp [theorem3ManyAlternative_special_averageUtility]
    · simp [halternative,
      theorem3ManyAlternative_ordinary_averageUtility beta epsilon xi hbeta hepsilon
        special alternative halternative]
  have hspecial_nonneg : 0 ≤ theorem3SpecialTypeMass beta epsilon :=
    (theorem3TypeMasses_nonneg hbeta hepsilon).1
  have hordinary_pos : 0 < xi * epsilon * theorem3OrdinaryTypeMass beta epsilon :=
    mul_pos (mul_pos hxi hepsilon) (theorem3TypeMasses_pos hbeta hepsilon).2
  unfold policyAverageUtility
  change 0 < AppliedModelingLib.pmfExp policy
    (fun alternative =>
      populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
        (theorem3ManyAlternativeUtility epsilon xi special) alternative)
  rw [havg]
  rw [AppliedModelingLib.pmfExp_eq_prob_mul_add_one_sub_prob_mul_of_forall_eq_if
    policy (fun alternative => alternative = special)
    (fun alternative => if alternative = special then theorem3SpecialTypeMass beta epsilon
      else xi * epsilon * theorem3OrdinaryTypeMass beta epsilon)
    (theorem3SpecialTypeMass beta epsilon)
    (xi * epsilon * theorem3OrdinaryTypeMass beta epsilon) (fun _ => rfl),
    AppliedModelingLib.pmfProb_singleton]
  have hspecial_term_nonneg :
      0 ≤ (policy special).toReal * theorem3SpecialTypeMass beta epsilon :=
    mul_nonneg ENNReal.toReal_nonneg hspecial_nonneg
  have hordinary_term_pos :
      0 < (1 - (policy special).toReal) *
        (xi * epsilon * theorem3OrdinaryTypeMass beta epsilon) :=
    mul_pos (sub_pos.mpr hselection) hordinary_pos
  linarith

/--
For the source's `xi = 1` and `0 < epsilon ≤ 1` construction, the special
alternative has at least the welfare of every ordinary alternative.  This is
the concavity-of-sigmoid calculation needed to identify the numerator in
Eq. (11) with optimal welfare.
-/
theorem theorem3SpecialWelfare_ge_ordinaryWelfare
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_le_one : epsilon ≤ 1) :
    epsilon * theorem3OrdinaryTypeMass beta epsilon ≤ theorem3SpecialTypeMass beta epsilon := by
  have hargument : beta * epsilon ∈ Set.Icc 0 beta := by
    constructor
    · exact mul_nonneg hbeta.le hepsilon.le
    · nlinarith [mul_le_mul_of_nonneg_left hepsilon_le_one hbeta.le]
  have hchord := sigmoidChordSlope_mul_le_sigmoid_centered hbeta hargument
  have hraw :
      epsilon * (Real.sigmoid beta - (1 : ℝ) / 2) ≤
        Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2 := by
    calc
      epsilon * (Real.sigmoid beta - (1 : ℝ) / 2) =
          sigmoidChordSlope beta * (beta * epsilon) := by
            unfold sigmoidChordSlope
            field_simp [hbeta.ne']
      _ ≤ Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2 := hchord
  unfold theorem3SpecialTypeMass theorem3OrdinaryTypeMass
  simpa [mul_div_assoc] using
    (div_le_div_iff_of_pos_right (theorem3BalanceDenominator_pos hbeta hepsilon)).mpr hraw

/--
Finite ratio form of Appendix E.3 Eq. (11).  It is stated for an arbitrary
finite alternative set and source parameter `ξ ≥ 0`; the paper takes `ξ = 1`
for its one-comparison lower bound.
-/
theorem theorem3ManyAlternative_distortion_lower_bound_of_special_mass_le
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {beta epsilon xi q : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hxi : 0 ≤ xi) (special : Alternative) (policy : PMF Alternative)
    (hselection : (policy special).toReal ≤ q)
    (hdenominator : 0 < q * theorem3SpecialTypeMass beta epsilon +
      xi * epsilon * theorem3OrdinaryTypeMass beta epsilon)
    (hpolicy_welfare : 0 < policyAverageUtility
      (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon xi special) policy) :
    theorem3SpecialTypeMass beta epsilon /
        (q * theorem3SpecialTypeMass beta epsilon +
          xi * epsilon * theorem3OrdinaryTypeMass beta epsilon) ≤
      theorem3SpecialTypeMass beta epsilon /
        policyAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
          (theorem3ManyAlternativeUtility epsilon xi special) policy := by
  apply (div_le_div_iff₀ hdenominator hpolicy_welfare).mpr
  exact mul_le_mul_of_nonneg_left
    (theorem3ManyAlternative_policyAverageUtility_le_of_special_mass_le
      hbeta hepsilon hxi special policy hselection)
    (theorem3TypeMasses_nonneg hbeta hepsilon).1

/--
Finite behavioral-axiom bridge for the `d ≥ 2` branch of Appendix E.3. If an
empirical Condorcet-loser certificate fails with probability at most `η`, then
the source's probabilistic Condorcet-loser criterion bounds the unconditional
selection mass by `1 / m + η`; this yields the corresponding exact welfare
ratio. The separate sampling theorem must supply the stated certificate error.
-/
theorem theorem3_condorcet_loser_distortion_lower_bound
    {Observation Alternative : Type*} [Fintype Observation] [DecidableEq Observation]
    [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    (hcard : 2 ≤ Fintype.card Alternative)
    (observationLaw : PMF Observation) (rule : Observation → PMF Alternative)
    (isCondorcetLoser : Observation → Alternative → Prop)
    [∀ observation alternative, Decidable (isCondorcetLoser observation alternative)]
    {beta epsilon xi : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) (hxi : 1 < xi)
    (hcriterion : theorem3ProbabilisticCondorcetLoserCriterion rule isCondorcetLoser)
    (special : Alternative) (eta : ℝ)
    (hbad : AppliedModelingLib.pmfProb observationLaw
      (fun observation => ¬isCondorcetLoser observation special) ≤ eta)
    (heta_lt : eta < 1 - (Fintype.card Alternative : ℝ)⁻¹) :
    theorem3SpecialTypeMass beta epsilon /
        (((Fintype.card Alternative : ℝ)⁻¹ + eta) * theorem3SpecialTypeMass beta epsilon +
          xi * epsilon * theorem3OrdinaryTypeMass beta epsilon) ≤
      theorem3SpecialTypeMass beta epsilon /
        policyAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
          (theorem3ManyAlternativeUtility epsilon xi special)
          (theorem3ObservationSelectionLaw observationLaw rule) := by
  let policy := theorem3ObservationSelectionLaw observationLaw rule
  have hselection : (policy special).toReal ≤ (Fintype.card Alternative : ℝ)⁻¹ + eta := by
    exact theorem3_selectionMass_le_uniform_add_condorcetCertificateError
      observationLaw rule isCondorcetLoser hcriterion special eta hbad
  have heta_nonneg : 0 ≤ eta := by
    exact le_trans
      (AppliedModelingLib.pmfProb_nonneg observationLaw
        (fun observation => ¬isCondorcetLoser observation special)) hbad
  have hcard_real : (1 : ℝ) < (Fintype.card Alternative : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) hcard
  have hinv_nonneg : 0 ≤ (Fintype.card Alternative : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hpolicy_lt_one : (policy special).toReal < 1 := by
    linarith
  have hpolicy_pos : 0 < policyAverageUtility
      (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
      (theorem3ManyAlternativeUtility epsilon xi special) policy :=
    theorem3ManyAlternative_policyAverageUtility_pos_of_special_mass_lt_one
      hbeta hepsilon (by linarith) special policy hpolicy_lt_one
  have hdenominator_pos : 0 <
      ((Fintype.card Alternative : ℝ)⁻¹ + eta) * theorem3SpecialTypeMass beta epsilon +
        xi * epsilon * theorem3OrdinaryTypeMass beta epsilon := by
    have hordinary_pos : 0 < xi * epsilon * theorem3OrdinaryTypeMass beta epsilon := by
      exact mul_pos (mul_pos (by linarith) hepsilon)
        (theorem3TypeMasses_pos hbeta hepsilon).2
    have hfirst_nonneg : 0 ≤
        ((Fintype.card Alternative : ℝ)⁻¹ + eta) * theorem3SpecialTypeMass beta epsilon := by
      exact mul_nonneg (add_nonneg hinv_nonneg heta_nonneg)
        (theorem3TypeMasses_nonneg hbeta hepsilon).1
    linarith
  exact theorem3ManyAlternative_distortion_lower_bound_of_special_mass_le
    hbeta hepsilon (by linarith) special policy hselection hdenominator_pos hpolicy_pos

/--
Asymptotic fixed-instance form of the source's `d ≥ 2` Condorcet-loser
argument. Once the empirical certificate's failure probability converges to
zero, every sufficiently large sample horizon satisfies the displayed welfare
ratio with an arbitrarily small selection-mass slack.
-/
theorem theorem3_eventually_condorcet_loser_distortion_lower_bound
    {Observation : ℕ → Type*} {Alternative : Type*}
    [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    [∀ horizon, Fintype (Observation horizon)] [∀ horizon, DecidableEq (Observation horizon)]
    (hcard : 2 ≤ Fintype.card Alternative)
    (observationLaw : ∀ horizon, PMF (Observation horizon))
    (rule : ∀ horizon, Observation horizon → PMF Alternative)
    (isCondorcetLoser : ∀ horizon, Observation horizon → Alternative → Prop)
    [∀ horizon observation alternative,
      Decidable (isCondorcetLoser horizon observation alternative)]
    {beta epsilon xi : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) (hxi : 1 < xi)
    (hcriterion : ∀ horizon,
      theorem3ProbabilisticCondorcetLoserCriterion (rule horizon)
        (isCondorcetLoser horizon))
    (special : Alternative)
    (hcertificate : Filter.Tendsto
      (fun horizon => AppliedModelingLib.pmfProb (observationLaw horizon)
        (fun observation => ¬isCondorcetLoser horizon observation special))
      Filter.atTop (𝓝 0))
    (delta : ℝ) (hdelta : 0 < delta)
    (hdelta_lt : delta < 1 - (Fintype.card Alternative : ℝ)⁻¹) :
    ∀ᶠ horizon : ℕ in Filter.atTop,
      theorem3SpecialTypeMass beta epsilon /
          (((Fintype.card Alternative : ℝ)⁻¹ + delta) * theorem3SpecialTypeMass beta epsilon +
            xi * epsilon * theorem3OrdinaryTypeMass beta epsilon) ≤
        theorem3SpecialTypeMass beta epsilon /
          policyAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
            (theorem3ManyAlternativeUtility epsilon xi special)
            (theorem3ObservationSelectionLaw (observationLaw horizon) (rule horizon)) := by
  filter_upwards [hcertificate.eventually_lt_const hdelta] with horizon hfailure
  exact theorem3_condorcet_loser_distortion_lower_bound hcard
    (observationLaw horizon) (rule horizon) (isCondorcetLoser horizon)
    hbeta hepsilon hxi (hcriterion horizon) special delta (le_of_lt hfailure) hdelta_lt

/--
Finite source endpoint of Theorem 3 for one comparison per user.  For every
rule over a fixed finite alternative set of size at least two, one relabelling
of the Appendix-E.3 instance has the special alternative welfare-maximizing
and, along infinitely many horizons, achieves at least the displayed Eq. (11)
distortion ratio.
-/
theorem theorem3_finite_d1_distortion_lower_bound_core
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    [Nonempty Alternative]
    (hcard : 2 ≤ Fintype.card Alternative)
    (pairSampling : PMF (Alternative × Alternative))
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (hepsilon_upper : epsilon ≤ (1 : ℝ) / 2)
    (rule : ∀ horizon,
      (Fin horizon → ((Alternative × Alternative) × Bool)) → PMF Alternative) :
    ∃ special : Alternative,
      Set.Infinite {horizon : ℕ |
        let policy := theorem3ObservationSelectionLaw
          (theorem3ManyAlternativeObservationLaw pairSampling beta epsilon hbeta hepsilon
            special horizon)
          (rule horizon)
        (∀ alternative,
          populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
            (theorem3ManyAlternativeUtility epsilon 1 special) alternative ≤
            populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
              (theorem3ManyAlternativeUtility epsilon 1 special) special) ∧
          theorem3SpecialTypeMass beta epsilon /
              ((Fintype.card Alternative : ℝ)⁻¹ * theorem3SpecialTypeMass beta epsilon +
                epsilon * theorem3OrdinaryTypeMass beta epsilon) ≤
            theorem3SpecialTypeMass beta epsilon /
              policyAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
                (theorem3ManyAlternativeUtility epsilon 1 special) policy} := by
  obtain ⟨special, hlow⟩ := theorem3ManyAlternative_exists_fixed_low_selection_alternative
    pairSampling beta epsilon hbeta hepsilon rule
  refine ⟨special, hlow.mono ?_⟩
  intro horizon hselection
  dsimp
  constructor
  · intro alternative
    by_cases halternative : alternative = special
    · subst alternative
      exact le_rfl
    · calc
        populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
            (theorem3ManyAlternativeUtility epsilon 1 special) alternative =
            epsilon * theorem3OrdinaryTypeMass beta epsilon := by
              simpa using theorem3ManyAlternative_ordinary_averageUtility
                beta epsilon 1 hbeta hepsilon special alternative halternative
        _ ≤ theorem3SpecialTypeMass beta epsilon :=
          theorem3SpecialWelfare_ge_ordinaryWelfare hbeta hepsilon (by linarith)
        _ = populationAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
            (theorem3ManyAlternativeUtility epsilon 1 special) special := by
              symm
              exact theorem3ManyAlternative_special_averageUtility
                beta epsilon 1 hbeta hepsilon special
  · let policy := theorem3ObservationSelectionLaw
      (theorem3ManyAlternativeObservationLaw pairSampling beta epsilon hbeta hepsilon
        special horizon)
      (rule horizon)
    have hcard_real : (1 : ℝ) < (Fintype.card Alternative : ℝ) := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 1 < 2) hcard
    have hinv_lt_one : (Fintype.card Alternative : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ hcard_real
    have hpolicy_lt_one : (policy special).toReal < 1 :=
      lt_of_le_of_lt hselection hinv_lt_one
    have hpolicy_pos : 0 < policyAverageUtility
        (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
        (theorem3ManyAlternativeUtility epsilon 1 special) policy :=
      theorem3ManyAlternative_policyAverageUtility_pos_of_special_mass_lt_one
        hbeta hepsilon (by norm_num) special policy hpolicy_lt_one
    have hinv_nonneg : 0 ≤ (Fintype.card Alternative : ℝ)⁻¹ :=
      inv_nonneg.mpr (le_trans zero_le_one hcard_real.le)
    have hdenominator_pos :
        0 < (Fintype.card Alternative : ℝ)⁻¹ * theorem3SpecialTypeMass beta epsilon +
          epsilon * theorem3OrdinaryTypeMass beta epsilon := by
      have hspecial_nonneg := (theorem3TypeMasses_nonneg hbeta hepsilon).1
      have hordinary_term_pos : 0 < epsilon * theorem3OrdinaryTypeMass beta epsilon :=
        mul_pos hepsilon (theorem3TypeMasses_pos hbeta hepsilon).2
      nlinarith [mul_nonneg hinv_nonneg hspecial_nonneg]
    have hdenominator_pos' :
        0 < (Fintype.card Alternative : ℝ)⁻¹ * theorem3SpecialTypeMass beta epsilon +
          (1 : ℝ) * epsilon * theorem3OrdinaryTypeMass beta epsilon := by
      simpa using hdenominator_pos
    have hbound := theorem3ManyAlternative_distortion_lower_bound_of_special_mass_le
      hbeta hepsilon (by norm_num) special policy hselection hdenominator_pos' hpolicy_pos
    simpa using hbound

/--
Combined finite `d = 1` lower-bound core of Theorem 3.  For every randomized
rule, the source constructs a choice of the special alternative and infinitely
many sample horizons on which the rule puts at most uniform mass on it; on
those horizons the rule's expected welfare obeys the exact Eq. (11) bound.
-/
theorem theorem3_finite_d1_welfare_lower_bound_core
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    [Nonempty Alternative]
    (pairSampling : PMF (Alternative × Alternative))
    (beta epsilon : ℝ) (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (rule : ∀ horizon,
      (Fin horizon → ((Alternative × Alternative) × Bool)) → PMF Alternative) :
    ∃ special : Alternative,
      Set.Infinite {horizon : ℕ |
        let policy := theorem3ObservationSelectionLaw
          (theorem3ManyAlternativeObservationLaw pairSampling beta epsilon hbeta hepsilon
            special horizon)
          (rule horizon)
        (policy special).toReal ≤ (Fintype.card Alternative : ℝ)⁻¹ ∧
          policyAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
            (theorem3ManyAlternativeUtility epsilon 1 special) policy ≤
              (Fintype.card Alternative : ℝ)⁻¹ * theorem3SpecialTypeMass beta epsilon +
                epsilon * theorem3OrdinaryTypeMass beta epsilon} := by
  obtain ⟨special, hlow⟩ := theorem3ManyAlternative_exists_fixed_low_selection_alternative
    pairSampling beta epsilon hbeta hepsilon rule
  refine ⟨special, hlow.mono ?_⟩
  intro horizon hselection
  constructor
  · exact hselection
  · simpa using
      (theorem3ManyAlternative_policyAverageUtility_le_of_special_mass_le
        (xi := 1) hbeta hepsilon (by norm_num) special
        (theorem3ObservationSelectionLaw
          (theorem3ManyAlternativeObservationLaw pairSampling beta epsilon hbeta hepsilon
            special horizon)
          (rule horizon)) hselection)

/-- The simplified finite ratio displayed as Eq. (11) in Appendix E.3. -/
noncomputable def theorem3Eq11Ratio (beta epsilon selectionMass : ℝ) : ℝ :=
  (Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) /
    (selectionMass * (Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) +
      epsilon * (Real.sigmoid beta - (1 : ℝ) / 2))

/--
The population-mass ratio in the finite lower bound is exactly the source's
simplified Eq. (11) expression; the common two-type denominator cancels.
-/
theorem theorem3_massRatio_eq_eq11Ratio
    {beta epsilon selectionMass : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    theorem3SpecialTypeMass beta epsilon /
        (selectionMass * theorem3SpecialTypeMass beta epsilon +
          epsilon * theorem3OrdinaryTypeMass beta epsilon) =
      theorem3Eq11Ratio beta epsilon selectionMass := by
  unfold theorem3SpecialTypeMass theorem3OrdinaryTypeMass theorem3Eq11Ratio
  have hdenominator_ne := theorem3BalanceDenominator_ne hbeta hepsilon
  field_simp [hdenominator_ne]

/-- The first-order sigmoid limit used in the final `epsilon → 0` step of Eq. (11). -/
theorem theorem3_sigmoid_scaled_centered_slope_limit (beta : ℝ) :
    Filter.Tendsto
      (fun epsilon : ℝ => (Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) / epsilon)
      (𝓝[>] 0) (𝓝 (beta / 4)) := by
  have hderiv :
      HasDerivAt (fun epsilon : ℝ => Real.sigmoid (beta * epsilon))
        (Real.sigmoid 0 * (1 - Real.sigmoid 0) * beta) 0 := by
    simpa using
      (Real.hasDerivAt_sigmoid (beta * 0)).comp 0 (hasDerivAt_const_mul beta)
  convert hderiv.tendsto_slope_zero_right using 1
  · ext epsilon
    simp [smul_eq_mul, Real.sigmoid_zero, div_eq_mul_inv, mul_comm]
  · norm_num [Real.sigmoid_zero]
    ring

/--
The two-type Eq. (11) expression after the `m → ∞` step has the exact
right-hand `epsilon → 0` limit used by Theorem 3.
-/
theorem theorem3_eq11_epsilon_limit
    {beta : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        (Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) /
          (epsilon * (Real.sigmoid beta - (1 : ℝ) / 2)))
      (𝓝[>] 0)
      (𝓝 ((beta / 4) / (Real.sigmoid beta - (1 : ℝ) / 2))) := by
  let denominator : ℝ := Real.sigmoid beta - (1 : ℝ) / 2
  have hscale := (theorem3_sigmoid_scaled_centered_slope_limit beta).div_const denominator
  have hepsilon_pos : ∀ᶠ epsilon : ℝ in 𝓝[>] (0 : ℝ), 0 < epsilon :=
    self_mem_nhdsWithin
  apply hscale.congr'
  filter_upwards [hepsilon_pos] with epsilon hepsilon
  dsimp [denominator]
  field_simp [hepsilon.ne']

/-- The analytic coefficient in the source's displayed statement of Theorem 3. -/
theorem theorem3_eq11_limit_coefficient
    {beta : ℝ} (hbeta : 0 < beta) :
    (beta / 4) / (Real.sigmoid beta - (1 : ℝ) / 2) =
      beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) := by
  have hexp_pos : 0 < Real.exp (-beta) := Real.exp_pos _
  have hexp_lt_one : Real.exp (-beta) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hbeta)
  have hden_pos : 0 < 1 - Real.exp (-beta) := sub_pos.mpr hexp_lt_one
  have hsum_pos : 0 < 1 + Real.exp (-beta) := by linarith
  have hsigmoid :
      Real.sigmoid beta - (1 : ℝ) / 2 =
        (1 - Real.exp (-beta)) / (2 * (1 + Real.exp (-beta))) := by
    rw [Real.sigmoid_def]
    field_simp [hsum_pos.ne']
    ring
  rw [hsigmoid]
  field_simp [hden_pos.ne', hsum_pos.ne']
  ring

/-- The source coefficient is the checked limit of the `epsilon` part of Eq. (11). -/
theorem theorem3_eq11_epsilon_limit_source_coefficient
    {beta : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun epsilon : ℝ =>
        (Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) /
          (epsilon * (Real.sigmoid beta - (1 : ℝ) / 2)))
      (𝓝[>] 0)
      (𝓝 (beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)))) := by
  rw [← theorem3_eq11_limit_coefficient hbeta]
  exact theorem3_eq11_epsilon_limit hbeta

/--
The other limiting step in Eq. (11): as the permitted special-selection mass
goes to zero, its finite ratio tends to the zero-mass expression.
-/
theorem theorem3_eq11_selection_mass_limit
    (specialWelfare ordinaryWelfare : ℝ) (hordinary : ordinaryWelfare ≠ 0) :
    Filter.Tendsto
      (fun selectionMass : ℝ =>
        specialWelfare / (selectionMass * specialWelfare + ordinaryWelfare))
      (𝓝 0) (𝓝 (specialWelfare / ordinaryWelfare)) := by
  have hdenominator : ContinuousAt
      (fun selectionMass : ℝ => selectionMass * specialWelfare + ordinaryWelfare) 0 := by
    fun_prop
  have hdenominator_ne : 0 * specialWelfare + ordinaryWelfare ≠ 0 := by
    simpa using hordinary
  simpa using (continuousAt_const.div hdenominator hdenominator_ne).tendsto

/--
For fixed positive `epsilon`, the source Eq. (11) ratio tends to its
zero-selection-mass expression.  This is the `m → ∞` step after writing the
selection mass as `1 / m`.
-/
theorem theorem3_eq11_ratio_selectionMass_limit
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    Filter.Tendsto
      (fun selectionMass : ℝ => theorem3Eq11Ratio beta epsilon selectionMass)
      (𝓝 0)
      (𝓝 ((Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) /
        (epsilon * (Real.sigmoid beta - (1 : ℝ) / 2)))) := by
  unfold theorem3Eq11Ratio
  apply theorem3_eq11_selection_mass_limit
  exact ne_of_gt <| mul_pos hepsilon
    (sub_pos.mpr (by
      calc
        (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
        _ < Real.sigmoid beta := Real.sigmoid_lt hbeta))

/-- The `ε = 1 / m`, `ξ = 1 + ε` diagonal for the source's `d ≥ 2` branch. -/
noncomputable def theorem3D2DiagonalEpsilon (n : ℕ) : ℝ := ((n + 3 : ℕ) : ℝ)⁻¹

/-- The source's strict `ξ > 1` perturbation along the multi-comparison diagonal. -/
noncomputable def theorem3D2DiagonalXi (n : ℕ) : ℝ := 1 + theorem3D2DiagonalEpsilon n

/-- The finite source ratio with uniform mass plus `ε` certificate slack. -/
noncomputable def theorem3D2DiagonalRatio (beta epsilon : ℝ) : ℝ :=
  (Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) /
    (2 * epsilon * (Real.sigmoid (beta * epsilon) - (1 : ℝ) / 2) +
      (1 + epsilon) * epsilon * (Real.sigmoid beta - (1 : ℝ) / 2))

/-- The common source population denominator also cancels in the `d ≥ 2` ratio. -/
theorem theorem3_massRatio_eq_d2DiagonalRatio
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    theorem3SpecialTypeMass beta epsilon /
        (2 * epsilon * theorem3SpecialTypeMass beta epsilon +
          (1 + epsilon) * epsilon * theorem3OrdinaryTypeMass beta epsilon) =
      theorem3D2DiagonalRatio beta epsilon := by
  unfold theorem3SpecialTypeMass theorem3OrdinaryTypeMass theorem3D2DiagonalRatio
  have hdenominator_ne := theorem3BalanceDenominator_ne hbeta hepsilon
  field_simp [hdenominator_ne]

theorem theorem3D2DiagonalEpsilon_pos (n : ℕ) : 0 < theorem3D2DiagonalEpsilon n := by
  unfold theorem3D2DiagonalEpsilon
  positivity

theorem theorem3D2DiagonalEpsilon_lt_half (n : ℕ) :
    theorem3D2DiagonalEpsilon n < (1 : ℝ) / 2 := by
  unfold theorem3D2DiagonalEpsilon
  apply (inv_lt_iff_one_lt_mul₀ (by positivity)).mpr
  have hthree : (3 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by
    norm_cast
    omega
  nlinarith

theorem theorem3D2DiagonalXi_bounds (n : ℕ) :
    1 < theorem3D2DiagonalXi n ∧ theorem3D2DiagonalXi n < 2 := by
  unfold theorem3D2DiagonalXi
  constructor
  · linarith [theorem3D2DiagonalEpsilon_pos n]
  · linarith [theorem3D2DiagonalEpsilon_lt_half n]

/--
The multi-comparison diagonal ratio has the same limiting coefficient as the
source's Eq. (11): the `ξ - 1` and certificate-slack terms vanish with `ε`.
-/
theorem theorem3_d2_diagonal_ratio_limit
    {beta : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun n : ℕ => theorem3D2DiagonalRatio beta (theorem3D2DiagonalEpsilon n))
      Filter.atTop
      (𝓝 (beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)))) := by
  let epsilon : ℕ → ℝ := fun n => theorem3D2DiagonalEpsilon n
  have hepsilon : Filter.Tendsto epsilon Filter.atTop (𝓝 0) := by
    simpa only [epsilon, theorem3D2DiagonalEpsilon, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 3)))
  have hepsilon_pos : ∀ n : ℕ, 0 < epsilon n := by
    intro n
    exact theorem3D2DiagonalEpsilon_pos n
  have hepsilon_within : Filter.Tendsto epsilon Filter.atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within epsilon hepsilon
      (Filter.Eventually.of_forall hepsilon_pos)
  have hsource : Filter.Tendsto
      (fun n : ℕ =>
        (Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
          (epsilon n * (Real.sigmoid beta - (1 : ℝ) / 2)))
      Filter.atTop
      (𝓝 (beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)))) :=
    (theorem3_eq11_epsilon_limit_source_coefficient hbeta).comp hepsilon_within
  have harg : Filter.Tendsto (fun n : ℕ => beta * epsilon n) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hepsilon)
  have hcentered : Filter.Tendsto
      (fun n : ℕ => Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2)
      Filter.atTop (𝓝 0) := by
    have hsigmoid : Filter.Tendsto (fun n : ℕ => Real.sigmoid (beta * epsilon n))
        Filter.atTop (𝓝 (Real.sigmoid 0)) :=
      (continuous_sigmoid.continuousAt.tendsto).comp harg
    simpa [Real.sigmoid_zero] using hsigmoid.sub
      (tendsto_const_nhds (x := (1 : ℝ) / 2))
  have hscale_pos : 0 < Real.sigmoid beta - (1 : ℝ) / 2 := by
    apply sub_pos.mpr
    calc
      (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
      _ < Real.sigmoid beta := Real.sigmoid_lt hbeta
  have hdenominator : Filter.Tendsto
      (fun n : ℕ => 1 + epsilon n + 2 *
        (Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
          (Real.sigmoid beta - (1 : ℝ) / 2))
      Filter.atTop (𝓝 1) := by
    have hfirst : Filter.Tendsto (fun n : ℕ => 1 + epsilon n) Filter.atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hepsilon
    have hsecond : Filter.Tendsto (fun n : ℕ => 2 *
        (Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
          (Real.sigmoid beta - (1 : ℝ) / 2))
        Filter.atTop (𝓝 0) := by
      simpa using ((tendsto_const_nhds (x := (2 : ℝ))).mul hcentered).div_const
        (Real.sigmoid beta - (1 : ℝ) / 2)
    simpa using hfirst.add hsecond
  have hquotient : Filter.Tendsto
      (fun n : ℕ =>
        ((Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
          (epsilon n * (Real.sigmoid beta - (1 : ℝ) / 2))) /
          (1 + epsilon n + 2 *
            (Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
              (Real.sigmoid beta - (1 : ℝ) / 2)))
      Filter.atTop
      (𝓝 (beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)))) := by
    simpa using hsource.div hdenominator (by norm_num : (1 : ℝ) ≠ 0)
  refine hquotient.congr' ?_
  filter_upwards with n
  let B : ℝ := Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2
  let A : ℝ := Real.sigmoid beta - (1 : ℝ) / 2
  let e : ℝ := epsilon n
  have hB : 0 < B := by
    apply sub_pos.mpr
    calc
      (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
      _ < Real.sigmoid (beta * epsilon n) :=
        Real.sigmoid_lt (mul_pos hbeta (hepsilon_pos n))
  have hA : 0 < A := by simpa [A] using hscale_pos
  have he : 0 < e := by simpa [e] using hepsilon_pos n
  have hidentity :
      ((Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
          (epsilon n * (Real.sigmoid beta - (1 : ℝ) / 2))) /
          (1 + epsilon n + 2 *
            (Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
              (Real.sigmoid beta - (1 : ℝ) / 2)) =
        (Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
          (2 * epsilon n * (Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) +
            (1 + epsilon n) * epsilon n * (Real.sigmoid beta - (1 : ℝ) / 2)) := by
    change (B / (e * A)) / (1 + e + 2 * B / A) =
      B / (2 * e * B + (1 + e) * e * A)
    have hden : A + e * A + 2 * B ≠ 0 := by positivity
    field_simp [hA.ne', he.ne', hden]
    ring
  rw [hidentity]
  simp [epsilon, theorem3D2DiagonalRatio]

/--
Large-`m` `d ≥ 2` source conclusion, conditional only on the empirical
Condorcet-loser certificates that Appendix E.3 says converge in probability.
It permits arbitrary report spaces and arbitrary within-user correlations;
those are contained in the supplied certificate convergence hypothesis.
-/
theorem theorem3_d2_asymptotic_lower_bound_of_condorcetCertification
    {beta : ℝ} (hbeta : 0 < beta)
    {Observation : ∀ n : ℕ, ℕ → Type*}
    [∀ n horizon, Fintype (Observation n horizon)]
    [∀ n horizon, DecidableEq (Observation n horizon)]
    (observationLaw : ∀ n horizon, PMF (Observation n horizon))
    (rule : ∀ n horizon, Observation n horizon → PMF (Fin (n + 3)))
    (isCondorcetLoser : ∀ n horizon, Observation n horizon → Fin (n + 3) → Prop)
    [∀ n horizon observation alternative,
      Decidable (isCondorcetLoser n horizon observation alternative)]
    (hcriterion : ∀ n horizon,
      theorem3ProbabilisticCondorcetLoserCriterion (rule n horizon)
        (isCondorcetLoser n horizon))
    (hcertificate : ∀ n, Filter.Tendsto
      (fun horizon => AppliedModelingLib.pmfProb (observationLaw n horizon)
        (fun observation => ¬isCondorcetLoser n horizon observation (0 : Fin (n + 3))))
      Filter.atTop (𝓝 0))
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ᶠ horizon : ℕ in Filter.atTop,
      beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) - delta <
        theorem3SpecialTypeMass beta (theorem3D2DiagonalEpsilon n) /
          policyAverageUtility
            (theorem3TwoTypePopulation beta (theorem3D2DiagonalEpsilon n) hbeta
              (theorem3D2DiagonalEpsilon_pos n))
            (theorem3ManyAlternativeUtility (theorem3D2DiagonalEpsilon n)
              (theorem3D2DiagonalXi n) (0 : Fin (n + 3)))
            (theorem3ObservationSelectionLaw (observationLaw n horizon) (rule n horizon)) := by
  have hratio_eventually : ∀ᶠ n : ℕ in Filter.atTop,
      beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) - delta <
        theorem3D2DiagonalRatio beta (theorem3D2DiagonalEpsilon n) :=
    (theorem3_d2_diagonal_ratio_limit hbeta).eventually_const_lt (by linarith)
  rcases Filter.eventually_atTop.1 hratio_eventually with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  let epsilon : ℝ := theorem3D2DiagonalEpsilon n
  have hepsilon : 0 < epsilon := by
    simpa [epsilon] using theorem3D2DiagonalEpsilon_pos n
  have hcard : 2 ≤ Fintype.card (Fin (n + 3)) := by
    simp only [Fintype.card_fin]
    omega
  have hxi : 1 < theorem3D2DiagonalXi n := (theorem3D2DiagonalXi_bounds n).1
  have hslack_lt : epsilon < 1 - (Fintype.card (Fin (n + 3)) : ℝ)⁻¹ := by
    have hcard_inv : (Fintype.card (Fin (n + 3)) : ℝ)⁻¹ = epsilon := by
      simp [epsilon, theorem3D2DiagonalEpsilon]
    rw [hcard_inv]
    linarith [theorem3D2DiagonalEpsilon_lt_half n]
  have hfinite := theorem3_eventually_condorcet_loser_distortion_lower_bound
    hcard (observationLaw n) (rule n) (isCondorcetLoser n) hbeta hepsilon hxi
    (hcriterion n) (0 : Fin (n + 3)) (hcertificate n) epsilon hepsilon hslack_lt
  filter_upwards [hfinite] with horizon hhorizon
  have hratio :
      theorem3SpecialTypeMass beta epsilon /
          (2 * epsilon * theorem3SpecialTypeMass beta epsilon +
            (1 + epsilon) * epsilon * theorem3OrdinaryTypeMass beta epsilon) =
        theorem3D2DiagonalRatio beta epsilon :=
    theorem3_massRatio_eq_d2DiagonalRatio hbeta hepsilon
  have hbound : theorem3D2DiagonalRatio beta epsilon ≤
      theorem3SpecialTypeMass beta epsilon /
        policyAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
          (theorem3ManyAlternativeUtility epsilon (1 + epsilon) (0 : Fin (n + 3)))
          (theorem3ObservationSelectionLaw (observationLaw n horizon) (rule n horizon)) := by
    rw [← hratio]
    convert hhorizon using 1 <;>
      simp [epsilon, theorem3D2DiagonalXi, theorem3D2DiagonalEpsilon] <;> ring
  calc
    beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) - delta <
        theorem3D2DiagonalRatio beta epsilon := by simpa [epsilon] using hN n hn
    _ ≤ theorem3SpecialTypeMass beta epsilon /
        policyAverageUtility (theorem3TwoTypePopulation beta epsilon hbeta hepsilon)
          (theorem3ManyAlternativeUtility epsilon (1 + epsilon) (0 : Fin (n + 3)))
          (theorem3ObservationSelectionLaw (observationLaw n horizon) (rule n horizon)) := hbound
    _ = theorem3SpecialTypeMass beta (theorem3D2DiagonalEpsilon n) /
        policyAverageUtility
          (theorem3TwoTypePopulation beta (theorem3D2DiagonalEpsilon n) hbeta
            (theorem3D2DiagonalEpsilon_pos n))
          (theorem3ManyAlternativeUtility (theorem3D2DiagonalEpsilon n)
            (theorem3D2DiagonalXi n) (0 : Fin (n + 3)))
          (theorem3ObservationSelectionLaw (observationLaw n horizon) (rule n horizon)) := by
            simp [epsilon, theorem3D2DiagonalXi]

/-- The concrete `ε = 1 / m` diagonal used to take the source's Eq. (11) limit. -/
noncomputable def theorem3DiagonalEpsilon (n : ℕ) : ℝ := ((n + 2 : ℕ) : ℝ)⁻¹

theorem theorem3DiagonalEpsilon_pos (n : ℕ) : 0 < theorem3DiagonalEpsilon n := by
  unfold theorem3DiagonalEpsilon
  positivity

theorem theorem3DiagonalEpsilon_le_half (n : ℕ) :
    theorem3DiagonalEpsilon n ≤ (1 : ℝ) / 2 := by
  unfold theorem3DiagonalEpsilon
  apply (inv_le_iff_one_le_mul₀ (by positivity)).mpr
  have htwo : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
    norm_cast
    omega
  nlinarith

/--
The literal diagonal family `m = n + 2`, `epsilon = 1 / (n + 2)` used in
Appendix E.3 has the source's limiting Eq. (11) coefficient.  This packages
the two limiting displays into one concrete growing-alternative family.
-/
theorem theorem3_eq11_diagonal_limit
    {beta : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun n : ℕ => theorem3Eq11Ratio beta (((n + 2 : ℕ) : ℝ)⁻¹)
        (((n + 2 : ℕ) : ℝ)⁻¹))
      Filter.atTop
      (𝓝 (beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)))) := by
  let epsilon : ℕ → ℝ := fun n => (((n + 2 : ℕ) : ℝ)⁻¹)
  have hepsilon : Filter.Tendsto epsilon Filter.atTop (𝓝 0) := by
    simpa only [epsilon, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 2)))
  have hepsilon_pos : ∀ n : ℕ, 0 < epsilon n := by
    intro n
    dsimp [epsilon]
    positivity
  have hepsilon_within : Filter.Tendsto epsilon Filter.atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within epsilon hepsilon
      (Filter.Eventually.of_forall hepsilon_pos)
  have hsource : Filter.Tendsto
      (fun n : ℕ =>
        (Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
          (epsilon n * (Real.sigmoid beta - (1 : ℝ) / 2)))
      Filter.atTop
      (𝓝 (beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)))) :=
    (theorem3_eq11_epsilon_limit_source_coefficient hbeta).comp hepsilon_within
  have harg : Filter.Tendsto (fun n : ℕ => beta * epsilon n) Filter.atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hepsilon)
  have hcentered : Filter.Tendsto
      (fun n : ℕ => Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2)
      Filter.atTop (𝓝 0) := by
    have hsigmoid : Filter.Tendsto (fun n : ℕ => Real.sigmoid (beta * epsilon n))
        Filter.atTop (𝓝 (Real.sigmoid 0)) :=
      (continuous_sigmoid.continuousAt.tendsto).comp harg
    simpa [Real.sigmoid_zero] using hsigmoid.sub
      (tendsto_const_nhds (x := (1 : ℝ) / 2))
  have hscale_pos : 0 < Real.sigmoid beta - (1 : ℝ) / 2 := by
    apply sub_pos.mpr
    calc
      (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
      _ < Real.sigmoid beta := Real.sigmoid_lt hbeta
  have hdenominator : Filter.Tendsto
      (fun n : ℕ => 1 +
        (Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
          (Real.sigmoid beta - (1 : ℝ) / 2))
      Filter.atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
      (hcentered.div_const (Real.sigmoid beta - (1 : ℝ) / 2))
  have hquotient : Filter.Tendsto
      (fun n : ℕ =>
        ((Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
          (epsilon n * (Real.sigmoid beta - (1 : ℝ) / 2))) /
          (1 + (Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
            (Real.sigmoid beta - (1 : ℝ) / 2)))
      Filter.atTop
      (𝓝 (beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)))) := by
    simpa using hsource.div hdenominator (by norm_num : (1 : ℝ) ≠ 0)
  refine hquotient.congr' ?_
  filter_upwards with n
  have hcentered_pos : 0 < Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2 := by
    apply sub_pos.mpr
    calc
      (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
      _ < Real.sigmoid (beta * epsilon n) :=
        Real.sigmoid_lt (mul_pos hbeta (hepsilon_pos n))
  have hsum_pos : 0 <
      Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2 +
        (Real.sigmoid beta - (1 : ℝ) / 2) := by
    linarith
  let B : ℝ := Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2
  let A : ℝ := Real.sigmoid beta - (1 : ℝ) / 2
  let e : ℝ := epsilon n
  have hA : 0 < A := by simpa [A] using hscale_pos
  have he : 0 < e := by simpa [e] using hepsilon_pos n
  have hBA : 0 < B + A := by simpa [B, A] using hsum_pos
  have hidentity :
      ((Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
          (epsilon n * (Real.sigmoid beta - (1 : ℝ) / 2))) /
          (1 + (Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
            (Real.sigmoid beta - (1 : ℝ) / 2)) =
        (Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) /
          (epsilon n * (Real.sigmoid (beta * epsilon n) - (1 : ℝ) / 2) +
            epsilon n * (Real.sigmoid beta - (1 : ℝ) / 2)) := by
    change (B / (e * A)) / (1 + B / A) = B / (e * B + e * A)
    have hAB : A + B ≠ 0 := by linarith
    field_simp [hA.ne', he.ne', hBA.ne', hAB]
    ring
  rw [hidentity]
  simp [epsilon, theorem3Eq11Ratio]

/--
The source's growing-alternative family for the `d = 1` branch of Theorem 3.
For each `m = n + 2`, it instantiates the finite indistinguishability argument
at `ε = 1 / m`; the exact Eq. (11) lower bound holds along infinitely many
sample horizons for every member of the supplied family of voting rules.
-/
theorem theorem3_d1_diagonal_family_lower_bound
    {beta : ℝ} (hbeta : 0 < beta)
    (pairSampling : ∀ n : ℕ, PMF (Fin (n + 2) × Fin (n + 2)))
    (rule : ∀ n horizon,
      (Fin horizon → ((Fin (n + 2) × Fin (n + 2)) × Bool)) → PMF (Fin (n + 2))) :
    ∀ n : ℕ, ∃ special : Fin (n + 2),
      Set.Infinite {horizon : ℕ |
        let policy := theorem3ObservationSelectionLaw
          (theorem3ManyAlternativeObservationLaw (pairSampling n) beta
            (theorem3DiagonalEpsilon n) hbeta (theorem3DiagonalEpsilon_pos n)
            special horizon)
          (rule n horizon)
        (∀ alternative,
          populationAverageUtility
            (theorem3TwoTypePopulation beta (theorem3DiagonalEpsilon n) hbeta
              (theorem3DiagonalEpsilon_pos n))
            (theorem3ManyAlternativeUtility (theorem3DiagonalEpsilon n) 1 special) alternative ≤
            populationAverageUtility
              (theorem3TwoTypePopulation beta (theorem3DiagonalEpsilon n) hbeta
                (theorem3DiagonalEpsilon_pos n))
              (theorem3ManyAlternativeUtility (theorem3DiagonalEpsilon n) 1 special) special) ∧
          theorem3Eq11Ratio beta (theorem3DiagonalEpsilon n) (theorem3DiagonalEpsilon n) ≤
            theorem3SpecialTypeMass beta (theorem3DiagonalEpsilon n) /
              policyAverageUtility
                (theorem3TwoTypePopulation beta (theorem3DiagonalEpsilon n) hbeta
                  (theorem3DiagonalEpsilon_pos n))
                (theorem3ManyAlternativeUtility (theorem3DiagonalEpsilon n) 1 special) policy} := by
  intro n
  have hcard : 2 ≤ Fintype.card (Fin (n + 2)) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨special, hspecial⟩ := theorem3_finite_d1_distortion_lower_bound_core
    hcard (pairSampling n) beta (theorem3DiagonalEpsilon n) hbeta
    (theorem3DiagonalEpsilon_pos n) (theorem3DiagonalEpsilon_le_half n) (rule n)
  refine ⟨special, hspecial.mono ?_⟩
  intro horizon hsource
  dsimp at hsource ⊢
  constructor
  · exact hsource.1
  · rw [← theorem3_massRatio_eq_eq11Ratio hbeta (theorem3DiagonalEpsilon_pos n)]
    simpa [theorem3DiagonalEpsilon] using hsource.2

/--
The asymptotic `d = 1` lower-bound form asserted in Theorem 3.  Given a
positive tolerance, the source's Eq. (11) construction yields, at every
sufficiently large alternative-set size, a welfare-maximizing hidden special
alternative and infinitely many sample horizons whose distortion is within
that tolerance below the stated coefficient.
-/
theorem theorem3_d1_asymptotic_lower_bound
    {beta : ℝ} (hbeta : 0 < beta)
    (pairSampling : ∀ n : ℕ, PMF (Fin (n + 2) × Fin (n + 2)))
    (rule : ∀ n horizon,
      (Fin horizon → ((Fin (n + 2) × Fin (n + 2)) × Bool)) → PMF (Fin (n + 2)))
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ special : Fin (n + 2),
      Set.Infinite {horizon : ℕ |
        let policy := theorem3ObservationSelectionLaw
          (theorem3ManyAlternativeObservationLaw (pairSampling n) beta
            (theorem3DiagonalEpsilon n) hbeta (theorem3DiagonalEpsilon_pos n)
            special horizon)
          (rule n horizon)
        (∀ alternative,
          populationAverageUtility
            (theorem3TwoTypePopulation beta (theorem3DiagonalEpsilon n) hbeta
              (theorem3DiagonalEpsilon_pos n))
            (theorem3ManyAlternativeUtility (theorem3DiagonalEpsilon n) 1 special) alternative ≤
            populationAverageUtility
              (theorem3TwoTypePopulation beta (theorem3DiagonalEpsilon n) hbeta
                (theorem3DiagonalEpsilon_pos n))
              (theorem3ManyAlternativeUtility (theorem3DiagonalEpsilon n) 1 special) special) ∧
          beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) - delta <
            theorem3SpecialTypeMass beta (theorem3DiagonalEpsilon n) /
              policyAverageUtility
                (theorem3TwoTypePopulation beta (theorem3DiagonalEpsilon n) hbeta
                  (theorem3DiagonalEpsilon_pos n))
                (theorem3ManyAlternativeUtility (theorem3DiagonalEpsilon n) 1 special) policy} := by
  have heventually : ∀ᶠ n : ℕ in Filter.atTop,
      beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) - delta <
        theorem3Eq11Ratio beta (theorem3DiagonalEpsilon n) (theorem3DiagonalEpsilon n) := by
    simpa [theorem3DiagonalEpsilon] using
      (theorem3_eq11_diagonal_limit hbeta).eventually_const_lt (by linarith)
  rcases Filter.eventually_atTop.1 heventually with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨special, hspecial⟩ :=
    theorem3_d1_diagonal_family_lower_bound hbeta pairSampling rule n
  refine ⟨special, hspecial.mono ?_⟩
  intro horizon hsource
  constructor
  · exact hsource.1
  · exact lt_of_lt_of_le (hN n hn) hsource.2

end GolzHaghtalabYang2025Distortion
