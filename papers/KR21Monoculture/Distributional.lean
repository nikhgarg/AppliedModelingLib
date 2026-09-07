import KR21Monoculture.Theorem1
import AppliedModelingLib.Foundations.Probability.MeasureInequalities

open AppliedModelingLib MeasureTheory

namespace KR21Monoculture

/-!
# The outer candidate-value distribution in KR21

The paper first draws a candidate-value profile from a joint distribution `D`
and then draws rankings conditional on that profile.  The earlier development
fixed the value profile pointwise.  This file restores the outer draw without
changing any of the finite-ranking proofs: `pointFamily` is the conditional
family to which those proofs apply, while the paper's utilities are their
integrals with respect to `D`.

The same algorithm accuracy must work for the whole distribution.  In
particular, `DistributionalTheorem1Target` puts the existential quantifier over
`thetaA` *outside* the integral; it is intentionally stronger than choosing a
different witness for each value profile.
-/

/-- A joint profile of the candidates' cardinal values. -/
abbrev ValueProfile (n : ℕ) := Candidate n → ℝ

/-- A ranking family conditional on the realized candidate-value profile. -/
structure DistributionalAccuracyFamily (n : ℕ) where
  dist : ℝ → ValueProfile n → PMF (Ranking n)

namespace DistributionalAccuracyFamily

/-- The fixed-value family obtained after conditioning on a value profile. -/
noncomputable def pointFamily {n : ℕ} (F : DistributionalAccuracyFamily n)
    (value : ValueProfile n) : AccuracyFamily n where
  dist := fun theta => F.dist theta value
  value := value

/-- Integrate a conditional payoff over the source's outer distribution `D`. -/
noncomputable def outerExpected {n : ℕ} (D : Measure (ValueProfile n))
    (u : ValueProfile n → ℝ) : ℝ := ∫ value, u value ∂D

/-- Source proof notation `f(thetaA)`, now including the outer draw from `D`. -/
noncomputable def theorem1_f {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (thetaA thetaH : ℝ) : ℝ :=
  outerExpected D (fun value =>
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.algorithm) +
    outerExpected D (fun value =>
      Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.algorithm Strategy.algorithm)

/-- Source proof notation `g(thetaA)`, now including the outer draw from `D`. -/
noncomputable def theorem1_g {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (thetaA thetaH : ℝ) : ℝ :=
  outerExpected D (fun value =>
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.human) +
    outerExpected D (fun value =>
      Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.algorithm Strategy.human)

/-- Source proof notation `h(thetaA)`, now including the outer draw from `D`. -/
noncomputable def theorem1_h {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (thetaA thetaH : ℝ) : ℝ :=
  outerExpected D (fun value =>
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.human) +
    outerExpected D (fun value =>
      Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.human Strategy.human)

/-- The algorithm-against-human payoff, including the outer draw from `D`. -/
noncomputable def theorem1_algorithmAgainstHuman {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (thetaA thetaH : ℝ) : ℝ :=
  outerExpected D (fun value =>
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.algorithm) +
    outerExpected D (fun value =>
      Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.human Strategy.algorithm)

/--
Definition 2 with its source quantifier order: utilities are first averaged over
the joint value distribution and the independent reranking must improve that
single ex-ante payoff.
-/
noncomputable def PrefersIndependentReranking {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) : Prop :=
  outerExpected D (fun value =>
      expectedSecondMoverShared (F.dist theta value) value) <
    outerExpected D (fun value =>
      expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value)

/--
Definition 3 with its source quantifier order: a human evaluator has higher
ex-ante second-mover utility against a human than against the more accurate
algorithm.
-/
noncomputable def PrefersWeakerCompetition {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (thetaA thetaH : ℝ) : Prop :=
  outerExpected D (fun value =>
      expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaA value) value) <
    outerExpected D (fun value =>
      expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaH value) value)

/-- Pointwise Definition 2 implies its distributional form when both payoffs are integrable. -/
theorem prefersIndependentReranking_of_pointwise {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    [IsProbabilityMeasure D] (theta : ℝ)
    (hshared : Integrable
      (fun value => expectedSecondMoverShared (F.dist theta value) value) D)
    (hindependent : Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) D)
    (hpoint : ∀ value,
      Model.PrefersIndependentReranking (F.dist theta value) value) :
    F.PrefersIndependentReranking D theta := by
  unfold PrefersIndependentReranking outerExpected
  exact integral_lt_integral_of_forall_lt D hshared hindependent fun value =>
    hpoint value

/-- Pointwise Definition 3 implies its distributional form when both payoffs are integrable. -/
theorem prefersWeakerCompetition_of_pointwise {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    [IsProbabilityMeasure D] (thetaA thetaH : ℝ)
    (hbetter : Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaA value) value) D)
    (hworse : Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaH value) value) D)
    (hpoint : ∀ value,
      Model.PrefersWeakerCompetition
        (F.dist thetaA value) (F.dist thetaH value) value) :
    F.PrefersWeakerCompetition D thetaA thetaH := by
  unfold PrefersWeakerCompetition outerExpected
  exact integral_lt_integral_of_forall_lt D hbetter hworse fun value =>
    hpoint value

/-- Definition 2 is exactly the initial `f < g` comparison at equal accuracy. -/
theorem theorem1_f_lt_g_of_prefersIndependent {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (h : F.PrefersIndependentReranking D theta) :
    F.theorem1_f D theta theta < F.theorem1_g D theta theta := by
  simpa [PrefersIndependentReranking, theorem1_f, theorem1_g, outerExpected,
    pointFamily,
    AccuracyFamily.modelAt, Model.firstMoverEU, Model.secondMoverEU,
    Model.rankingDist] using h

/-- Definition 3 is exactly the `g < h` comparison above human accuracy. -/
theorem theorem1_g_lt_h_of_prefersWeakerCompetition {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (thetaA thetaH : ℝ) (h : F.PrefersWeakerCompetition D thetaA thetaH) :
    F.theorem1_g D thetaA thetaH < F.theorem1_h D thetaA thetaH := by
  simpa [PrefersWeakerCompetition, theorem1_g, theorem1_h, outerExpected,
    pointFamily,
    AccuracyFamily.modelAt, Model.firstMoverEU, Model.secondMoverEU,
    Model.rankingDist] using h

/-- The all-human expression is constant as the algorithm accuracy varies. -/
theorem theorem1_h_const {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (thetaA thetaA' thetaH : ℝ) :
    F.theorem1_h D thetaA thetaH = F.theorem1_h D thetaA' thetaH := by
  rfl

/--
The distributional Theorem 1 conclusion.  One common `thetaA` gives both strict
dominance inequalities and makes all-human welfare exceed all-algorithm welfare.
-/
noncomputable def DistributionalTheorem1Target {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (thetaH : ℝ) : Prop :=
  ∃ thetaA, thetaH < thetaA ∧
    F.theorem1_g D thetaA thetaH < F.theorem1_f D thetaA thetaH ∧
    F.theorem1_h D thetaA thetaH <
      F.theorem1_algorithmAgainstHuman D thetaA thetaH ∧
    F.theorem1_f D thetaA thetaH < F.theorem1_h D thetaA thetaH

/--
The analytic regularity used when the source's finite conditional payoffs are
averaged over `D`.  The continuity fields are the minor dominated-continuity
assumption implicit in the paper's crossing argument; they do not alter the
economic assumptions in Definitions 2 and 3.
-/
structure DistributionalTheorem1Assumptions {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (thetaH : ℝ) : Type where
  prefers_independent_at_equal : F.PrefersIndependentReranking D thetaH
  f_continuity : ∀ theta, thetaH ≤ theta →
    EpsilonContinuousAt (fun thetaA => F.theorem1_f D thetaA thetaH) theta
  g_continuity : ∀ theta, thetaH ≤ theta →
    EpsilonContinuousAt (fun thetaA => F.theorem1_g D thetaA thetaH) theta
  asymptotic_first_dominance : ∀ lower, thetaH < lower →
    ∃ hi, lower < hi ∧
      F.theorem1_g D hi thetaH < F.theorem1_f D hi thetaH
  prefers_weaker_above : ∀ thetaA, thetaH < thetaA →
    F.PrefersWeakerCompetition D thetaA thetaH
  algorithm_against_human_above : ∀ thetaA, thetaH < thetaA →
    F.theorem1_h D thetaA thetaH <
      F.theorem1_algorithmAgainstHuman D thetaA thetaH

/--
Paper Theorem 1 with the source's outer value distribution restored.  The proof
uses one scalar crossing of the already-averaged payoffs, hence produces one
algorithm accuracy common to every realization of `D`.
-/
theorem distributional_theorem1 {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (thetaH : ℝ) (assumptions : DistributionalTheorem1Assumptions F D thetaH) :
    F.DistributionalTheorem1Target D thetaH := by
  have hinitial :
      F.theorem1_f D thetaH thetaH < F.theorem1_g D thetaH thetaH :=
    theorem1_f_lt_g_of_prefersIndependent
      F D thetaH assumptions.prefers_independent_at_equal
  rcases exists_right_radius_lt_of_epsilonContinuousAt
      (assumptions.f_continuity thetaH le_rfl)
      (assumptions.g_continuity thetaH le_rfl) hinitial with
    ⟨initialRadius, hinitialRadius, hpersistInitial⟩
  let lo := thetaH + initialRadius / 2
  have hthetaH_lo : thetaH < lo := by
    dsimp [lo]
    linarith
  have hf_lt_g_lo : F.theorem1_f D lo thetaH < F.theorem1_g D lo thetaH := by
    apply hpersistInitial
    · exact hthetaH_lo
    · dsimp [lo]
      linarith
  rcases assumptions.asymptotic_first_dominance lo hthetaH_lo with
    ⟨hi, hlo_hi, hg_lt_f_hi⟩
  have hdiff_continuous :
      ContinuousOn
        (fun thetaA => F.theorem1_f D thetaA thetaH -
          F.theorem1_g D thetaA thetaH) (Set.Icc lo hi) :=
    continuousOn_of_forall_epsilonContinuousAt fun theta htheta =>
      epsilonContinuousAt_sub
        (assumptions.f_continuity theta
          (le_trans (le_of_lt hthetaH_lo) htheta.1))
        (assumptions.g_continuity theta
          (le_trans (le_of_lt hthetaH_lo) htheta.1))
  have hlo_nonpos :
      F.theorem1_f D lo thetaH - F.theorem1_g D lo thetaH ≤ 0 := by
    linarith
  have hhi_pos :
      0 < F.theorem1_f D hi thetaH - F.theorem1_g D hi thetaH := by
    linarith
  rcases exists_last_nonpos_with_right_pos_on_Icc
      (d := fun thetaA => F.theorem1_f D thetaA thetaH -
        F.theorem1_g D thetaA thetaH)
      hlo_hi hdiff_continuous hlo_nonpos hhi_pos with
    ⟨thetaStar, hlo_star, hstar_hi, hdiff_nonpos, hright_pos⟩
  have hthetaH_star : thetaH < thetaStar := hthetaH_lo.trans_le hlo_star
  have hf_lt_h_star :
      F.theorem1_f D thetaStar thetaH < F.theorem1_h D thetaStar thetaH := by
    have hfg :
        F.theorem1_f D thetaStar thetaH ≤ F.theorem1_g D thetaStar thetaH := by
      linarith
    exact hfg.trans_lt
      (theorem1_g_lt_h_of_prefersWeakerCompetition F D thetaStar thetaH
        (assumptions.prefers_weaker_above thetaStar hthetaH_star))
  have hh_continuity :
      EpsilonContinuousAt (fun thetaA => F.theorem1_h D thetaA thetaH) thetaStar := by
    intro epsilon hepsilon
    refine ⟨1, zero_lt_one, ?_⟩
    intro theta _
    change |F.theorem1_h D theta thetaH -
      F.theorem1_h D thetaStar thetaH| < epsilon
    rw [theorem1_h_const F D theta thetaStar thetaH]
    simpa using hepsilon
  rcases exists_right_radius_lt_of_epsilonContinuousAt
      (assumptions.f_continuity thetaStar
        (le_trans (le_of_lt hthetaH_lo) hlo_star))
      hh_continuity hf_lt_h_star with
    ⟨welfareRadius, hwelfareRadius, hpersistWelfare⟩
  let radius := min ((hi - thetaStar) / 2) welfareRadius
  have hradius : 0 < radius := by
    dsimp [radius]
    exact lt_min (by linarith) hwelfareRadius
  let thetaA := thetaStar + radius / 2
  have hstar_thetaA : thetaStar < thetaA := by
    dsimp [thetaA]
    linarith
  have hthetaH_thetaA : thetaH < thetaA := hthetaH_star.trans hstar_thetaA
  have hthetaA_hi : thetaA ≤ hi := by
    have hradius_le : radius ≤ (hi - thetaStar) / 2 := by
      dsimp [radius]
      exact min_le_left _ _
    dsimp [thetaA]
    linarith
  have hthetaA_welfare : thetaA < thetaStar + welfareRadius := by
    have hradius_le : radius ≤ welfareRadius := by
      dsimp [radius]
      exact min_le_right _ _
    dsimp [thetaA]
    linarith
  refine ⟨thetaA, hthetaH_thetaA, ?_, ?_, ?_⟩
  · have hpos := hright_pos thetaA hstar_thetaA hthetaA_hi
    linarith
  · exact assumptions.algorithm_against_human_above thetaA hthetaH_thetaA
  · exact hpersistWelfare thetaA hstar_thetaA hthetaA_welfare

end DistributionalAccuracyFamily
end KR21Monoculture
