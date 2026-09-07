import KR21Monoculture.MainTheorems
import KR21Monoculture.ThreeCandidateValueProfile

open AppliedModelingLib MeasureTheory

namespace KR21Monoculture

/-!
# Theorem 2 with the outer candidate distribution

The existing Gaussian and Laplace source proofs are conditional on one fixed
three-candidate value profile.  The paper's Theorem 2 quantifies over a joint
distribution `D` of profiles.  This file applies the proved conditional
comparisons at every realization and integrates them.  Integrability is stated
explicitly; it is the minimal regularity needed for the source expectations to
exist.
-/

/-- Gaussian RUM ranking law at source accuracy `theta` (standard deviation `1/theta`). -/
noncomputable def gaussianThreeCandidateRankingLaw
    (theta x1 x2 x3 : ℝ) : PMF (Ranking 1) :=
  rumRankingPMFOfMeasure
    (theorem8GaussianDefinition2ScoreMeasureStd (1 / theta) x1 x2 x3)
    (rum3RankByScoreFns
      theorem8GaussianDefinition2Score1
      theorem8GaussianDefinition2Score2
      theorem8GaussianDefinition2Score3)
    (rum3RankByScoreFns_measurable
      theorem8GaussianDefinition2Score1_measurable
      theorem8GaussianDefinition2Score2_measurable
      theorem8GaussianDefinition2Score3_measurable)

/-- Fixed-profile Gaussian accuracy family used to invoke the proved conditional source theorem. -/
noncomputable def gaussianThreeCandidateAccuracyFamily
    (x1 x2 x3 : ℝ) : AccuracyFamily 1 where
  dist := fun theta => gaussianThreeCandidateRankingLaw theta x1 x2 x3
  value := threeCandidateValueProfile x1 x2 x3

/-- Conditional Gaussian Definition 2 endpoint in notation suited to outer integration. -/
theorem gaussianThreeCandidate_prefersIndependent
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersIndependentReranking
      (gaussianThreeCandidateRankingLaw theta x1 x2 x3)
      (threeCandidateValueProfile x1 x2 x3) := by
  exact
    MallowsComparison.paper_definition2_threeCandidate_gaussianStd_prefersIndependentReranking
      (σ := 1 / theta) (x1 := x1) (x2 := x2) (x3 := x3)
      (value := threeCandidateValueProfile x1 x2 x3)
      (one_div_pos.mpr htheta)
      (by simp [threeCandidateValueProfile, hx12])
      (by simp [threeCandidateValueProfile, hx23])
      hx12 hx23

/-- Conditional Gaussian Definition 3 endpoint in notation suited to outer integration. -/
theorem gaussianThreeCandidate_prefersWeaker
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (gaussianThreeCandidateRankingLaw thetaA x1 x2 x3)
      (gaussianThreeCandidateRankingLaw thetaH x1 x2 x3)
      (threeCandidateValueProfile x1 x2 x3) := by
  let F := gaussianThreeCandidateAccuracyFamily x1 x2 x3
  have hsource :=
    paper_theorem2_gaussianStd_prefersWeakerCompetition_of_rum_source
      (F := F) (x1 := x1) (x2 := x2) (x3 := x3)
      (by simp [F, gaussianThreeCandidateAccuracyFamily,
        threeCandidateValueProfile])
      (by simp [F, gaussianThreeCandidateAccuracyFamily,
        threeCandidateValueProfile])
      (by simp [F, gaussianThreeCandidateAccuracyFamily,
        threeCandidateValueProfile])
      hx12 hx23
      (by
        intro theta htheta
        rfl)
  exact hsource thetaA thetaH hthetaH hthetaHA

/--
Paper Theorem 2, Gaussian part, for an arbitrary outer probability law `D` on
three-candidate value draws.  The conclusion is exactly Definitions 2 and 3
after averaging over `D`.
-/
theorem theorem2_gaussian_with_outer_value_distribution
    {Omega : Type*} [MeasurableSpace Omega]
    (D : Measure Omega) [IsProbabilityMeasure D]
    (x1 x2 x3 : Omega → ℝ)
    (horder12 : ∀ omega, x2 omega < x1 omega)
    (horder23 : ∀ omega, x3 omega < x2 omega)
    (hshared : ∀ theta, 0 < theta → Integrable (fun omega =>
      expectedSecondMoverShared
        (gaussianThreeCandidateRankingLaw theta
          (x1 omega) (x2 omega) (x3 omega))
        (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega))) D)
    (hindependent : ∀ theta, 0 < theta → Integrable (fun omega =>
      expectedSecondMoverIndependent
        (gaussianThreeCandidateRankingLaw theta
          (x1 omega) (x2 omega) (x3 omega))
        (gaussianThreeCandidateRankingLaw theta
          (x1 omega) (x2 omega) (x3 omega))
        (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega))) D)
    (hbetter : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun omega =>
        expectedSecondMoverIndependent
          (gaussianThreeCandidateRankingLaw thetaH
            (x1 omega) (x2 omega) (x3 omega))
          (gaussianThreeCandidateRankingLaw thetaA
            (x1 omega) (x2 omega) (x3 omega))
          (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega))) D)
    (hworse : ∀ thetaH, 0 < thetaH → Integrable (fun omega =>
      expectedSecondMoverIndependent
        (gaussianThreeCandidateRankingLaw thetaH
          (x1 omega) (x2 omega) (x3 omega))
        (gaussianThreeCandidateRankingLaw thetaH
          (x1 omega) (x2 omega) (x3 omega))
        (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega))) D) :
    (∀ theta, 0 < theta →
      (∫ omega, expectedSecondMoverShared
          (gaussianThreeCandidateRankingLaw theta
            (x1 omega) (x2 omega) (x3 omega))
          (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega)) ∂D) <
        ∫ omega, expectedSecondMoverIndependent
          (gaussianThreeCandidateRankingLaw theta
            (x1 omega) (x2 omega) (x3 omega))
          (gaussianThreeCandidateRankingLaw theta
            (x1 omega) (x2 omega) (x3 omega))
          (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega)) ∂D) ∧
    (∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∫ omega, expectedSecondMoverIndependent
          (gaussianThreeCandidateRankingLaw thetaH
            (x1 omega) (x2 omega) (x3 omega))
          (gaussianThreeCandidateRankingLaw thetaA
            (x1 omega) (x2 omega) (x3 omega))
          (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega)) ∂D) <
        ∫ omega, expectedSecondMoverIndependent
          (gaussianThreeCandidateRankingLaw thetaH
            (x1 omega) (x2 omega) (x3 omega))
          (gaussianThreeCandidateRankingLaw thetaH
            (x1 omega) (x2 omega) (x3 omega))
          (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega)) ∂D) := by
  constructor
  · intro theta htheta
    exact integral_lt_integral_of_forall_lt D
      (hshared theta htheta) (hindependent theta htheta) fun omega =>
        gaussianThreeCandidate_prefersIndependent htheta
          (horder12 omega) (horder23 omega)
  · intro thetaA thetaH hthetaH hthetaHA
    exact integral_lt_integral_of_forall_lt D
      (hbetter thetaA thetaH hthetaH hthetaHA) (hworse thetaH hthetaH)
      fun omega => gaussianThreeCandidate_prefersWeaker
        hthetaH hthetaHA (horder12 omega) (horder23 omega)

/-- Canonical positive-rate Laplace ranking law, totalized outside the source domain. -/
noncomputable def laplaceThreeCandidateRankingLaw
    (theta x1 x2 x3 : ℝ) : PMF (Ranking 1) := by
  by_cases htheta : 0 < theta
  · exact theorem7LaplacianDefinition2RankingPMF theta x1 x2 x3 htheta
  · exact PMF.pure rum3Ranking012

/-- Fixed-profile canonical Laplace accuracy family. -/
noncomputable def laplaceThreeCandidateAccuracyFamily
    (x1 x2 x3 : ℝ) : AccuracyFamily 1 where
  dist := fun theta => laplaceThreeCandidateRankingLaw theta x1 x2 x3
  value := threeCandidateValueProfile x1 x2 x3

theorem laplaceThreeCandidateRankingLaw_eq_of_pos
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta) :
    laplaceThreeCandidateRankingLaw theta x1 x2 x3 =
      theorem7LaplacianDefinition2RankingPMF theta x1 x2 x3 htheta := by
  simp [laplaceThreeCandidateRankingLaw, htheta]

/-- Conditional canonical-Laplace Definition 2 endpoint. -/
theorem laplaceThreeCandidate_prefersIndependent
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersIndependentReranking
      (laplaceThreeCandidateRankingLaw theta x1 x2 x3)
      (threeCandidateValueProfile x1 x2 x3) := by
  rw [laplaceThreeCandidateRankingLaw_eq_of_pos htheta]
  exact
    MallowsComparison.paper_definition2_threeCandidate_laplacian_prefersIndependentReranking
      htheta
      (by simp [threeCandidateValueProfile, hx12])
      (by simp [threeCandidateValueProfile, hx23])
      hx12 hx23

/-- Conditional canonical-Laplace Definition 3 endpoint. -/
theorem laplaceThreeCandidate_prefersWeaker
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (laplaceThreeCandidateRankingLaw thetaA x1 x2 x3)
      (laplaceThreeCandidateRankingLaw thetaH x1 x2 x3)
      (threeCandidateValueProfile x1 x2 x3) := by
  let F := laplaceThreeCandidateAccuracyFamily x1 x2 x3
  have hsource :=
    paper_theorem2_laplacianRate_prefersWeakerCompetition_of_rum_source
      (F := F) (x1 := x1) (x2 := x2) (x3 := x3)
      (fun theta : ℝ => theta)
      (fun _ htheta => htheta)
      (fun _ _ _ hthetaHA => hthetaHA)
      (by simp [F, laplaceThreeCandidateAccuracyFamily,
        threeCandidateValueProfile])
      (by simp [F, laplaceThreeCandidateAccuracyFamily,
        threeCandidateValueProfile])
      (by simp [F, laplaceThreeCandidateAccuracyFamily,
        threeCandidateValueProfile])
      hx12 hx23
      (by
        intro theta htheta
        exact laplaceThreeCandidateRankingLaw_eq_of_pos htheta)
  exact hsource thetaA thetaH hthetaH hthetaHA

/--
Paper Theorem 2, Laplace part, after averaging the proved conditional
comparisons over an arbitrary outer value distribution `D`.
-/
theorem theorem2_laplace_with_outer_value_distribution
    {Omega : Type*} [MeasurableSpace Omega]
    (D : Measure Omega) [IsProbabilityMeasure D]
    (x1 x2 x3 : Omega → ℝ)
    (horder12 : ∀ omega, x2 omega < x1 omega)
    (horder23 : ∀ omega, x3 omega < x2 omega)
    (hshared : ∀ theta, 0 < theta → Integrable (fun omega =>
      expectedSecondMoverShared
        (laplaceThreeCandidateRankingLaw theta
          (x1 omega) (x2 omega) (x3 omega))
        (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega))) D)
    (hindependent : ∀ theta, 0 < theta → Integrable (fun omega =>
      expectedSecondMoverIndependent
        (laplaceThreeCandidateRankingLaw theta
          (x1 omega) (x2 omega) (x3 omega))
        (laplaceThreeCandidateRankingLaw theta
          (x1 omega) (x2 omega) (x3 omega))
        (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega))) D)
    (hbetter : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun omega =>
        expectedSecondMoverIndependent
          (laplaceThreeCandidateRankingLaw thetaH
            (x1 omega) (x2 omega) (x3 omega))
          (laplaceThreeCandidateRankingLaw thetaA
            (x1 omega) (x2 omega) (x3 omega))
          (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega))) D)
    (hworse : ∀ thetaH, 0 < thetaH → Integrable (fun omega =>
      expectedSecondMoverIndependent
        (laplaceThreeCandidateRankingLaw thetaH
          (x1 omega) (x2 omega) (x3 omega))
        (laplaceThreeCandidateRankingLaw thetaH
          (x1 omega) (x2 omega) (x3 omega))
        (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega))) D) :
    (∀ theta, 0 < theta →
      (∫ omega, expectedSecondMoverShared
          (laplaceThreeCandidateRankingLaw theta
            (x1 omega) (x2 omega) (x3 omega))
          (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega)) ∂D) <
        ∫ omega, expectedSecondMoverIndependent
          (laplaceThreeCandidateRankingLaw theta
            (x1 omega) (x2 omega) (x3 omega))
          (laplaceThreeCandidateRankingLaw theta
            (x1 omega) (x2 omega) (x3 omega))
          (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega)) ∂D) ∧
    (∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∫ omega, expectedSecondMoverIndependent
          (laplaceThreeCandidateRankingLaw thetaH
            (x1 omega) (x2 omega) (x3 omega))
          (laplaceThreeCandidateRankingLaw thetaA
            (x1 omega) (x2 omega) (x3 omega))
          (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega)) ∂D) <
        ∫ omega, expectedSecondMoverIndependent
          (laplaceThreeCandidateRankingLaw thetaH
            (x1 omega) (x2 omega) (x3 omega))
          (laplaceThreeCandidateRankingLaw thetaH
            (x1 omega) (x2 omega) (x3 omega))
          (threeCandidateValueProfile (x1 omega) (x2 omega) (x3 omega)) ∂D) := by
  constructor
  · intro theta htheta
    exact integral_lt_integral_of_forall_lt D
      (hshared theta htheta) (hindependent theta htheta) fun omega =>
        laplaceThreeCandidate_prefersIndependent htheta
          (horder12 omega) (horder23 omega)
  · intro thetaA thetaH hthetaH hthetaHA
    exact integral_lt_integral_of_forall_lt D
      (hbetter thetaA thetaH hthetaH hthetaHA) (hworse thetaH hthetaH)
      fun omega => laplaceThreeCandidate_prefersWeaker
        hthetaH hthetaHA (horder12 omega) (horder23 omega)

end KR21Monoculture
