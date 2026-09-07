import KR21Monoculture.OuterLinearPayoffBridge

open AppliedModelingLib MeasureTheory ProbabilityTheory

namespace KR21Monoculture

/-!
# Outer Theorem 1 mean-reduction bridge

For a ranking family whose conditional law is independent of the realized
cardinal-value profile, all KR21 two-firm payoffs are linear in that profile.
Consequently, an outer candidate-value distribution reduces exactly to its
coordinatewise mean.  This file records the resulting one-witness Theorem 1
lift.  It intentionally does not apply to a value-dependent ranking kernel.
-/

namespace DistributionalAccuracyFamily

/-- A distributional ranking family induced by a ranking law which is fixed
across the outer candidate-value draw. -/
noncomputable def ofFixedLaw {n : ℕ}
    (law : ℝ → PMF (Ranking n)) : DistributionalAccuracyFamily n where
  dist := fun theta _ => law theta

/-- The corresponding fixed-value family at one cardinal profile. -/
noncomputable def fixedLawPointFamily {n : ℕ}
    (law : ℝ → PMF (Ranking n)) (value : ValueProfile n) : AccuracyFamily n where
  dist := law
  value := value

@[simp] theorem ofFixedLaw_dist {n : ℕ} (law : ℝ → PMF (Ranking n))
    (theta : ℝ) (value : ValueProfile n) :
    (ofFixedLaw law).dist theta value = law theta := rfl

@[simp] theorem fixedLawPointFamily_dist {n : ℕ} (law : ℝ → PMF (Ranking n))
    (value : ValueProfile n) (theta : ℝ) :
    (fixedLawPointFamily law value).dist theta = law theta := rfl

/-- The outer all-algorithm expression of a value-independent ranking law is
its ordinary fixed-value expression at the coordinatewise outer mean. -/
theorem ofFixedLaw_outer_theorem1_f_eq_mean
    {n : ℕ} (D : Measure (ValueProfile n)) (law : ℝ → PMF (Ranking n))
    (thetaA thetaH : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (ofFixedLaw law).theorem1_f D thetaA thetaH =
      AccuracyFamily.theorem1_f
        (fixedLawPointFamily law (outerMeanValue D)) thetaA thetaH := by
  change outerExpected D
      (fun value => expectedFirstMoverUtility (law thetaA) value) +
      outerExpected D
        (fun value => expectedSecondMoverShared (law thetaA) value) =
    expectedFirstMoverUtility (law thetaA) (outerMeanValue D) +
      expectedSecondMoverShared (law thetaA) (outerMeanValue D)
  rw [outerExpected_expectedFirstMoverUtility_eq_outerMean D (law thetaA) hvalue,
    outerExpected_expectedSecondMoverShared_eq_outerMean D (law thetaA) hvalue]

/-- The outer mixed expression of a value-independent ranking law is its
ordinary fixed-value expression at the coordinatewise outer mean. -/
theorem ofFixedLaw_outer_theorem1_g_eq_mean
    {n : ℕ} (D : Measure (ValueProfile n)) (law : ℝ → PMF (Ranking n))
    (thetaA thetaH : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (ofFixedLaw law).theorem1_g D thetaA thetaH =
      AccuracyFamily.theorem1_g
        (fixedLawPointFamily law (outerMeanValue D)) thetaA thetaH := by
  change outerExpected D
      (fun value => expectedFirstMoverUtility (law thetaH) value) +
      outerExpected D
        (fun value => expectedSecondMoverIndependent (law thetaH) (law thetaA) value) =
    expectedFirstMoverUtility (law thetaH) (outerMeanValue D) +
      expectedSecondMoverIndependent (law thetaH) (law thetaA) (outerMeanValue D)
  rw [outerExpected_expectedFirstMoverUtility_eq_outerMean D (law thetaH) hvalue,
    outerExpected_expectedSecondMoverIndependent_eq_outerMean D
      (law thetaH) (law thetaA) hvalue]

/-- The outer all-human expression of a value-independent ranking law is its
ordinary fixed-value expression at the coordinatewise outer mean. -/
theorem ofFixedLaw_outer_theorem1_h_eq_mean
    {n : ℕ} (D : Measure (ValueProfile n)) (law : ℝ → PMF (Ranking n))
    (thetaA thetaH : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (ofFixedLaw law).theorem1_h D thetaA thetaH =
      AccuracyFamily.theorem1_h
        (fixedLawPointFamily law (outerMeanValue D)) thetaA thetaH := by
  change outerExpected D
      (fun value => expectedFirstMoverUtility (law thetaH) value) +
      outerExpected D
        (fun value => expectedSecondMoverIndependent (law thetaH) (law thetaH) value) =
    expectedFirstMoverUtility (law thetaH) (outerMeanValue D) +
      expectedSecondMoverIndependent (law thetaH) (law thetaH) (outerMeanValue D)
  rw [outerExpected_expectedFirstMoverUtility_eq_outerMean D (law thetaH) hvalue,
    outerExpected_expectedSecondMoverIndependent_eq_outerMean D
      (law thetaH) (law thetaH) hvalue]

/-- The outer algorithm-against-human expression of a value-independent
ranking law is its ordinary fixed-value expression at the coordinatewise outer
mean. -/
theorem ofFixedLaw_outer_theorem1_algorithmAgainstHuman_eq_mean
    {n : ℕ} (D : Measure (ValueProfile n)) (law : ℝ → PMF (Ranking n))
    (thetaA thetaH : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (ofFixedLaw law).theorem1_algorithmAgainstHuman D thetaA thetaH =
      AccuracyFamily.theorem1_algorithmAgainstHuman
        (fixedLawPointFamily law (outerMeanValue D)) thetaA thetaH := by
  change outerExpected D
      (fun value => expectedFirstMoverUtility (law thetaA) value) +
      outerExpected D
        (fun value => expectedSecondMoverIndependent (law thetaA) (law thetaH) value) =
    expectedFirstMoverUtility (law thetaA) (outerMeanValue D) +
      expectedSecondMoverIndependent (law thetaA) (law thetaH) (outerMeanValue D)
  rw [outerExpected_expectedFirstMoverUtility_eq_outerMean D (law thetaA) hvalue,
    outerExpected_expectedSecondMoverIndependent_eq_outerMean D
      (law thetaA) (law thetaH) hvalue]

/--
One common Theorem 1 accuracy witness lifts through an arbitrary outer value
law whenever the conditional ranking PMF is fixed across that draw.  The point
theorem is used only at the coordinatewise mean profile; no per-profile
accuracy witnesses and no unproved outer continuity premise appear here.
-/
theorem distributionalTheorem1Target_of_fixedLaw_pointTarget
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (law : ℝ → PMF (Ranking n)) (thetaH : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hpoint : AccuracyFamily.Theorem1Target
      (fixedLawPointFamily law (outerMeanValue D)) thetaH) :
    (ofFixedLaw law).DistributionalTheorem1Target D thetaH := by
  rcases hpoint with ⟨thetaA, htheta, hparadox⟩
  rcases hparadox with ⟨hdominant, hwelfare⟩
  rcases hdominant with ⟨hagainstAlgorithm, hagainstHuman⟩
  have hgf :
      AccuracyFamily.theorem1_g
        (fixedLawPointFamily law (outerMeanValue D)) thetaA thetaH <
      AccuracyFamily.theorem1_f
        (fixedLawPointFamily law (outerMeanValue D)) thetaA thetaH := by
    simpa [AccuracyFamily.theorem1_f, AccuracyFamily.theorem1_g,
      AccuracyFamily.modelAt, Model.firstMoverEU, Model.secondMoverEU,
      Model.rankingDist] using hagainstAlgorithm
  have hh_against :
      AccuracyFamily.theorem1_h
        (fixedLawPointFamily law (outerMeanValue D)) thetaA thetaH <
      AccuracyFamily.theorem1_algorithmAgainstHuman
        (fixedLawPointFamily law (outerMeanValue D)) thetaA thetaH := by
    simpa [AccuracyFamily.theorem1_h,
      AccuracyFamily.theorem1_algorithmAgainstHuman,
      AccuracyFamily.modelAt, Model.firstMoverEU, Model.secondMoverEU,
      Model.rankingDist] using hagainstHuman
  have hfh :
      AccuracyFamily.theorem1_f
        (fixedLawPointFamily law (outerMeanValue D)) thetaA thetaH <
      AccuracyFamily.theorem1_h
        (fixedLawPointFamily law (outerMeanValue D)) thetaA thetaH := by
    unfold Model.HumanProfileBeatsAlgorithmProfile at hwelfare
    rw [Model.welfareRandomOrder_self, Model.welfareRandomOrder_self] at hwelfare
    rw [Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU,
      Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU] at hwelfare
    simpa [AccuracyFamily.theorem1_f, AccuracyFamily.theorem1_h] using hwelfare
  refine ⟨thetaA, htheta, ?_, ?_, ?_⟩
  · rw [ofFixedLaw_outer_theorem1_g_eq_mean D law thetaA thetaH hvalue,
      ofFixedLaw_outer_theorem1_f_eq_mean D law thetaA thetaH hvalue]
    exact hgf
  · rw [ofFixedLaw_outer_theorem1_h_eq_mean D law thetaA thetaH hvalue,
      ofFixedLaw_outer_theorem1_algorithmAgainstHuman_eq_mean
        D law thetaA thetaH hvalue]
    exact hh_against
  · rw [ofFixedLaw_outer_theorem1_f_eq_mean D law thetaA thetaH hvalue,
      ofFixedLaw_outer_theorem1_h_eq_mean D law thetaA thetaH hvalue]
    exact hfh

/--
Semantic form of the mean-reduction lift.  The premise says the conditional
ranking PMF does not change with the realized value profile.  It is stated as
an equation over the kernel rather than by requiring a particular Lean
definition for the family.
-/
theorem distributionalTheorem1Target_of_valueIndependentKernel
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (thetaH : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hkernel : ∀ theta value,
      F.dist theta value = F.dist theta (outerMeanValue D))
    (hpoint : AccuracyFamily.Theorem1Target
      (F.pointFamily (outerMeanValue D)) thetaH) :
    F.DistributionalTheorem1Target D thetaH := by
  let law : ℝ → PMF (Ranking n) := fun theta => F.dist theta (outerMeanValue D)
  have hpoint_fixed : AccuracyFamily.Theorem1Target
      (fixedLawPointFamily law (outerMeanValue D)) thetaH := by
    simpa [law, fixedLawPointFamily, pointFamily] using hpoint
  have hlift := distributionalTheorem1Target_of_fixedLaw_pointTarget
    D law thetaH hvalue hpoint_fixed
  have hfamily : F = ofFixedLaw law := by
    cases F with
    | mk dist =>
      dsimp [law, ofFixedLaw] at hkernel ⊢
      congr
      funext theta value
      exact hkernel theta value
  rw [hfamily]
  exact hlift

end DistributionalAccuracyFamily

end KR21Monoculture
