import KR21Monoculture.OuterLinearPayoffBridge

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter

namespace KR21Monoculture

/-!
# Fixed-center Mallows outer-source bridge

The KR21 source first samples a cardinal value profile from an outer law `D`
and then uses a finite Mallows ranking law around one fixed true ordering.  This
module keeps that outer draw explicit.  Its hypotheses say exactly what is
needed for the finite-sum transport: `D` is a probability law, every coordinate
is integrable, and the profiles are strictly ordered by the fixed center almost
everywhere.  No relabelling of an arbitrary identity-labelled profile is
performed here.
-/

/-- A fixed-center Mallows ranking family, independent of the realized
cardinal profile. -/
noncomputable def fixedCenterMallowsDistributionalFamily {n : ℕ}
    (center : Ranking n) : DistributionalAccuracyFamily n where
  dist := fun theta _ => (concreteMallowsSpec center theta).law

@[simp] theorem fixedCenterMallowsDistributionalFamily_dist
    {n : ℕ} (center : Ranking n) (theta : ℝ) (value : ValueProfile n) :
    (fixedCenterMallowsDistributionalFamily center).dist theta value =
      (concreteMallowsSpec center theta).law := rfl

/-- Almost-everywhere strict pointwise inequalities integrate strictly under a
probability law when both sides are integrable. -/
theorem integral_lt_integral_of_ae_lt
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {f g : α → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hlt : ∀ᵐ a ∂μ, f a < g a) :
    (∫ a, f a ∂μ) < ∫ a, g a ∂μ := by
  have hdiff_int : Integrable (fun a => g a - f a) μ := hg.sub hf
  have hdiff_nonneg : 0 ≤ᵐ[μ] fun a => g a - f a := by
    filter_upwards [hlt] with a ha
    exact sub_nonneg.mpr (le_of_lt ha)
  have hsupport_ae : ∀ᵐ a ∂μ, a ∈ Function.support (fun a => g a - f a) := by
    filter_upwards [hlt] with a ha
    change g a - f a ≠ 0
    exact ne_of_gt (sub_pos.mpr ha)
  have hsupport_pos : 0 < μ (Function.support fun a => g a - f a) := by
    apply (pos_iff_ne_zero).2
    intro hzero
    have hcompl : μ (Function.support (fun a => g a - f a))ᶜ = 0 :=
      (mem_ae_iff.mp hsupport_ae)
    have huniv : μ Set.univ = 0 := by
      rw [← Set.union_compl_self (Function.support fun a => g a - f a)]
      exact measure_union_null hzero hcompl
    rw [measure_univ] at huniv
    norm_num at huniv
  have hpos : 0 < ∫ a, g a - f a ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hdiff_nonneg hdiff_int).2 hsupport_pos
  have hsub :
      (∫ a, g a - f a ∂μ) = (∫ a, g a ∂μ) - ∫ a, f a ∂μ :=
    integral_sub hg hf
  linarith

/-- If values decrease down a fixed center almost surely, their coordinatewise
mean decreases strictly down that same center. -/
theorem strictlyOrderedBy_outerMeanValue_of_ae
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    StrictlyOrderedBy center (outerMeanValue D) := by
  intro a b hab
  unfold outerMeanValue
  apply integral_lt_integral_of_ae_lt
  · exact hvalue b
  · exact hvalue a
  filter_upwards [hstrict] with value hvalue_strict
  exact hvalue_strict hab

/-- The ordinary fixed-value accuracy family associated with the same
fixed-center Mallows laws. -/
noncomputable def fixedCenterMallowsPointFamily {n : ℕ}
    (center : Ranking n) (value : ValueProfile n) : AccuracyFamily n where
  dist := fun theta => (concreteMallowsSpec center theta).law
  value := value

@[simp] theorem fixedCenterMallowsPointFamily_dist
    {n : ℕ} (center : Ranking n) (value : ValueProfile n) (theta : ℝ) :
    (fixedCenterMallowsPointFamily center value).dist theta =
      (concreteMallowsSpec center theta).law := rfl

/-- The lightweight point family is definitionally the concrete Mallows family
used by the established finite-sum Theorem 1 proof. -/
theorem fixedCenterMallowsPointFamily_eq_concrete
    {n : ℕ} (center : Ranking n) (value : ValueProfile n)
    (hvalue : StrictlyOrderedBy center value) :
    fixedCenterMallowsPointFamily center value =
      MallowsAccuracyFamilySpec.toAccuracyFamily
        (concreteMallowsAccuracyFamilySpec center value hvalue) := by
  rfl

/-- A fixed-center Mallows first-mover outer payoff is the corresponding
finite-PMF payoff at the coordinatewise outer mean. -/
theorem fixedCenterMallows_outerExpected_first_eq_mean
    {n : ℕ} (D : Measure (ValueProfile n)) (center : Ranking n) (theta : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    DistributionalAccuracyFamily.outerExpected D
      (fun value => expectedFirstMoverUtility
        ((fixedCenterMallowsDistributionalFamily center).dist theta value) value) =
      expectedFirstMoverUtility (concreteMallowsSpec center theta).law
        (outerMeanValue D) := by
  simpa [fixedCenterMallowsDistributionalFamily] using
    (outerExpected_expectedFirstMoverUtility_eq_outerMean D
      (concreteMallowsSpec center theta).law hvalue)

/-- A fixed-center Mallows shared second-mover outer payoff is the
corresponding finite-PMF payoff at the coordinatewise outer mean. -/
theorem fixedCenterMallows_outerExpected_shared_eq_mean
    {n : ℕ} (D : Measure (ValueProfile n)) (center : Ranking n) (theta : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    DistributionalAccuracyFamily.outerExpected D
      (fun value => expectedSecondMoverShared
        ((fixedCenterMallowsDistributionalFamily center).dist theta value) value) =
      expectedSecondMoverShared (concreteMallowsSpec center theta).law
        (outerMeanValue D) := by
  simpa [fixedCenterMallowsDistributionalFamily] using
    (outerExpected_expectedSecondMoverShared_eq_outerMean D
      (concreteMallowsSpec center theta).law hvalue)

/-- A fixed-center Mallows independent second-mover outer payoff is the
corresponding finite-PMF payoff at the coordinatewise outer mean. -/
theorem fixedCenterMallows_outerExpected_independent_eq_mean
    {n : ℕ} (D : Measure (ValueProfile n)) (center : Ranking n)
    (thetaSecond thetaFirst : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    DistributionalAccuracyFamily.outerExpected D
      (fun value => expectedSecondMoverIndependent
        ((fixedCenterMallowsDistributionalFamily center).dist thetaSecond value)
        ((fixedCenterMallowsDistributionalFamily center).dist thetaFirst value)
        value) =
      expectedSecondMoverIndependent
        (concreteMallowsSpec center thetaSecond).law
        (concreteMallowsSpec center thetaFirst).law
        (outerMeanValue D) := by
  simpa [fixedCenterMallowsDistributionalFamily] using
    (outerExpected_expectedSecondMoverIndependent_eq_outerMean D
      (concreteMallowsSpec center thetaSecond).law
      (concreteMallowsSpec center thetaFirst).law hvalue)

/-- The outer all-algorithm expression `f` is exactly its fixed-value Mallows
counterpart evaluated at the coordinatewise mean profile. -/
theorem fixedCenterMallows_outer_theorem1_f_eq_mean
    {n : ℕ} (D : Measure (ValueProfile n)) (center : Ranking n)
    (thetaA thetaH : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    DistributionalAccuracyFamily.theorem1_f
      (fixedCenterMallowsDistributionalFamily center) D thetaA thetaH =
      AccuracyFamily.theorem1_f
        (fixedCenterMallowsPointFamily center (outerMeanValue D)) thetaA thetaH := by
  change DistributionalAccuracyFamily.outerExpected D
      (fun value => expectedFirstMoverUtility (concreteMallowsSpec center thetaA).law value) +
      DistributionalAccuracyFamily.outerExpected D
        (fun value => expectedSecondMoverShared (concreteMallowsSpec center thetaA).law value) =
    expectedFirstMoverUtility (concreteMallowsSpec center thetaA).law (outerMeanValue D) +
      expectedSecondMoverShared (concreteMallowsSpec center thetaA).law (outerMeanValue D)
  rw [outerExpected_expectedFirstMoverUtility_eq_outerMean D
      (concreteMallowsSpec center thetaA).law hvalue,
    outerExpected_expectedSecondMoverShared_eq_outerMean D
      (concreteMallowsSpec center thetaA).law hvalue]

/-- The outer mixed expression `g` is exactly its fixed-value Mallows
counterpart evaluated at the coordinatewise mean profile. -/
theorem fixedCenterMallows_outer_theorem1_g_eq_mean
    {n : ℕ} (D : Measure (ValueProfile n)) (center : Ranking n)
    (thetaA thetaH : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    DistributionalAccuracyFamily.theorem1_g
      (fixedCenterMallowsDistributionalFamily center) D thetaA thetaH =
      AccuracyFamily.theorem1_g
        (fixedCenterMallowsPointFamily center (outerMeanValue D)) thetaA thetaH := by
  change DistributionalAccuracyFamily.outerExpected D
      (fun value => expectedFirstMoverUtility (concreteMallowsSpec center thetaH).law value) +
      DistributionalAccuracyFamily.outerExpected D
        (fun value => expectedSecondMoverIndependent
          (concreteMallowsSpec center thetaH).law (concreteMallowsSpec center thetaA).law value) =
    expectedFirstMoverUtility (concreteMallowsSpec center thetaH).law (outerMeanValue D) +
      expectedSecondMoverIndependent
        (concreteMallowsSpec center thetaH).law (concreteMallowsSpec center thetaA).law
        (outerMeanValue D)
  rw [outerExpected_expectedFirstMoverUtility_eq_outerMean D
      (concreteMallowsSpec center thetaH).law hvalue,
    outerExpected_expectedSecondMoverIndependent_eq_outerMean D
      (concreteMallowsSpec center thetaH).law (concreteMallowsSpec center thetaA).law hvalue]

/-- The outer all-human expression `h` is exactly its fixed-value Mallows
counterpart evaluated at the coordinatewise mean profile. -/
theorem fixedCenterMallows_outer_theorem1_h_eq_mean
    {n : ℕ} (D : Measure (ValueProfile n)) (center : Ranking n)
    (thetaA thetaH : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    DistributionalAccuracyFamily.theorem1_h
      (fixedCenterMallowsDistributionalFamily center) D thetaA thetaH =
      AccuracyFamily.theorem1_h
        (fixedCenterMallowsPointFamily center (outerMeanValue D)) thetaA thetaH := by
  change DistributionalAccuracyFamily.outerExpected D
      (fun value => expectedFirstMoverUtility (concreteMallowsSpec center thetaH).law value) +
      DistributionalAccuracyFamily.outerExpected D
        (fun value => expectedSecondMoverIndependent
          (concreteMallowsSpec center thetaH).law (concreteMallowsSpec center thetaH).law value) =
    expectedFirstMoverUtility (concreteMallowsSpec center thetaH).law (outerMeanValue D) +
      expectedSecondMoverIndependent
        (concreteMallowsSpec center thetaH).law (concreteMallowsSpec center thetaH).law
        (outerMeanValue D)
  rw [outerExpected_expectedFirstMoverUtility_eq_outerMean D
      (concreteMallowsSpec center thetaH).law hvalue,
    outerExpected_expectedSecondMoverIndependent_eq_outerMean D
      (concreteMallowsSpec center thetaH).law (concreteMallowsSpec center thetaH).law hvalue]

/-- The outer algorithm-against-human expression is exactly its fixed-value
Mallows counterpart evaluated at the coordinatewise mean profile. -/
theorem fixedCenterMallows_outer_theorem1_algorithmAgainstHuman_eq_mean
    {n : ℕ} (D : Measure (ValueProfile n)) (center : Ranking n)
    (thetaA thetaH : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    DistributionalAccuracyFamily.theorem1_algorithmAgainstHuman
      (fixedCenterMallowsDistributionalFamily center) D thetaA thetaH =
      AccuracyFamily.theorem1_algorithmAgainstHuman
        (fixedCenterMallowsPointFamily center (outerMeanValue D)) thetaA thetaH := by
  change DistributionalAccuracyFamily.outerExpected D
      (fun value => expectedFirstMoverUtility (concreteMallowsSpec center thetaA).law value) +
      DistributionalAccuracyFamily.outerExpected D
        (fun value => expectedSecondMoverIndependent
          (concreteMallowsSpec center thetaA).law (concreteMallowsSpec center thetaH).law value) =
    expectedFirstMoverUtility (concreteMallowsSpec center thetaA).law (outerMeanValue D) +
      expectedSecondMoverIndependent
        (concreteMallowsSpec center thetaA).law (concreteMallowsSpec center thetaH).law
        (outerMeanValue D)
  rw [outerExpected_expectedFirstMoverUtility_eq_outerMean D
      (concreteMallowsSpec center thetaA).law hvalue,
    outerExpected_expectedSecondMoverIndependent_eq_outerMean D
      (concreteMallowsSpec center thetaA).law (concreteMallowsSpec center thetaH).law hvalue]

/-- Source-shaped Definition 2 for an outer cardinal-value law and a
fixed-center Mallows ranking law.  The strict ordering condition is almost
everywhere, rather than an unrecorded pointwise convention. -/
theorem fixedCenterMallows_outer_prefersIndependentReranking
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n) (theta : ℝ) (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    (fixedCenterMallowsDistributionalFamily center).PrefersIndependentReranking
      D theta := by
  let mean := outerMeanValue D
  have hmean : StrictlyOrderedBy center mean :=
    strictlyOrderedBy_outerMeanValue_of_ae D center hvalue hstrict
  let MF := concreteMallowsAccuracyFamilySpec center mean hmean
  have hpoint : Model.PrefersIndependentReranking
      ((fixedCenterMallowsPointFamily center mean).dist theta) mean := by
    rw [fixedCenterMallowsPointFamily_eq_concrete center mean hmean]
    exact MF.prefersIndependentReranking hn theta htheta
  change DistributionalAccuracyFamily.outerExpected D
      (fun value => expectedSecondMoverShared (concreteMallowsSpec center theta).law value) <
    DistributionalAccuracyFamily.outerExpected D
      (fun value => expectedSecondMoverIndependent
        (concreteMallowsSpec center theta).law (concreteMallowsSpec center theta).law value)
  rw [outerExpected_expectedSecondMoverShared_eq_outerMean D
      (concreteMallowsSpec center theta).law hvalue,
    outerExpected_expectedSecondMoverIndependent_eq_outerMean D
      (concreteMallowsSpec center theta).law (concreteMallowsSpec center theta).law hvalue]
  exact hpoint

/-- Source-shaped Definition 3 for an outer cardinal-value law and two
fixed-center Mallows ranking laws of strictly ordered accuracy. -/
theorem fixedCenterMallows_outer_prefersWeakerCompetition
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n) (thetaA thetaH : ℝ)
    (hthetaH : 0 < thetaH) (htheta : thetaH < thetaA)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    (fixedCenterMallowsDistributionalFamily center).PrefersWeakerCompetition
      D thetaA thetaH := by
  let mean := outerMeanValue D
  have hmean : StrictlyOrderedBy center mean :=
    strictlyOrderedBy_outerMeanValue_of_ae D center hvalue hstrict
  let MF := concreteMallowsAccuracyFamilySpec center mean hmean
  have hpoint : Model.PrefersWeakerCompetition
      ((fixedCenterMallowsPointFamily center mean).dist thetaA)
      ((fixedCenterMallowsPointFamily center mean).dist thetaH) mean := by
    rw [fixedCenterMallowsPointFamily_eq_concrete center mean hmean]
    exact MF.prefersWeakerCompetition hn thetaA thetaH hthetaH htheta
  change DistributionalAccuracyFamily.outerExpected D
      (fun value => expectedSecondMoverIndependent
        (concreteMallowsSpec center thetaH).law (concreteMallowsSpec center thetaA).law value) <
    DistributionalAccuracyFamily.outerExpected D
      (fun value => expectedSecondMoverIndependent
        (concreteMallowsSpec center thetaH).law (concreteMallowsSpec center thetaH).law value)
  rw [outerExpected_expectedSecondMoverIndependent_eq_outerMean D
      (concreteMallowsSpec center thetaH).law (concreteMallowsSpec center thetaA).law hvalue,
    outerExpected_expectedSecondMoverIndependent_eq_outerMean D
      (concreteMallowsSpec center thetaH).law (concreteMallowsSpec center thetaH).law hvalue]
  exact hpoint

/-- The existing concrete finite Mallows Theorem 1 theorem, restated for the
lightweight point-family surface used by the outer-source transport. -/
theorem fixedCenterMallows_point_theorem1Target
    {n : ℕ} (center : Ranking n) (value : ValueProfile n)
    (hvalue : StrictlyOrderedBy center value) (hn : 0 < n)
    (thetaH : ℝ) (hthetaH : 0 < thetaH) :
    AccuracyFamily.Theorem1Target
      (fixedCenterMallowsPointFamily center value) thetaH := by
  rw [fixedCenterMallowsPointFamily_eq_concrete center value hvalue]
  exact concreteMallows_theorem1Target center value hvalue hn thetaH hthetaH

/-- Full source-shaped Theorem 1 conclusion for a fixed-center Mallows model.

The theorem has one shared accuracy witness outside the outer integral.  Its
only outer-law assumptions are probability, coordinatewise integrability, and
almost-everywhere strict ordering by the fixed center. -/
theorem fixedCenterMallows_outer_distributionalTheorem1Target
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n) (thetaH : ℝ) (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    DistributionalAccuracyFamily.DistributionalTheorem1Target
      (fixedCenterMallowsDistributionalFamily center) D thetaH := by
  have hmean : StrictlyOrderedBy center (outerMeanValue D) :=
    strictlyOrderedBy_outerMeanValue_of_ae D center hvalue hstrict
  rcases fixedCenterMallows_point_theorem1Target
      center (outerMeanValue D) hmean hn thetaH hthetaH with
    ⟨thetaA, htheta, hparadox⟩
  rcases hparadox with ⟨hdominant, hwelfare⟩
  rcases hdominant with ⟨hagainstAlgorithm, hagainstHuman⟩
  have hgf :
      AccuracyFamily.theorem1_g
        (fixedCenterMallowsPointFamily center (outerMeanValue D)) thetaA thetaH <
      AccuracyFamily.theorem1_f
        (fixedCenterMallowsPointFamily center (outerMeanValue D)) thetaA thetaH := by
    simpa [AccuracyFamily.theorem1_f, AccuracyFamily.theorem1_g,
      AccuracyFamily.modelAt, Model.firstMoverEU, Model.secondMoverEU,
      Model.rankingDist] using hagainstAlgorithm
  have hh_against :
      AccuracyFamily.theorem1_h
        (fixedCenterMallowsPointFamily center (outerMeanValue D)) thetaA thetaH <
      AccuracyFamily.theorem1_algorithmAgainstHuman
        (fixedCenterMallowsPointFamily center (outerMeanValue D)) thetaA thetaH := by
    simpa [AccuracyFamily.theorem1_h, AccuracyFamily.theorem1_algorithmAgainstHuman,
      AccuracyFamily.modelAt, Model.firstMoverEU, Model.secondMoverEU,
      Model.rankingDist] using hagainstHuman
  have hfh :
      AccuracyFamily.theorem1_f
        (fixedCenterMallowsPointFamily center (outerMeanValue D)) thetaA thetaH <
      AccuracyFamily.theorem1_h
        (fixedCenterMallowsPointFamily center (outerMeanValue D)) thetaA thetaH := by
    unfold Model.HumanProfileBeatsAlgorithmProfile at hwelfare
    rw [Model.welfareRandomOrder_self, Model.welfareRandomOrder_self] at hwelfare
    rw [Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU,
      Model.welfareOrdered_eq_firstMoverEU_add_secondMoverEU] at hwelfare
    simpa [AccuracyFamily.theorem1_f, AccuracyFamily.theorem1_h] using hwelfare
  refine ⟨thetaA, htheta, ?_, ?_, ?_⟩
  · rw [fixedCenterMallows_outer_theorem1_g_eq_mean D center thetaA thetaH hvalue,
      fixedCenterMallows_outer_theorem1_f_eq_mean D center thetaA thetaH hvalue]
    exact hgf
  · rw [fixedCenterMallows_outer_theorem1_h_eq_mean D center thetaA thetaH hvalue,
      fixedCenterMallows_outer_theorem1_algorithmAgainstHuman_eq_mean
        D center thetaA thetaH hvalue]
    exact hh_against
  · rw [fixedCenterMallows_outer_theorem1_f_eq_mean D center thetaA thetaH hvalue,
      fixedCenterMallows_outer_theorem1_h_eq_mean D center thetaA thetaH hvalue]
    exact hfh

end KR21Monoculture
