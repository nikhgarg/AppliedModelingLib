import LG21TestOptionalPolicies.ContinuousResampling
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Continuous Gaussian population model and continuous fairness bridges

This file closes two source-model gaps that finite PMF surfaces cannot express:

* the unit-mass Gaussian population is represented by one probability measure
  on access, latent skill, and an independent finite family of Gaussian noise
  coordinates; observed features are `skill + noise`;
* the implication chain from latent-skill to observable to demographic
  fairness is proved for continuous measure laws by the law of total
  probability, using measurable kernels rather than finite PMF mixtures.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open MeasureTheory
open ProbabilityTheory

/-! ## Unified source population -/

/--
Parameters of the source's continuous Gaussian population.  Sampling a
student from the unit mass means sampling from `populationLaw` below.

The access coordinate is drawn independently of the entire skill/noise block.
This is the measure-theoretic form of access being preset and unrelated to
skill and observed features.
-/
structure LG21ContinuousGaussianPopulation (Feature : Type*)
    [Fintype Feature] where
  accessLaw : Measure Bool
  accessLaw_isProbability : IsProbabilityMeasure accessLaw
  priorMean : ℝ
  priorVariance : NNReal
  noiseVariance : Feature → NNReal

/-- Joint law of the independent feature-noise coordinates. -/
def lg21ContinuousGaussianNoiseLaw
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) :
    Measure (Feature → ℝ) :=
  Measure.pi (fun feature => gaussianReal 0 (M.noiseVariance feature))

/-- Joint law of latent skill and the independent feature-noise vector. -/
def lg21ContinuousGaussianStudentPrimitiveLaw
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) :
    Measure (ℝ × (Feature → ℝ)) :=
  (gaussianReal M.priorMean M.priorVariance).prod
    (lg21ContinuousGaussianNoiseLaw M)

/--
Unified population law on access, latent skill, and all feature noises.
The product construction makes access independent of the whole student block.
-/
def lg21ContinuousGaussianPopulationLaw
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) :
    Measure (Bool × (ℝ × (Feature → ℝ))) :=
  M.accessLaw.prod (lg21ContinuousGaussianStudentPrimitiveLaw M)

/-- Source access indicator `Z` on the unified population space. -/
def lg21ContinuousPopulationAccess
    {Feature : Type*} : Bool × (ℝ × (Feature → ℝ)) → Bool :=
  Prod.fst

/-- Source latent skill `q` on the unified population space. -/
def lg21ContinuousPopulationSkill
    {Feature : Type*} : Bool × (ℝ × (Feature → ℝ)) → ℝ :=
  fun student => student.2.1

/-- Feature-specific Gaussian noise `epsilon_k`. -/
def lg21ContinuousPopulationNoise
    {Feature : Type*} (feature : Feature) :
    Bool × (ℝ × (Feature → ℝ)) → ℝ :=
  fun student => student.2.2 feature

/-- Observed feature `theta_k = q + epsilon_k`. -/
def lg21ContinuousPopulationFeature
    {Feature : Type*} (feature : Feature) :
    Bool × (ℝ × (Feature → ℝ)) → ℝ :=
  fun student =>
    lg21ContinuousPopulationSkill student +
      lg21ContinuousPopulationNoise feature student

/-- The unified source population has total mass one. -/
theorem lg21ContinuousGaussianPopulationLaw_isProbability
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) :
    IsProbabilityMeasure (lg21ContinuousGaussianPopulationLaw M) := by
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  change IsProbabilityMeasure
    (M.accessLaw.prod
      ((gaussianReal M.priorMean M.priorVariance).prod
        (Measure.pi
          (fun feature => gaussianReal 0 (M.noiseVariance feature)))))
  infer_instance

/--
Access is independent of the entire latent-skill/noise block: every product
event factors into its access and student-block probabilities.
-/
theorem lg21ContinuousGaussianPopulation_access_student_factorization
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (accessEvent : Set Bool)
    (studentEvent : Set (ℝ × (Feature → ℝ))) :
    lg21ContinuousGaussianPopulationLaw M
        (accessEvent ×ˢ studentEvent) =
      M.accessLaw accessEvent *
        lg21ContinuousGaussianStudentPrimitiveLaw M studentEvent := by
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoiseLaw M) := by
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  letI : IsProbabilityMeasure
      (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
    unfold lg21ContinuousGaussianStudentPrimitiveLaw
    infer_instance
  exact Measure.prod_prod accessEvent studentEvent

/-- In particular, access and latent skill events factor. -/
theorem lg21ContinuousGaussianPopulation_access_skill_factorization
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (accessEvent : Set Bool) (skillEvent : Set ℝ) :
    lg21ContinuousGaussianPopulationLaw M
        (accessEvent ×ˢ
          (skillEvent ×ˢ (Set.univ : Set (Feature → ℝ)))) =
      M.accessLaw accessEvent *
        gaussianReal M.priorMean M.priorVariance skillEvent := by
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoiseLaw M) := by
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  letI : IsProbabilityMeasure
      (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
    unfold lg21ContinuousGaussianStudentPrimitiveLaw
    infer_instance
  rw [lg21ContinuousGaussianPopulationLaw, Measure.prod_prod]
  rw [lg21ContinuousGaussianStudentPrimitiveLaw, Measure.prod_prod]
  simp

/-- The latent-skill marginal is exactly the source Gaussian prior. -/
theorem lg21ContinuousGaussianStudentPrimitiveLaw_skill_marginal
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (skillEvent : Set ℝ) :
    lg21ContinuousGaussianStudentPrimitiveLaw M
        (skillEvent ×ˢ (Set.univ : Set (Feature → ℝ))) =
      gaussianReal M.priorMean M.priorVariance skillEvent := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoiseLaw M) := by
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  rw [lg21ContinuousGaussianStudentPrimitiveLaw, Measure.prod_prod]
  simp

/-- The noise-vector marginal is the independent Gaussian product law. -/
theorem lg21ContinuousGaussianStudentPrimitiveLaw_noise_marginal
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (noiseEvent : Set (Feature → ℝ)) :
    lg21ContinuousGaussianStudentPrimitiveLaw M
        ((Set.univ : Set ℝ) ×ˢ noiseEvent) =
      lg21ContinuousGaussianNoiseLaw M noiseEvent := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoiseLaw M) := by
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  rw [lg21ContinuousGaussianStudentPrimitiveLaw, Measure.prod_prod]
  simp

/--
The finite family of feature noises has the product-rectangle probabilities
of independent centered Gaussians with feature-specific variances.
-/
theorem lg21ContinuousGaussianNoiseLaw_product_rectangle
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (events : Feature → Set ℝ) :
    lg21ContinuousGaussianNoiseLaw M
        (Set.pi Set.univ events) =
      ∏ feature, gaussianReal 0 (M.noiseVariance feature) (events feature) := by
  rw [lg21ContinuousGaussianNoiseLaw, Measure.pi_pi]

/-- Every observed coordinate is definitionally `theta_k = q + epsilon_k`. -/
theorem lg21ContinuousPopulationFeature_eq_skill_add_noise
    {Feature : Type*} (feature : Feature)
    (student : Bool × (ℝ × (Feature → ℝ))) :
    lg21ContinuousPopulationFeature feature student =
      lg21ContinuousPopulationSkill student +
        lg21ContinuousPopulationNoise feature student :=
  rfl

/--
Source-model endpoint for the unit-mass Gaussian student population.  It
bundles the probability-law interpretation, the Gaussian skill marginal, the
independent Gaussian noise coordinates, and the defining signal equation
`theta_k = q + epsilon_k` in one reviewed declaration.
-/
theorem paper_student_gaussian_signal_model
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) :
    IsProbabilityMeasure (lg21ContinuousGaussianPopulationLaw M) ∧
      (∀ skillEvent : Set ℝ,
        lg21ContinuousGaussianStudentPrimitiveLaw M
            (skillEvent ×ˢ (Set.univ : Set (Feature → ℝ))) =
          gaussianReal M.priorMean M.priorVariance skillEvent) ∧
      (∀ events : Feature → Set ℝ,
        lg21ContinuousGaussianNoiseLaw M (Set.pi Set.univ events) =
          ∏ feature,
            gaussianReal 0 (M.noiseVariance feature) (events feature)) ∧
      ∀ (feature : Feature)
        (student : Bool × (ℝ × (Feature → ℝ))),
        lg21ContinuousPopulationFeature feature student =
          lg21ContinuousPopulationSkill student +
            lg21ContinuousPopulationNoise feature student := by
  refine
    ⟨lg21ContinuousGaussianPopulationLaw_isProbability M,
      lg21ContinuousGaussianStudentPrimitiveLaw_skill_marginal M,
      lg21ContinuousGaussianNoiseLaw_product_rectangle M, ?_⟩
  exact lg21ContinuousPopulationFeature_eq_skill_add_noise

/-- Any source-feasible action satisfies the paper's order `Y ≥ X`. -/
theorem paper_access_action_report_implies_take_of_feasible
    (policy : LG21RequirementPolicy) (status : LG21AccessStatus)
    (action : LG21AccessAction)
    (hfeasible :
      LG21RequirementPolicy.feasibleAction policy status action) :
    action.reportImpliesTake := by
  cases status with
  | noAccess =>
      have haction : action = LG21AccessAction.noTake :=
        (LG21RequirementPolicy.feasibleAction_noAccess_iff
          policy action).1 hfeasible
      rw [haction]
      exact LG21AccessAction.noTake_reportImpliesTake
  | access =>
      exact hfeasible.1

/--
Combined source endpoint for `Z ≥ Y ≥ X` and preset access.  Full source
feasibility enforces `Z ≥ Y ≥ X`; independently, the product population
law makes every access event independent of the entire latent-skill and
feature-noise block.
-/
theorem paper_access_action_constraints_and_access_independence
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (policy : LG21RequirementPolicy) (status : LG21AccessStatus)
    (action : LG21AccessAction)
    (hfeasible :
      LG21RequirementPolicy.feasibleAction policy status action)
    (accessEvent : Set Bool)
    (studentEvent : Set (ℝ × (Feature → ℝ))) :
    (status = LG21AccessStatus.noAccess →
        action = LG21AccessAction.noTake) ∧
      action.reportImpliesTake ∧
      lg21ContinuousGaussianPopulationLaw M
          (accessEvent ×ˢ studentEvent) =
        M.accessLaw accessEvent *
          lg21ContinuousGaussianStudentPrimitiveLaw M studentEvent :=
  ⟨by
      intro hstatus
      subst status
      exact
        (LG21RequirementPolicy.feasibleAction_noAccess_iff
          policy action).1 hfeasible,
    paper_access_action_report_implies_take_of_feasible
      policy status action hfeasible,
    lg21ContinuousGaussianPopulation_access_student_factorization
      M accessEvent studentEvent⟩

/-! ## Continuous law-of-total-probability fairness chain -/

/--
Continuous Definitions 2 to 3 bridge.  Observable laws are obtained by
integrating latent-skill-conditioned Markov kernels against the common
conditional skill law at each base profile.
-/
theorem lg21_sourceLawObservablyFair_of_latentSkillFair_of_kernel_mixture
    {Skill Base Test Estimate : Type*}
    [MeasurableSpace Skill] [MeasurableSpace Base]
    [MeasurableSpace Estimate]
    {S : LG21SourceLawPolicySurface Skill Base Test (Measure Estimate)}
    (skillGivenBase : Kernel Base Skill)
    (latentAccessKernel latentNoAccessKernel :
      S.Equilibrium → Base → Kernel Skill Estimate)
    (hLatentAccess :
      ∀ e base skill,
        latentAccessKernel e base skill =
          S.latentAccessLaw e skill base)
    (hLatentNoAccess :
      ∀ e base skill,
        latentNoAccessKernel e base skill =
          S.latentNoAccessLaw e skill base)
    (hObservableAccess :
      ∀ e base,
        S.observableAccessLaw e base =
          Measure.bind (skillGivenBase base)
            (latentAccessKernel e base))
    (hObservableNoAccess :
      ∀ e base,
        S.observableNoAccessLaw e base =
          Measure.bind (skillGivenBase base)
            (latentNoAccessKernel e base))
    (hlatent : lg21SourceLawLatentSkillFair S) :
    lg21SourceLawObservablyFair S := by
  intro e base
  have hkernel :
      latentAccessKernel e base = latentNoAccessKernel e base := by
    ext skill
    rw [hLatentAccess e base skill, hLatentNoAccess e base skill]
    exact congrArg (fun law : Measure Estimate => law _) (hlatent e skill base)
  rw [hObservableAccess e base, hObservableNoAccess e base, hkernel]

/--
Continuous Definitions 3 to 4 bridge.  Demographic laws integrate the
observable base-conditioned kernels against the shared base-profile law.
-/
theorem lg21_sourceLawDemographicallyFair_of_observablyFair_of_kernel_mixture
    {Skill Base Test Estimate : Type*}
    [MeasurableSpace Base] [MeasurableSpace Estimate]
    {S : LG21SourceLawPolicySurface Skill Base Test (Measure Estimate)}
    (baseLaw : Measure Base)
    (observableAccessKernel observableNoAccessKernel :
      S.Equilibrium → Kernel Base Estimate)
    (hObservableAccess :
      ∀ e base,
        observableAccessKernel e base = S.observableAccessLaw e base)
    (hObservableNoAccess :
      ∀ e base,
        observableNoAccessKernel e base = S.observableNoAccessLaw e base)
    (hDemographicAccess :
      ∀ e,
        S.demographicAccessLaw e =
          Measure.bind baseLaw (observableAccessKernel e))
    (hDemographicNoAccess :
      ∀ e,
        S.demographicNoAccessLaw e =
          Measure.bind baseLaw (observableNoAccessKernel e))
    (hobservable : lg21SourceLawObservablyFair S) :
    lg21SourceLawDemographicallyFair S := by
  intro e
  have hkernel :
      observableAccessKernel e = observableNoAccessKernel e := by
    ext base
    rw [hObservableAccess e base, hObservableNoAccess e base]
    exact congrArg (fun law : Measure Estimate => law _) (hobservable e base)
  rw [hDemographicAccess e, hDemographicNoAccess e, hkernel]

/--
Continuous source implication chain: latent-skill fairness implies observable
fairness, which implies demographic fairness, with both total-probability
mixtures explicit.
-/
theorem paper_continuous_fairness_implication_chain_of_kernel_mixtures
    {Skill Base Test Estimate : Type*}
    [MeasurableSpace Skill] [MeasurableSpace Base]
    [MeasurableSpace Estimate]
    {S : LG21SourceLawPolicySurface Skill Base Test (Measure Estimate)}
    (skillGivenBase : Kernel Base Skill)
    (baseLaw : Measure Base)
    (latentAccessKernel latentNoAccessKernel :
      S.Equilibrium → Base → Kernel Skill Estimate)
    (observableAccessKernel observableNoAccessKernel :
      S.Equilibrium → Kernel Base Estimate)
    (hLatentAccess :
      ∀ e base skill,
        latentAccessKernel e base skill =
          S.latentAccessLaw e skill base)
    (hLatentNoAccess :
      ∀ e base skill,
        latentNoAccessKernel e base skill =
          S.latentNoAccessLaw e skill base)
    (hObservableAccessLatent :
      ∀ e base,
        S.observableAccessLaw e base =
          Measure.bind (skillGivenBase base)
            (latentAccessKernel e base))
    (hObservableNoAccessLatent :
      ∀ e base,
        S.observableNoAccessLaw e base =
          Measure.bind (skillGivenBase base)
            (latentNoAccessKernel e base))
    (hObservableAccessKernel :
      ∀ e base,
        observableAccessKernel e base = S.observableAccessLaw e base)
    (hObservableNoAccessKernel :
      ∀ e base,
        observableNoAccessKernel e base = S.observableNoAccessLaw e base)
    (hDemographicAccess :
      ∀ e,
        S.demographicAccessLaw e =
          Measure.bind baseLaw (observableAccessKernel e))
    (hDemographicNoAccess :
      ∀ e,
        S.demographicNoAccessLaw e =
          Measure.bind baseLaw (observableNoAccessKernel e)) :
    (lg21SourceLawLatentSkillFair S →
        lg21SourceLawObservablyFair S) ∧
      (lg21SourceLawObservablyFair S →
        lg21SourceLawDemographicallyFair S) := by
  constructor
  · exact
      lg21_sourceLawObservablyFair_of_latentSkillFair_of_kernel_mixture
        skillGivenBase latentAccessKernel latentNoAccessKernel
        hLatentAccess hLatentNoAccess
        hObservableAccessLatent hObservableNoAccessLatent
  · exact
      lg21_sourceLawDemographicallyFair_of_observablyFair_of_kernel_mixture
        baseLaw observableAccessKernel observableNoAccessKernel
        hObservableAccessKernel hObservableNoAccessKernel
        hDemographicAccess hDemographicNoAccess

end

end LG21TestOptionalPolicies
