import KR21Monoculture.LaplaceSourceNormalization
import AppliedModelingLib.Foundations.Probability.NormalizedKernelDensity

open AppliedModelingLib MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace KR21Monoculture

/-!
# Semantic outer measurability for the KR21 RUM source laws

The Gaussian and source-normalized Laplace laws are induced by normalized,
jointly measurable score densities on a fixed three-score space.  This module
uses those densities to derive measurability of ranking atoms in the outer
value profile; it does not accept atom measurability as a caller certificate.
-/

/-- The canonical Gaussian three-score density is jointly measurable in the
outer value profile and the realized scores. -/
theorem measurable_gaussianCanonicalScoreDensity :
    Measurable (Function.uncurry (fun value : ValueProfile 1 =>
      rum3ScoreDensityENN (theorem8GaussianPDF 0)
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1))
        rum3Score1 rum3Score2 rum3Score3)) := by
  have h1 : Measurable (fun p : ValueProfile 1 × RUM3ScoreSpace =>
      theorem8GaussianPDF 0
        (rum3Score1 p.2 - p.1 (0 : Candidate 1))) :=
    (theorem8GaussianPDF_measurable 0).comp
      ((rum3Score1_measurable.comp measurable_snd).sub
        ((measurable_pi_apply (0 : Candidate 1)).comp measurable_fst))
  have h2 : Measurable (fun p : ValueProfile 1 × RUM3ScoreSpace =>
      theorem8GaussianPDF 0
        (rum3Score2 p.2 - p.1 (1 : Candidate 1))) :=
    (theorem8GaussianPDF_measurable 0).comp
      ((rum3Score2_measurable.comp measurable_snd).sub
        ((measurable_pi_apply (1 : Candidate 1)).comp measurable_fst))
  have h3 : Measurable (fun p : ValueProfile 1 × RUM3ScoreSpace =>
      theorem8GaussianPDF 0
        (rum3Score3 p.2 - p.1 (2 : Candidate 1))) :=
    (theorem8GaussianPDF_measurable 0).comp
      ((rum3Score3_measurable.comp measurable_snd).sub
        ((measurable_pi_apply (2 : Candidate 1)).comp measurable_fst))
  simpa only [Function.uncurry, rum3ScoreDensityENN,
    AppliedModelingLib.Probability.rum3ScoreDensityENN] using
    (h1.mul h2 |>.mul h3).ennreal_ofReal

/-- The canonical Gaussian score law, viewed as a Markov kernel over value
profiles. -/
noncomputable def gaussianCanonicalScoreKernelDensity :
    AppliedModelingLib.Probability.NormalizedKernelDensity (ValueProfile 1)
      RUM3ScoreSpace (volume : Measure RUM3ScoreSpace) where
  density := fun value =>
    rum3ScoreDensityENN (theorem8GaussianPDF 0)
      (value (0 : Candidate 1)) (value (1 : Candidate 1))
      (value (2 : Candidate 1))
      rum3Score1 rum3Score2 rum3Score3
  density_measurable := measurable_gaussianCanonicalScoreDensity
  integral_eq_one := fun value =>
    rum3ScoreDensityENN_gaussian_zero_lintegral_eq_one
      (value (0 : Candidate 1)) (value (1 : Candidate 1))
      (value (2 : Candidate 1))

/-- The score cell for a concrete ranking is Borel. -/
theorem measurableSet_rum3Score_rankingAtom (pi : Ranking 1) :
    MeasurableSet {omega : RUM3ScoreSpace |
      rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 omega = pi} :=
  measurableSet_eq_fun
    (rum3RankByScoreFns_measurable
      rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable)
    measurable_const

/-- A fixed ranking cell has Borel mass under the canonical Gaussian
score-density kernel. -/
theorem measurable_gaussianCanonicalScoreKernel_rankingAtom (pi : Ranking 1) :
    Measurable (fun value : ValueProfile 1 =>
      (gaussianCanonicalScoreKernelDensity.toKernel value
        {omega : RUM3ScoreSpace |
          rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 omega = pi}).toReal) :=
  (Kernel.measurable_coe gaussianCanonicalScoreKernelDensity.toKernel
    (measurableSet_rum3Score_rankingAtom pi)).ennreal_toReal

/-- Evaluating the Gaussian score-density kernel at a profile produces the
ordinary with-density score law. -/
theorem gaussianCanonicalScoreKernelDensity_toKernel_apply
    (value : ValueProfile 1) :
    gaussianCanonicalScoreKernelDensity.toKernel value =
      (volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN (theorem8GaussianPDF 0)
          (value (0 : Candidate 1)) (value (1 : Candidate 1))
          (value (2 : Candidate 1))
          rum3Score1 rum3Score2 rum3Score3) := by
  rw [AppliedModelingLib.Probability.NormalizedKernelDensity.toKernel_eq_withDensity,
    Kernel.withDensity_apply (Kernel.const (ValueProfile 1)
      (volume : Measure RUM3ScoreSpace))
      gaussianCanonicalScoreKernelDensity.density_measurable]
  rfl

/-- The ranking law induced directly by the canonical score-density kernel. -/
noncomputable def gaussianCanonicalScoreRankingLaw
    (value : ValueProfile 1) : PMF (Ranking 1) := by
  letI : IsMarkovKernel gaussianCanonicalScoreKernelDensity.toKernel :=
    gaussianCanonicalScoreKernelDensity.toKernel_isMarkov
  exact rumRankingPMFOfMeasure
    (gaussianCanonicalScoreKernelDensity.toKernel value)
    (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3)
    (rum3RankByScoreFns_measurable
      rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable)

/-- An atom of the score-induced ranking law is exactly the corresponding
Borel score-cell mass of the kernel. -/
theorem gaussianCanonicalScoreRankingLaw_atom_eq_kernelAtom
    (value : ValueProfile 1) (pi : Ranking 1) :
    ((gaussianCanonicalScoreRankingLaw value) pi).toReal =
      (gaussianCanonicalScoreKernelDensity.toKernel value
        {omega : RUM3ScoreSpace |
          rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 omega = pi}).toReal := by
  letI : IsMarkovKernel gaussianCanonicalScoreKernelDensity.toKernel :=
    gaussianCanonicalScoreKernelDensity.toKernel_isMarkov
  rw [gaussianCanonicalScoreRankingLaw, ← pmfProb_singleton]
  rw [rumRankingPMFOfMeasure_eventProb]
  rfl

/-- The score-density ranking law agrees with the established canonical
Gaussian Definition-2 ranking law. -/
theorem gaussianCanonicalScoreRankingLaw_eq_definition2
    (value : ValueProfile 1) :
    gaussianCanonicalScoreRankingLaw value =
      rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasure
          (value (0 : Candidate 1)) (value (1 : Candidate 1))
          (value (2 : Candidate 1)))
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable) := by
  letI : IsMarkovKernel gaussianCanonicalScoreKernelDensity.toKernel :=
    gaussianCanonicalScoreKernelDensity.toKernel_isMarkov
  let e : RUM3ScoreSpace ≃ᵐ Theorem8GaussianDefinition2ScoreSpace :=
    MeasurableEquiv.prodAssoc
  have he : MeasurePreserving e
      (gaussianCanonicalScoreKernelDensity.toKernel value)
      (theorem8GaussianDefinition2ScoreMeasure
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1))) := by
    rw [gaussianCanonicalScoreKernelDensity_toKernel_apply]
    simpa [e] using
      (rum3ScoreMeasure_gaussian_zero_prodAssoc_measurePreserving
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1)))
  unfold gaussianCanonicalScoreRankingLaw
  refine AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eq_of_measurePreserving
    (gaussianCanonicalScoreKernelDensity.toKernel value)
    (theorem8GaussianDefinition2ScoreMeasure
      (value (0 : Candidate 1)) (value (1 : Candidate 1))
      (value (2 : Candidate 1)))
    e he
    (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3)
    (rum3RankByScoreFns_measurable
      rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable)
    (rum3RankByScoreFns
      theorem8GaussianDefinition2Score1
      theorem8GaussianDefinition2Score2
      theorem8GaussianDefinition2Score3)
    (rum3RankByScoreFns_measurable
      theorem8GaussianDefinition2Score1_measurable
      theorem8GaussianDefinition2Score2_measurable
      theorem8GaussianDefinition2Score3_measurable)
    ?_
  intro omega
  rfl

/-- Each ranking atom of the canonical Gaussian Definition-2 law is Borel in
the value profile. -/
theorem measurable_gaussianDefinition2CanonicalRankingAtom (pi : Ranking 1) :
    Measurable (fun value : ValueProfile 1 =>
      ((rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasure
          (value (0 : Candidate 1)) (value (1 : Candidate 1))
          (value (2 : Candidate 1)))
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) pi).toReal) := by
  convert measurable_gaussianCanonicalScoreKernel_rankingAtom pi using 1
  funext value
  rw [← gaussianCanonicalScoreRankingLaw_atom_eq_kernelAtom,
    gaussianCanonicalScoreRankingLaw_eq_definition2]

/-- The profile rescaling that transports a positive-variance Gaussian score
law to the canonical variance-one-half score law. -/
noncomputable def gaussianCanonicalScaledProfile
    (theta : ℝ) (value : ValueProfile 1) : ValueProfile 1 :=
  fun candidate => theorem8GaussianCanonicalScale (1 / theta) * value candidate

theorem measurable_gaussianCanonicalScaledProfile (theta : ℝ) :
    Measurable (gaussianCanonicalScaledProfile theta) := by
  apply measurable_pi_lambda
  intro candidate
  exact measurable_const.mul (measurable_pi_apply candidate)

/-- At positive source accuracy, the actual Gaussian source atom is the
canonical score-density atom evaluated at its semantically scaled profile. -/
theorem gaussianThreeCandidateDistributionalFamily_atom_eq_canonical
    {theta : ℝ} (htheta : 0 < theta)
    (value : ValueProfile 1) (pi : Ranking 1) :
    ((gaussianThreeCandidateDistributionalFamily.dist theta value) pi).toReal =
      ((rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasure
          (gaussianCanonicalScaledProfile theta value (0 : Candidate 1))
          (gaussianCanonicalScaledProfile theta value (1 : Candidate 1))
          (gaussianCanonicalScaledProfile theta value (2 : Candidate 1)))
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) pi).toReal := by
  have hsigma : 0 < 1 / theta := one_div_pos.mpr htheta
  have hlaw := theorem8GaussianDefinition2RankingPMFStd_canonical_eq
    (σ := 1 / theta)
    (x1 := value (0 : Candidate 1))
    (x2 := value (1 : Candidate 1))
    (x3 := value (2 : Candidate 1)) hsigma
  exact congrArg (fun law : PMF (Ranking 1) => (law pi).toReal)
    (by simpa [gaussianThreeCandidateDistributionalFamily_dist,
      gaussianThreeCandidateRankingLaw, gaussianCanonicalScaledProfile] using hlaw)

/-- Each actual Gaussian source ranking atom is Borel in the outer value
profile at every positive source accuracy. -/
theorem measurable_gaussianThreeCandidateDistributionalFamily_rankingAtom
    {theta : ℝ} (htheta : 0 < theta) (pi : Ranking 1) :
    Measurable (fun value : ValueProfile 1 =>
      ((gaussianThreeCandidateDistributionalFamily.dist theta value) pi).toReal) := by
  have hcanonical := (measurable_gaussianDefinition2CanonicalRankingAtom pi).comp
    (measurable_gaussianCanonicalScaledProfile theta)
  convert hcanonical using 1
  funext value
  exact gaussianThreeCandidateDistributionalFamily_atom_eq_canonical
    htheta value pi

/-- Borel atom regularity yields the needed AEStrong measurability under any
outer value law. -/
theorem aestronglyMeasurable_gaussianThreeCandidateDistributionalFamily_rankingAtom
    (D : Measure (ValueProfile 1)) {theta : ℝ} (htheta : 0 < theta)
    (pi : Ranking 1) :
    AEStronglyMeasurable (fun value : ValueProfile 1 =>
      ((gaussianThreeCandidateDistributionalFamily.dist theta value) pi).toReal) D :=
  (measurable_gaussianThreeCandidateDistributionalFamily_rankingAtom htheta pi).aestronglyMeasurable

/-- A fixed positive-rate Laplace three-score density is jointly measurable in
the outer value profile and realized scores. -/
theorem measurable_laplaceScoreDensity (lam : ℝ) :
    Measurable (Function.uncurry (fun value : ValueProfile 1 =>
      rum3ScoreDensityENN (theorem7LaplacePDF lam 0)
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1))
        rum3Score1 rum3Score2 rum3Score3)) := by
  have h1 : Measurable (fun p : ValueProfile 1 × RUM3ScoreSpace =>
      theorem7LaplacePDF lam 0
        (rum3Score1 p.2 - p.1 (0 : Candidate 1))) :=
    (theorem7LaplacePDF_measurable lam 0).comp
      ((rum3Score1_measurable.comp measurable_snd).sub
        ((measurable_pi_apply (0 : Candidate 1)).comp measurable_fst))
  have h2 : Measurable (fun p : ValueProfile 1 × RUM3ScoreSpace =>
      theorem7LaplacePDF lam 0
        (rum3Score2 p.2 - p.1 (1 : Candidate 1))) :=
    (theorem7LaplacePDF_measurable lam 0).comp
      ((rum3Score2_measurable.comp measurable_snd).sub
        ((measurable_pi_apply (1 : Candidate 1)).comp measurable_fst))
  have h3 : Measurable (fun p : ValueProfile 1 × RUM3ScoreSpace =>
      theorem7LaplacePDF lam 0
        (rum3Score3 p.2 - p.1 (2 : Candidate 1))) :=
    (theorem7LaplacePDF_measurable lam 0).comp
      ((rum3Score3_measurable.comp measurable_snd).sub
        ((measurable_pi_apply (2 : Candidate 1)).comp measurable_fst))
  simpa only [Function.uncurry, rum3ScoreDensityENN,
    AppliedModelingLib.Probability.rum3ScoreDensityENN] using
    (h1.mul h2 |>.mul h3).ennreal_ofReal

/-- A positive-rate Laplace score density, normalized as a Markov kernel over
outer value profiles. -/
noncomputable def laplaceScoreKernelDensity
    (lam : ℝ) (hlam : 0 < lam) :
    AppliedModelingLib.Probability.NormalizedKernelDensity (ValueProfile 1)
      RUM3ScoreSpace (volume : Measure RUM3ScoreSpace) where
  density := fun value =>
    rum3ScoreDensityENN (theorem7LaplacePDF lam 0)
      (value (0 : Candidate 1)) (value (1 : Candidate 1))
      (value (2 : Candidate 1))
      rum3Score1 rum3Score2 rum3Score3
  density_measurable := measurable_laplaceScoreDensity lam
  integral_eq_one := fun value =>
    rum3ScoreDensityENN_laplace_zero_lintegral_eq_one hlam
      (value (0 : Candidate 1)) (value (1 : Candidate 1))
      (value (2 : Candidate 1))

/-- A fixed ranking cell has Borel mass under the normalized Laplace
score-density kernel. -/
theorem measurable_laplaceScoreKernel_rankingAtom
    (lam : ℝ) (hlam : 0 < lam) (pi : Ranking 1) :
    Measurable (fun value : ValueProfile 1 =>
      ((laplaceScoreKernelDensity lam hlam).toKernel value
        {omega : RUM3ScoreSpace |
          rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 omega = pi}).toReal) :=
  (Kernel.measurable_coe (laplaceScoreKernelDensity lam hlam).toKernel
    (measurableSet_rum3Score_rankingAtom pi)).ennreal_toReal

/-- Evaluating the Laplace score-density kernel produces the ordinary
with-density score law. -/
theorem laplaceScoreKernelDensity_toKernel_apply
    (lam : ℝ) (hlam : 0 < lam) (value : ValueProfile 1) :
    (laplaceScoreKernelDensity lam hlam).toKernel value =
      (volume : Measure RUM3ScoreSpace).withDensity
        (rum3ScoreDensityENN (theorem7LaplacePDF lam 0)
          (value (0 : Candidate 1)) (value (1 : Candidate 1))
          (value (2 : Candidate 1))
          rum3Score1 rum3Score2 rum3Score3) := by
  rw [AppliedModelingLib.Probability.NormalizedKernelDensity.toKernel_eq_withDensity,
    Kernel.withDensity_apply (Kernel.const (ValueProfile 1)
      (volume : Measure RUM3ScoreSpace))
      (laplaceScoreKernelDensity lam hlam).density_measurable]
  rfl

/-- The ranking law induced directly by a positive-rate Laplace score-density
kernel. -/
noncomputable def laplaceScoreRankingLaw
    (lam : ℝ) (hlam : 0 < lam) (value : ValueProfile 1) : PMF (Ranking 1) := by
  letI : IsMarkovKernel (laplaceScoreKernelDensity lam hlam).toKernel :=
    (laplaceScoreKernelDensity lam hlam).toKernel_isMarkov
  exact rumRankingPMFOfMeasure
    ((laplaceScoreKernelDensity lam hlam).toKernel value)
    (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3)
    (rum3RankByScoreFns_measurable
      rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable)

/-- An atom of the score-induced Laplace ranking law is the Borel score-cell
mass of the kernel. -/
theorem laplaceScoreRankingLaw_atom_eq_kernelAtom
    (lam : ℝ) (hlam : 0 < lam) (value : ValueProfile 1) (pi : Ranking 1) :
    ((laplaceScoreRankingLaw lam hlam value) pi).toReal =
      ((laplaceScoreKernelDensity lam hlam).toKernel value
        {omega : RUM3ScoreSpace |
          rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3 omega = pi}).toReal := by
  letI : IsMarkovKernel (laplaceScoreKernelDensity lam hlam).toKernel :=
    (laplaceScoreKernelDensity lam hlam).toKernel_isMarkov
  rw [laplaceScoreRankingLaw, ← pmfProb_singleton]
  rw [rumRankingPMFOfMeasure_eventProb]
  rfl

/-- The score-density ranking law agrees with the established positive-rate
Laplace Definition-2 ranking law. -/
theorem laplaceScoreRankingLaw_eq_definition2
    (lam : ℝ) (hlam : 0 < lam) (value : ValueProfile 1) :
    laplaceScoreRankingLaw lam hlam value =
      theorem7LaplacianDefinition2RankingPMF lam
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1)) hlam := by
  letI : IsMarkovKernel (laplaceScoreKernelDensity lam hlam).toKernel :=
    (laplaceScoreKernelDensity lam hlam).toKernel_isMarkov
  let e : RUM3ScoreSpace ≃ᵐ Theorem7LaplacianDefinition2ScoreSpace :=
    MeasurableEquiv.prodAssoc
  have he : MeasurePreserving e
      ((laplaceScoreKernelDensity lam hlam).toKernel value)
      (theorem7LaplacianDefinition2ScoreMeasure lam
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1))) := by
    rw [laplaceScoreKernelDensity_toKernel_apply]
    simpa [e] using
      (rum3ScoreMeasure_laplace_zero_prodAssoc_measurePreserving
        (lam := lam) hlam
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1)))
  letI : IsProbabilityMeasure
      (theorem7LaplacianDefinition2ScoreMeasure lam
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1))) :=
    theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure hlam
  unfold laplaceScoreRankingLaw theorem7LaplacianDefinition2RankingPMF
  exact AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eq_of_measurePreserving
    ((laplaceScoreKernelDensity lam hlam).toKernel value)
    (theorem7LaplacianDefinition2ScoreMeasure lam
      (value (0 : Candidate 1)) (value (1 : Candidate 1))
      (value (2 : Candidate 1)))
    e he
    (rum3RankByScoreFns rum3Score1 rum3Score2 rum3Score3)
    (rum3RankByScoreFns_measurable
      rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable)
    (rum3RankByScoreFns
      theorem7LaplacianDefinition2Score1
      theorem7LaplacianDefinition2Score2
      theorem7LaplacianDefinition2Score3)
    (rum3RankByScoreFns_measurable
      theorem7LaplacianDefinition2Score1_measurable
      theorem7LaplacianDefinition2Score2_measurable
      theorem7LaplacianDefinition2Score3_measurable)
    (by intro omega; rfl)

/-- Each ranking atom of the positive-rate Laplace Definition-2 law is Borel
in the value profile. -/
theorem measurable_laplaceDefinition2RankingAtom
    (lam : ℝ) (hlam : 0 < lam) (pi : Ranking 1) :
    Measurable (fun value : ValueProfile 1 =>
      ((theorem7LaplacianDefinition2RankingPMF lam
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1)) hlam) pi).toReal) := by
  convert measurable_laplaceScoreKernel_rankingAtom lam hlam pi using 1
  funext value
  rw [← laplaceScoreRankingLaw_atom_eq_kernelAtom,
    laplaceScoreRankingLaw_eq_definition2]

/-- Each ranking atom of the source-normalized Laplace family is Borel in the
outer value profile at every positive source accuracy. -/
theorem measurable_sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_rankingAtom
    {theta : ℝ} (htheta : 0 < theta) (pi : Ranking 1) :
    Measurable (fun value : ValueProfile 1 =>
      ((sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value) pi).toReal) := by
  let lam := sourceUnitVarianceLaplaceRate theta
  have hlam : 0 < lam := by
    dsimp [lam]
    exact sourceUnitVarianceLaplaceRate_pos htheta
  have hcanonical := measurable_laplaceDefinition2RankingAtom lam hlam pi
  convert hcanonical using 1
  funext value
  simpa [lam, sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_dist] using
    congrArg (fun law : PMF (Ranking 1) => (law pi).toReal)
      (laplaceThreeCandidateRankingLaw_eq_of_pos
        (theta := lam) (x1 := value (0 : Candidate 1))
        (x2 := value (1 : Candidate 1)) (x3 := value (2 : Candidate 1)) hlam)

/-- Borel Laplace ranking atoms are AEStronglyMeasurable under every outer
value law. -/
theorem aestronglyMeasurable_sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_rankingAtom
    (D : Measure (ValueProfile 1)) {theta : ℝ} (htheta : 0 < theta)
    (pi : Ranking 1) :
    AEStronglyMeasurable (fun value : ValueProfile 1 =>
      ((sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value) pi).toReal) D :=
  (measurable_sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_rankingAtom
    htheta pi).aestronglyMeasurable

end KR21Monoculture
