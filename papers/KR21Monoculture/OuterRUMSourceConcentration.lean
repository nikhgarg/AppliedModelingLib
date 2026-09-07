import KR21Monoculture.OuterRUMTheorem1Lift
import KR21Monoculture.LaplaceSourceNormalization

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace KR21Monoculture

/-!
# KR21 source RUM concentration under an outer value law

The source fixes the candidate labels in decreasing true-value order before
introducing its joint outer law `D`.  This module records the analytic part of
that convention which the outer Theorem 1 lift needs: the concrete Gaussian
and source-normalized Laplace score laws converge, atom by atom, to that fixed
ranking center on the ordered support of `D`.

The underlying RUM developments already prove the relevant adjacent-inversion
probabilities tend to zero.  Their older `atomwise_concentration` interfaces
only select a single sufficiently high accuracy.  Here we retain their
eventual bounds and prove the genuine filter convergence required by dominated
convergence over `D`.
-/

namespace DistributionalAccuracyFamily

/-- A value-dependent finite PMF payoff selecting one candidate coordinate is
integrable under coordinatewise first moments and measurable ranking atoms. -/
theorem integrable_outer_pmfExp_valueSelection_of_atomwise
    {n : ℕ} {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (D : Measure (ValueProfile n))
    (law : ℝ → ValueProfile n → PMF alpha) (theta : ℝ)
    (select : alpha → Candidate n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_measurable : ∀ a,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((law theta value) a).toReal) D) :
    Integrable (fun value => AppliedModelingLib.pmfExp (law theta value)
      (fun a => value (select a))) D := by
  unfold AppliedModelingLib.pmfExp
  refine MeasureTheory.integrable_finset_sum Finset.univ ?_
  intro a _
  refine (hvalue (select a)).abs.mono' ?_ ?_
  · exact (hatom_measurable a).mul
      (hvalue (select a)).aestronglyMeasurable
  · filter_upwards with value
    change |((law theta value) a).toReal * value (select a)| ≤
      |value (select a)|
    rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    simpa [mul_comm] using
      (mul_le_of_le_one_right (abs_nonneg (value (select a)))
        (AppliedModelingLib.pmf_apply_toReal_le_one (law theta value) a))

/-- A value-dependent finite independent-pair payoff selecting one candidate
coordinate is integrable under the same first moments and atom
measurability. -/
theorem integrable_outer_pmfPairExp_valueSelection_of_atomwise
    {n : ℕ} {alpha beta : Type*}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (D : Measure (ValueProfile n))
    (leftLaw : ValueProfile n → PMF alpha)
    (rightLaw : ValueProfile n → PMF beta)
    (select : alpha → beta → Candidate n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hleft_measurable : ∀ a,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((leftLaw value) a).toReal) D)
    (hright_measurable : ∀ b,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((rightLaw value) b).toReal) D) :
    Integrable (fun value => AppliedModelingLib.pmfPairExp (leftLaw value)
      (rightLaw value) (fun a b => value (select a b))) D := by
  let term : alpha → beta → ValueProfile n → ℝ :=
    fun a b value =>
      ((leftLaw value) a).toReal * ((rightLaw value) b).toReal *
        value (select a b)
  have hterm : ∀ a b, Integrable (term a b) D := by
    intro a b
    refine (hvalue (select a b)).abs.mono' ?_ ?_
    · exact ((hleft_measurable a).mul (hright_measurable b)).mul
        (hvalue (select a b)).aestronglyMeasurable
    · filter_upwards with value
      dsimp [term]
      change |((leftLaw value) a).toReal * ((rightLaw value) b).toReal *
        value (select a b)| ≤ |value (select a b)|
      rw [abs_mul, abs_mul,
        abs_of_nonneg ENNReal.toReal_nonneg,
        abs_of_nonneg ENNReal.toReal_nonneg]
      calc
        ((leftLaw value) a).toReal * ((rightLaw value) b).toReal *
            |value (select a b)| =
          ((leftLaw value) a).toReal *
            (((rightLaw value) b).toReal * |value (select a b)|) := by
              ring
        _ ≤ ((rightLaw value) b).toReal * |value (select a b)| := by
          rw [mul_comm]
          exact mul_le_of_le_one_right
            (mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))
            (AppliedModelingLib.pmf_apply_toReal_le_one (leftLaw value) a)
        _ ≤ |value (select a b)| := by
          rw [mul_comm]
          exact mul_le_of_le_one_right (abs_nonneg (value (select a b)))
            (AppliedModelingLib.pmf_apply_toReal_le_one (rightLaw value) b)
  have hrewrite :
      (fun value => AppliedModelingLib.pmfPairExp (leftLaw value) (rightLaw value)
        (fun a b => value (select a b))) =
      fun value => ∑ a, ∑ b, term a b value := by
    funext value
    unfold AppliedModelingLib.pmfPairExp AppliedModelingLib.pmfExp
    simp_rw [Finset.mul_sum]
    simp only [term, mul_assoc]
  rw [hrewrite]
  exact MeasureTheory.integrable_finset_sum Finset.univ
    (fun a _ => MeasureTheory.integrable_finset_sum Finset.univ
      (fun b _ => hterm a b))

end DistributionalAccuracyFamily

/-- The paper's fixed source-label order `x₁ > x₂ > x₃` is precisely strict
ordering by the concrete ranking `[0, 1, 2]`.  This is a semantic conversion
of the displayed coordinate inequalities, not a sorting or relabelling claim
about an arbitrary identity-labelled profile. -/
theorem strictlyOrderedBy_rum3Ranking012_of_source_order
    {value : ValueProfile 1}
    (horder : value (1 : Candidate 1) < value (0 : Candidate 1) ∧
      value (2 : Candidate 1) < value (1 : Candidate 1)) :
    StrictlyOrderedBy rum3Ranking012 value := by
  have hcenter : rum3Ranking012 = Equiv.refl (Candidate 1) := by
    ext candidate
    fin_cases candidate <;> simp [rum3Ranking012]
  rw [hcenter]
  have href : StrictlyOrderedBy (Equiv.refl (Candidate 1)) value :=
    strictlyOrderedBy_refl_threeCandidate_of_values
      (value := value) (x1 := value 0) (x2 := value 1) (x3 := value 2)
      rfl rfl rfl horder.1 horder.2
  exact @href

/-- The source's rank-labelled outer-law convention transports directly to the
fixed center used by the outer Theorem 1 lift. -/
theorem ae_strictlyOrderedBy_rum3Ranking012_of_source_order
    (D : Measure (ValueProfile 1))
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1)) :
    ∀ᵐ value ∂D, StrictlyOrderedBy rum3Ranking012 value := by
  filter_upwards [horder] with value hvalue
  exact strictlyOrderedBy_rum3Ranking012_of_source_order hvalue

/-- At every positive source accuracy, each Gaussian RUM ranking atom is
continuous in the literal `1 / theta` source parameterization. -/
theorem gaussianThreeCandidateDistributionalFamily_atom_epsilonContinuousAt
    {theta : ℝ} (htheta : 0 < theta)
    (value : ValueProfile 1) (pi : Ranking 1) :
    AppliedModelingLib.EpsilonContinuousAt
      (fun theta' : ℝ =>
        ((gaussianThreeCandidateDistributionalFamily.dist theta' value) pi).toReal)
      theta := by
  simpa [gaussianThreeCandidateDistributionalFamily,
    gaussianThreeCandidateRankingLaw] using
    (theorem8GaussianDefinition2RankingPMFStd_atom_epsilonContinuousAt
      (θ := theta)
      (x1 := value (0 : Candidate 1))
      (x2 := value (1 : Candidate 1))
      (x3 := value (2 : Candidate 1)) htheta pi)

/-- At every positive source accuracy, each source-normalized Laplace RUM
ranking atom is continuous after the explicit rate change `sqrt 2 * theta`. -/
theorem sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_atom_epsilonContinuousAt
    {theta : ℝ} (htheta : 0 < theta)
    (value : ValueProfile 1) (pi : Ranking 1) :
    AppliedModelingLib.EpsilonContinuousAt
      (fun theta' : ℝ =>
        ((sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta' value) pi).toReal)
      theta := by
  let rate : ℝ → ℝ := sourceUnitVarianceLaplaceRate
  have hrate_theta : 0 < rate theta := by
    simpa [rate] using sourceUnitVarianceLaplaceRate_pos htheta
  let source : ℝ → ℝ := fun lambda : ℝ =>
    if hlambda : 0 < lambda then
      ((theorem7LaplacianDefinition2RankingPMF lambda
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1)) hlambda) pi).toReal
    else
      ((theorem7LaplacianDefinition2RankingPMF (rate theta)
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1)) hrate_theta) pi).toReal
  have hsource : AppliedModelingLib.EpsilonContinuousAt source (rate theta) := by
    simpa [source] using
      (theorem7LaplacianDefinition2RankingPMF_canonical_atom_epsilonContinuousAt
        (θ := rate theta)
        (x1 := value (0 : Candidate 1))
        (x2 := value (1 : Candidate 1))
        (x3 := value (2 : Candidate 1)) hrate_theta pi)
  have hrate_continuous : ContinuousAt rate theta := by
    change ContinuousAt (fun theta' : ℝ => Real.sqrt 2 * theta') theta
    fun_prop
  have hcomp : AppliedModelingLib.EpsilonContinuousAt
      (fun theta' : ℝ => source (rate theta')) theta :=
    AppliedModelingLib.epsilonContinuousAt_comp_of_continuousAt hsource hrate_continuous
  refine AppliedModelingLib.epsilonContinuousAt_congr_eventually hcomp ?_ ?_
  · filter_upwards [Ioi_mem_nhds htheta] with theta' htheta'
    have htheta'_pos : 0 < theta' := htheta'
    have hrate_theta' : 0 < rate theta' := by
      simpa [rate] using sourceUnitVarianceLaplaceRate_pos htheta'_pos
    have hrate_concrete : 0 < Real.sqrt 2 * theta' := by
      simpa [rate] using hrate_theta'
    change source (rate theta') =
      ((sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta' value) pi).toReal
    simp only [source, dif_pos hrate_theta']
    rw [sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_dist,
      laplaceThreeCandidateRankingLaw_eq_of_pos hrate_concrete]
    dsimp [rate]
  · have hrate_concrete : 0 < Real.sqrt 2 * theta := by
      simpa [rate] using hrate_theta
    change source (rate theta) =
      ((sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value) pi).toReal
    simp only [source, dif_pos hrate_theta]
    rw [sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_dist,
      laplaceThreeCandidateRankingLaw_eq_of_pos hrate_concrete]
    dsimp [rate]

/-- For an ordered three-candidate profile, the Gaussian source RUM law
converges atomwise to the fixed source ranking `[0, 1, 2]` as its literal
source accuracy parameter tends to infinity. -/
theorem gaussianThreeCandidateRankingLaw_atomwise_tendsto_pure012
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2)
    (pi : Ranking 1) :
    Tendsto
      (fun theta : ℝ =>
        ((gaussianThreeCandidateRankingLaw theta x1 x2 x3) pi).toReal)
      atTop
      (nhds (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) pi).toReal)) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro epsilon hepsilon
  have hsum :=
    theorem8GaussianDefinition2ScoreMeasureStd_adjacent_inversions_tendsto_atTop_zero
      (x1 := x1) (x2 := x2) (x3 := x3) hx12 hx23
  have hsmall : ∀ᶠ theta : ℝ in atTop,
      measureProb
          (theorem8GaussianDefinition2ScoreMeasureStd (1 / theta) x1 x2 x3)
          (fun omega =>
            theorem8GaussianDefinition2Score1 omega <
              theorem8GaussianDefinition2Score2 omega) +
        measureProb
          (theorem8GaussianDefinition2ScoreMeasureStd (1 / theta) x1 x2 x3)
          (fun omega =>
            theorem8GaussianDefinition2Score2 omega <
              theorem8GaussianDefinition2Score3 omega) < epsilon :=
    hsum.eventually (Iio_mem_nhds hepsilon)
  rcases Filter.eventually_atTop.1 hsmall with ⟨lower, hlower⟩
  refine ⟨lower, ?_⟩
  intro theta htheta
  rw [Real.dist_eq]
  let mu := theorem8GaussianDefinition2ScoreMeasureStd (1 / theta) x1 x2 x3
  haveI : IsProbabilityMeasure mu := by
    dsimp [mu]
    infer_instance
  have hclose :=
    rumRankingPMFOfMeasure_rankByScoreFns_atomwise_close_to_pure012_of_pair_inversions_lt
      mu theorem8GaussianDefinition2Score1 theorem8GaussianDefinition2Score2
      theorem8GaussianDefinition2Score3
      (rum3RankByScoreFns_measurable
        theorem8GaussianDefinition2Score1_measurable
        theorem8GaussianDefinition2Score2_measurable
        theorem8GaussianDefinition2Score3_measurable)
      hepsilon (hlower theta htheta) pi
  simpa [gaussianThreeCandidateRankingLaw, mu] using hclose

/-- For an ordered three-candidate profile, the Laplace RUM with the paper's
unit-variance noise normalization converges atomwise to `[0, 1, 2]` as the
literal source accuracy parameter tends to infinity.  The proof uses the
explicit source conversion from accuracy to Laplace rate, `sqrt 2 * theta`. -/
theorem sourceUnitVarianceLaplaceThreeCandidateRankingLaw_atomwise_tendsto_pure012
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2)
    (pi : Ranking 1) :
    Tendsto
      (fun theta : ℝ =>
        ((sourceUnitVarianceLaplaceThreeCandidateRankingLaw theta x1 x2 x3) pi).toReal)
      atTop
      (nhds (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) pi).toReal)) := by
  have hrate : Tendsto (fun theta : ℝ => Real.sqrt 2 * theta) atTop atTop := by
    exact Tendsto.const_mul_atTop
      (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)) tendsto_id
  refine Metric.tendsto_atTop.mpr ?_
  intro epsilon hepsilon
  have hsum :=
    theorem7LaplacianDefinition2ScoreMeasure_adjacent_inversions_tendsto_atTop_zero
      (lam := fun theta : ℝ => Real.sqrt 2 * theta) hrate
      (x1 := x1) (x2 := x2) (x3 := x3) hx12 hx23
  have hsmall : ∀ᶠ theta : ℝ in atTop,
      measureProb
          (theorem7LaplacianDefinition2ScoreMeasure
            (Real.sqrt 2 * theta) x1 x2 x3)
          (fun omega =>
            theorem7LaplacianDefinition2Score1 omega <
              theorem7LaplacianDefinition2Score2 omega) +
        measureProb
          (theorem7LaplacianDefinition2ScoreMeasure
            (Real.sqrt 2 * theta) x1 x2 x3)
          (fun omega =>
            theorem7LaplacianDefinition2Score2 omega <
              theorem7LaplacianDefinition2Score3 omega) < epsilon :=
    hsum.eventually (Iio_mem_nhds hepsilon)
  have hrate_pos : ∀ᶠ theta : ℝ in atTop, 0 < Real.sqrt 2 * theta :=
    hrate.eventually (eventually_gt_atTop 0)
  rcases Filter.eventually_atTop.1 (hsmall.and hrate_pos) with ⟨lower, hlower⟩
  refine ⟨lower, ?_⟩
  intro theta htheta
  rw [Real.dist_eq]
  have hpair := (hlower theta htheta).1
  have hpositive := (hlower theta htheta).2
  let mu := theorem7LaplacianDefinition2ScoreMeasure
    (Real.sqrt 2 * theta) x1 x2 x3
  haveI : IsProbabilityMeasure mu :=
    theorem7LaplacianDefinition2ScoreMeasure_isProbabilityMeasure
      (lam := Real.sqrt 2 * theta) (x1 := x1) (x2 := x2) (x3 := x3) hpositive
  have hclose :=
    rumRankingPMFOfMeasure_rankByScoreFns_atomwise_close_to_pure012_of_pair_inversions_lt
      mu theorem7LaplacianDefinition2Score1 theorem7LaplacianDefinition2Score2
      theorem7LaplacianDefinition2Score3
      (rum3RankByScoreFns_measurable
        theorem7LaplacianDefinition2Score1_measurable
        theorem7LaplacianDefinition2Score2_measurable
        theorem7LaplacianDefinition2Score3_measurable)
      hepsilon (by simpa [mu] using hpair) pi
  simpa [sourceUnitVarianceLaplaceThreeCandidateRankingLaw,
    laplaceThreeCandidateRankingLaw_eq_of_pos hpositive, mu] using hclose

/-- The Gaussian source family satisfies the outer lift's atomwise convergence
premise on every outer law supported on the source's fixed ordered cone. -/
theorem gaussianThreeCandidate_ae_atomwise_tendsto_pure012_of_source_order
    (D : Measure (ValueProfile 1))
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1)) :
    ∀ᵐ value ∂D, ∀ pi : Ranking 1,
      Tendsto
        (fun theta : ℝ =>
          ((gaussianThreeCandidateDistributionalFamily.dist theta value) pi).toReal)
        atTop
        (nhds (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) pi).toReal)) := by
  filter_upwards [horder] with value hvalue
  intro pi
  simpa using
    (gaussianThreeCandidateRankingLaw_atomwise_tendsto_pure012
      hvalue.1 hvalue.2 pi)

/-- The literal source-normalized Laplace family satisfies the same outer
atomwise convergence premise on the source's fixed ordered cone. -/
theorem sourceUnitVarianceLaplaceThreeCandidate_ae_atomwise_tendsto_pure012_of_source_order
    (D : Measure (ValueProfile 1))
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1)) :
    ∀ᵐ value ∂D, ∀ pi : Ranking 1,
      Tendsto
        (fun theta : ℝ =>
          ((sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value) pi).toReal)
        atTop
        (nhds (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) pi).toReal)) := by
  filter_upwards [horder] with value hvalue
  intro pi
  simpa using
    (sourceUnitVarianceLaplaceThreeCandidateRankingLaw_atomwise_tendsto_pure012
      hvalue.1 hvalue.2 pi)

end KR21Monoculture
