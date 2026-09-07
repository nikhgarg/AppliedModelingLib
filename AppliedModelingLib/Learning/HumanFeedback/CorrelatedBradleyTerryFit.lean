import AppliedModelingLib.Learning.HumanFeedback.PairwiseReportCounts
import AppliedModelingLib.Learning.HumanFeedback.BradleyTerryFitExistence

/-!
# Finite Bradley--Terry fitting under correlated pair sampling

The usual finite Bradley--Terry objective samples two alternatives
independently from one PMF.  Some alignment constructions instead choose an
unordered comparison pair from a correlated law.  This file provides the
corresponding ordered-pair presentation: a symmetric PMF on ordered pairs
encodes an unordered pair law by assigning half of each pair's mass to either
orientation.

The population objective is kept separate from finite count likelihoods.  Its
coordinate derivative is the weighted first-order equation used to analyse
correlated comparison designs.
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

/-- A finite comparison-pair sampler, distinct from an independently sampled
pair of alternatives. -/
abbrev CorrelatedPairSampling (Response : Type*) := PMF (Response × Response)

/-- The ordered presentation of an unordered comparison design is symmetric. -/
def CorrelatedPairSampling.IsSymmetric {Response : Type*}
    (sampling : CorrelatedPairSampling Response) : Prop :=
  ∀ first second,
    (sampling (first, second)).toReal = (sampling (second, first)).toReal

/-- A correlated comparison sampler gives positive mass to every distinct
ordered pair.  This is the full-support condition used for MLE existence. -/
def CorrelatedPairSampling.HasFullOffDiagonalSupport {Response : Type*}
    (sampling : CorrelatedPairSampling Response) : Prop :=
  ∀ first second, first ≠ second → 0 < (sampling (first, second)).toReal

/-- A correlated comparison law omits diagonal displays.  This is the natural
condition when the finite count likelihood has zero diagonal counts. -/
def CorrelatedPairSampling.HasZeroDiagonal {Response : Type*}
    (sampling : CorrelatedPairSampling Response) : Prop :=
  ∀ response, (sampling (response, response)).toReal = 0

/-- A real Bernoulli comparison outcome.  This small wrapper keeps the
probability bounds visible at the point where a population preference is
turned into a literal finite-data report law. -/
noncomputable def correlatedBernoulliReport (probability : ℝ)
    (hnonneg : 0 ≤ probability) (hle_one : probability ≤ 1) : PMF Bool :=
  PMF.bernoulli ⟨probability, hnonneg⟩ (by
    change probability ≤ (1 : ℝ)
    exact hle_one)

/-- One literal binary-comparison report from a correlated ordered-pair
sampling law.  Unlike the independent-product sampler, the displayed pair is
drawn directly from `sampling`. -/
noncomputable def correlatedOneComparisonReportLaw
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (sampling : CorrelatedPairSampling Response)
    (preference : PairwisePreference PUnit Response) :
    PMF (BinaryPairwiseReport Response) :=
  sampling.bind fun pair =>
    (correlatedBernoulliReport
      (preference.prob PUnit.unit pair.1 pair.2)
      (preference.nonneg PUnit.unit pair.1 pair.2)
      (preference.le_one PUnit.unit pair.1 pair.2)).map
        (fun outcome => (pair, outcome))

/-- Under full off-diagonal pair support and strictly interior preferences,
every direct-true report atom has positive mass in the correlated source
report law. -/
theorem correlatedOneComparisonReportLaw_directTrue_pos
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (sampling : CorrelatedPairSampling Response)
    (preference : PairwisePreference PUnit Response)
    (winner loser : Response) (hneq : winner ≠ loser)
    (hsampling : sampling.HasFullOffDiagonalSupport)
    (hpreference : ∀ first second,
      0 < preference.prob PUnit.unit first second) :
    0 < (correlatedOneComparisonReportLaw sampling preference
      (PairwiseCountDataset.directTrueBinaryReport winner loser)).toReal := by
  classical
  have hpair : (winner, loser) ∈ sampling.support := by
    rw [PMF.mem_support_iff]
    exact ne_of_gt (ENNReal.toReal_pos_iff.mp (hsampling winner loser hneq)).1
  have htrue : true ∈
      (correlatedBernoulliReport
        (preference.prob PUnit.unit winner loser)
        (preference.nonneg PUnit.unit winner loser)
        (preference.le_one PUnit.unit winner loser)).support := by
    rw [correlatedBernoulliReport, PMF.mem_support_bernoulli_iff]
    simp only [Bool.cond_true]
    apply ne_of_gt
    change 0 < preference.prob PUnit.unit winner loser
    exact hpreference winner loser
  have hinner : PairwiseCountDataset.directTrueBinaryReport winner loser ∈
      ((correlatedBernoulliReport
        (preference.prob PUnit.unit winner loser)
        (preference.nonneg PUnit.unit winner loser)
        (preference.le_one PUnit.unit winner loser)).map
          (fun outcome => ((winner, loser), outcome))).support := by
    rw [PMF.mem_support_map_iff]
    exact ⟨true, htrue, rfl⟩
  have houter : PairwiseCountDataset.directTrueBinaryReport winner loser ∈
      (sampling.bind fun pair =>
        (correlatedBernoulliReport
          (preference.prob PUnit.unit pair.1 pair.2)
          (preference.nonneg PUnit.unit pair.1 pair.2)
          (preference.le_one PUnit.unit pair.1 pair.2)).map
            (fun outcome => (pair, outcome))).support := by
    rw [PMF.mem_support_bind_iff]
    exact ⟨(winner, loser), hpair, hinner⟩
  have hsupported : PairwiseCountDataset.directTrueBinaryReport winner loser ∈
      (correlatedOneComparisonReportLaw sampling preference).support := by
    simpa [correlatedOneComparisonReportLaw] using houter
  exact ENNReal.toReal_pos
    ((PMF.mem_support_iff _ _).mp hsupported)
    ((correlatedOneComparisonReportLaw sampling preference).apply_ne_top _)

/-- The finite population Bradley--Terry objective under an arbitrary
correlated ordered-pair sampling law. -/
noncomputable def correlatedBradleyTerryFitObjective {Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response) (reward : Response → ℝ) : ℝ :=
  pmfExp sampling (fun pair =>
    preference.prob () pair.1 pair.2 *
      Real.log (Real.sigmoid (reward pair.1 - reward pair.2)))

/-- Expectation of an arbitrary real-valued function of one real Bernoulli
comparison outcome. -/
theorem correlatedBernoulliReport_pmfExp_apply
    (probability : ℝ) (hnonneg : 0 ≤ probability) (hle_one : probability ≤ 1)
    (value : Bool → ℝ) :
    pmfExp (correlatedBernoulliReport probability hnonneg hle_one) value =
      probability * value true + (1 - probability) * value false := by
  simp [pmfExp, correlatedBernoulliReport, PMF.bernoulli_apply]
  rw [NNReal.coe_sub]
  · rfl
  · change probability ≤ (1 : ℝ)
    exact hle_one

/-- The expected literal finite-data log likelihood for one report drawn from
a correlated pair sampler. -/
noncomputable def correlatedOneComparisonExpectedRawLogLikelihood
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (sampling : CorrelatedPairSampling Response)
    (preference : PairwisePreference PUnit Response)
    (score : PairwiseCountDataset.ScoreVector Response) : ℝ :=
  pmfExp (correlatedOneComparisonReportLaw sampling preference)
    (PairwiseCountDataset.binaryReportLogLikelihoodTerm Real.sigmoid score)

/-- The literal correlated report likelihood has the ordered-pair cross-entropy
form, including false outcomes as reversed directed wins. -/
theorem correlatedOneComparisonExpectedRawLogLikelihood_eq
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (sampling : CorrelatedPairSampling Response)
    (preference : PairwisePreference PUnit Response)
    (score : PairwiseCountDataset.ScoreVector Response) :
    correlatedOneComparisonExpectedRawLogLikelihood sampling preference score =
      pmfExp sampling (fun pair =>
        if pair.1 = pair.2 then 0 else
          preference.prob PUnit.unit pair.1 pair.2 *
              Real.log (Real.sigmoid (score pair.1 - score pair.2)) +
            (1 - preference.prob PUnit.unit pair.1 pair.2) *
              Real.log (Real.sigmoid (score pair.2 - score pair.1))) := by
  unfold correlatedOneComparisonExpectedRawLogLikelihood
    correlatedOneComparisonReportLaw
  rw [pmfExp_bind]
  apply pmfExp_congr
  rintro ⟨first, second⟩
  rw [pmfExp_map]
  rw [correlatedBernoulliReport_pmfExp_apply]
  by_cases hsame : first = second
  · subst second
    rw [PairwiseCountDataset.binaryReportLogLikelihoodTerm_diagonal,
      PairwiseCountDataset.binaryReportLogLikelihoodTerm_diagonal]
    simp
  · rw [PairwiseCountDataset.binaryReportLogLikelihoodTerm_direct_true
      Real.sigmoid score first second hsame]
    rw [PairwiseCountDataset.binaryReportLogLikelihoodTerm_reverse_false
      Real.sigmoid score second first (Ne.symm hsame)]
    simp [hsame, PairwiseCountDataset.randomUtilityWinProbability]

/-- The off-diagonal correlated population objective exactly matches the
literal count likelihood; diagonal displays have no finite-count term. -/
noncomputable def correlatedOneComparisonOffDiagonalFitObjective
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (sampling : CorrelatedPairSampling Response)
    (preference : PairwisePreference PUnit Response)
    (score : PairwiseCountDataset.ScoreVector Response) : ℝ :=
  pmfExp sampling (fun pair =>
    if pair.1 = pair.2 then 0 else
      preference.prob PUnit.unit pair.1 pair.2 *
        Real.log (Real.sigmoid (score pair.1 - score pair.2)))

/-- Swapping the two coordinates inside a finite expectation preserves it
under a symmetric correlated pair sampler. -/
theorem correlatedPairSampling_pmfExp_swap
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (sampling : CorrelatedPairSampling Response)
    (hsymmetric : sampling.IsSymmetric) (value : Response → Response → ℝ) :
    pmfExp sampling (fun pair => value pair.2 pair.1) =
      pmfExp sampling (fun pair => value pair.1 pair.2) := by
  classical
  let swapEquiv : (Response × Response) ≃ (Response × Response) :=
    Equiv.prodComm Response Response
  unfold pmfExp
  calc
    (∑ pair : Response × Response,
        (sampling pair).toReal * value pair.2 pair.1) =
      ∑ pair : Response × Response,
        (sampling (swapEquiv pair)).toReal *
          value (swapEquiv pair).2 (swapEquiv pair).1 := by
        simpa [swapEquiv] using
          (Equiv.sum_comp swapEquiv (fun pair : Response × Response =>
            (sampling pair).toReal * value pair.2 pair.1)).symm
    _ = ∑ pair : Response × Response,
        (sampling pair).toReal * value pair.1 pair.2 := by
        apply Finset.sum_congr rfl
        intro pair _
        have hmass := hsymmetric pair.2 pair.1
        simpa [swapEquiv] using congrArg (fun mass : ℝ =>
          mass * value pair.1 pair.2) hmass

/-- A symmetric correlated report law counts both orientations in its
population objective, so its literal expected log likelihood is exactly twice
the off-diagonal fit objective. -/
theorem correlatedOneComparisonExpectedRawLogLikelihood_eq_two_offDiagonalFitObjective
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (sampling : CorrelatedPairSampling Response)
    (preference : PairwisePreference PUnit Response)
    (hsymmetric : sampling.IsSymmetric)
    (score : PairwiseCountDataset.ScoreVector Response) :
    correlatedOneComparisonExpectedRawLogLikelihood sampling preference score =
      2 * correlatedOneComparisonOffDiagonalFitObjective sampling preference score := by
  rw [correlatedOneComparisonExpectedRawLogLikelihood_eq]
  let term : Response → Response → ℝ := fun first second =>
    if first = second then 0 else
      preference.prob PUnit.unit first second *
        Real.log (Real.sigmoid (score first - score second))
  have hterm : ∀ first second,
      (if first = second then 0 else
          preference.prob PUnit.unit first second *
              Real.log (Real.sigmoid (score first - score second)) +
            (1 - preference.prob PUnit.unit first second) *
              Real.log (Real.sigmoid (score second - score first))) =
        term first second + term second first := by
    intro first second
    by_cases hsame : first = second
    · subst second
      simp [term]
    · rw [if_neg hsame]
      have hcomplement := preference.complementary PUnit.unit first second
      dsimp [term]
      rw [if_neg hsame, if_neg (Ne.symm hsame)]
      have hreverse : 1 - preference.prob PUnit.unit first second =
          preference.prob PUnit.unit second first := by
        linarith
      rw [hreverse]
  change pmfExp sampling _ = 2 * pmfExp sampling (fun pair => term pair.1 pair.2)
  rw [show (fun pair : Response × Response =>
      if pair.1 = pair.2 then 0 else
        preference.prob PUnit.unit pair.1 pair.2 *
            Real.log (Real.sigmoid (score pair.1 - score pair.2)) +
          (1 - preference.prob PUnit.unit pair.1 pair.2) *
            Real.log (Real.sigmoid (score pair.2 - score pair.1))) =
      fun pair => term pair.1 pair.2 + term pair.2 pair.1 by
        funext pair
        exact hterm pair.1 pair.2]
  rw [pmfExp_add, correlatedPairSampling_pmfExp_swap sampling hsymmetric]
  ring

/-- With zero diagonal mass, the correlated off-diagonal fit objective is
definitionally equal to the full correlated population Bradley--Terry
objective. -/
theorem correlatedBradleyTerryFitObjective_eq_offDiagonalFitObjective
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (sampling : CorrelatedPairSampling Response)
    (preference : PairwisePreference PUnit Response)
    (hdiagonal : sampling.HasZeroDiagonal)
    (score : PairwiseCountDataset.ScoreVector Response) :
    correlatedBradleyTerryFitObjective preference sampling score =
      correlatedOneComparisonOffDiagonalFitObjective sampling preference score := by
  unfold correlatedBradleyTerryFitObjective
    correlatedOneComparisonOffDiagonalFitObjective pmfExp
  apply Finset.sum_congr rfl
  rintro ⟨first, second⟩ _
  by_cases hsame : first = second
  · subst second
    rw [hdiagonal first]
    ring
  · simp [hsame]

/-- Under zero diagonal mass, the literal off-diagonal and full correlated
population objectives have exactly the same global maximizers. -/
theorem correlatedOffDiagonalFit_globalMax_iff_correlatedBradleyTerryFit_globalMax
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (sampling : CorrelatedPairSampling Response)
    (preference : PairwisePreference PUnit Response)
    (hdiagonal : sampling.HasZeroDiagonal)
    (score : PairwiseCountDataset.ScoreVector Response) :
    (∀ candidate,
      correlatedOneComparisonOffDiagonalFitObjective sampling preference candidate ≤
        correlatedOneComparisonOffDiagonalFitObjective sampling preference score) ↔
      (∀ candidate,
        correlatedBradleyTerryFitObjective preference sampling candidate ≤
          correlatedBradleyTerryFitObjective preference sampling score) := by
  constructor
  · intro h candidate
    have hcandidate := h candidate
    rw [← correlatedBradleyTerryFitObjective_eq_offDiagonalFitObjective
      sampling preference hdiagonal candidate,
      ← correlatedBradleyTerryFitObjective_eq_offDiagonalFitObjective
        sampling preference hdiagonal score] at hcandidate
    exact hcandidate
  · intro h candidate
    have hcandidate := h candidate
    rw [correlatedBradleyTerryFitObjective_eq_offDiagonalFitObjective
      sampling preference hdiagonal candidate,
      correlatedBradleyTerryFitObjective_eq_offDiagonalFitObjective
        sampling preference hdiagonal score] at hcandidate
    exact hcandidate

/-- The population win total for one response under a correlated pair sampler.
The weights are the ordered-pair marginal coefficients, rather than the
product weights of `preferenceAgainstSampling`. -/
noncomputable def correlatedPreferenceAgainstSampling {Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response) (response : Response) : ℝ :=
  ∑ opponent : Response,
    (sampling (response, opponent)).toReal * preference.prob () response opponent

/-- The fitted Bradley--Terry analogue of
`correlatedPreferenceAgainstSampling`. -/
noncomputable def correlatedBradleyTerryAgainstSampling {Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (sampling : CorrelatedPairSampling Response)
    (reward : Response → ℝ) (response : Response) : ℝ :=
  ∑ opponent : Response,
    (sampling (response, opponent)).toReal *
      Real.sigmoid (reward response - reward opponent)

/-- The source-style coordinate derivative assertion for the correlated
population objective. -/
def HasCorrelatedBradleyTerryFitCoordinateDerivative {Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response) (reward : Response → ℝ) : Prop :=
  ∀ response,
    HasDerivAt
      (fun amount =>
        correlatedBradleyTerryFitObjective preference sampling
          (rewardCoordinatePerturbation reward response amount))
      (correlatedPreferenceAgainstSampling preference sampling response -
        correlatedBradleyTerryAgainstSampling sampling reward response) 0

/-- Raw finite-sum derivative of the correlated population objective. -/
theorem hasDerivAt_correlatedBradleyTerryFitObjective_coordinate_raw
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response)
    (reward : Response → ℝ) (response : Response) :
    HasDerivAt
      (fun amount =>
        correlatedBradleyTerryFitObjective preference sampling
          (rewardCoordinatePerturbation reward response amount))
      (∑ pair : Response × Response,
        (sampling pair).toReal * preference.prob () pair.1 pair.2 *
          (1 - Real.sigmoid (reward pair.1 - reward pair.2)) *
            ((if pair.1 = response then (1 : ℝ) else 0) -
              if pair.2 = response then (1 : ℝ) else 0)) 0 := by
  unfold correlatedBradleyTerryFitObjective pmfExp
  have hterms : ∀ pair : Response × Response,
      HasDerivAt
        (fun amount =>
          (sampling pair).toReal *
            (preference.prob () pair.1 pair.2 *
              Real.log (Real.sigmoid
                (rewardCoordinatePerturbation reward response amount pair.1 -
                  rewardCoordinatePerturbation reward response amount pair.2))))
        ((sampling pair).toReal * preference.prob () pair.1 pair.2 *
          (1 - Real.sigmoid (reward pair.1 - reward pair.2)) *
            ((if pair.1 = response then (1 : ℝ) else 0) -
              if pair.2 = response then (1 : ℝ) else 0)) 0 := by
    intro pair
    convert
      (hasDerivAt_bradleyTerryFitTerm preference reward response pair.1 pair.2).const_mul
        (sampling pair).toReal using 1; ring
  convert HasDerivAt.sum (u := Finset.univ) (fun pair _ => hterms pair) using 1
  funext amount
  simp

/-- Symmetry of the ordered-pair presentation turns the raw derivative into
the weighted first-order equation for one response. -/
theorem correlatedBradleyTerryFit_coordinateDerivative_raw_eq_source
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response)
    (hsymmetric : sampling.IsSymmetric) (reward : Response → ℝ)
    (response : Response) :
    (∑ pair : Response × Response,
      (sampling pair).toReal * preference.prob () pair.1 pair.2 *
        (1 - Real.sigmoid (reward pair.1 - reward pair.2)) *
          ((if pair.1 = response then (1 : ℝ) else 0) -
            if pair.2 = response then (1 : ℝ) else 0)) =
      correlatedPreferenceAgainstSampling preference sampling response -
        correlatedBradleyTerryAgainstSampling sampling reward response := by
  classical
  let mass : Response → Response → ℝ := fun first second =>
    (sampling (first, second)).toReal
  let probability : Response → Response → ℝ := fun first second =>
    preference.prob () first second
  let fitted : Response → Response → ℝ := fun first second =>
    Real.sigmoid (reward first - reward second)
  change
    (∑ pair : Response × Response,
      mass pair.1 pair.2 * probability pair.1 pair.2 *
        (1 - fitted pair.1 pair.2) *
          ((if pair.1 = response then (1 : ℝ) else 0) -
            if pair.2 = response then (1 : ℝ) else 0)) =
      (∑ opponent : Response, mass response opponent * probability response opponent) -
        ∑ opponent : Response, mass response opponent * fitted response opponent
  rw [Fintype.sum_prod_type]
  have hsplit :
      (∑ first : Response, ∑ second : Response,
        mass first second * probability first second * (1 - fitted first second) *
          ((if first = response then (1 : ℝ) else 0) -
            if second = response then (1 : ℝ) else 0)) =
        (∑ first : Response, ∑ second : Response,
          mass first second * probability first second * (1 - fitted first second) *
            (if first = response then (1 : ℝ) else 0)) -
          ∑ first : Response, ∑ second : Response,
            mass first second * probability first second * (1 - fitted first second) *
              (if second = response then (1 : ℝ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro first _
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro second _
    ring
  have hfirst :
      (∑ first : Response, ∑ second : Response,
        mass first second * probability first second * (1 - fitted first second) *
          (if first = response then (1 : ℝ) else 0)) =
        ∑ second : Response,
          mass response second * probability response second * (1 - fitted response second) := by
    calc
      (∑ first : Response, ∑ second : Response,
        mass first second * probability first second * (1 - fitted first second) *
          (if first = response then (1 : ℝ) else 0)) =
          ∑ first : Response, if first = response then
            ∑ second : Response,
              mass first second * probability first second * (1 - fitted first second) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro first _
            by_cases hfirst : first = response <;> simp [hfirst]
      _ = ∑ second : Response,
            mass response second * probability response second * (1 - fitted response second) := by
            rw [Finset.sum_ite_eq' (s := Finset.univ) (a := response)]
            simp
  have hsecond :
      (∑ first : Response, ∑ second : Response,
        mass first second * probability first second * (1 - fitted first second) *
          (if second = response then (1 : ℝ) else 0)) =
        ∑ first : Response,
          mass first response * probability first response * (1 - fitted first response) := by
    apply Finset.sum_congr rfl
    intro first _
    calc
      (∑ second : Response,
        mass first second * probability first second * (1 - fitted first second) *
          (if second = response then (1 : ℝ) else 0)) =
          ∑ second : Response, if second = response then
            mass first second * probability first second * (1 - fitted first second) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro second _
            by_cases hsecond : second = response <;> simp [hsecond]
      _ = mass first response * probability first response * (1 - fitted first response) := by
            rw [Finset.sum_ite_eq' (s := Finset.univ) (a := response)]
            simp
  have hsecond' :
      (∑ first : Response,
        mass first response * probability first response * (1 - fitted first response)) =
        ∑ first : Response,
          mass response first * (1 - probability response first) * fitted response first := by
    refine Finset.sum_congr rfl ?_
    intro first _
    have hmass : mass first response = mass response first := by
      exact hsymmetric first response
    have hprobability : probability first response = 1 - probability response first := by
      have hcomplementary := preference.complementary () response first
      dsimp [probability]
      linarith
    have hfitted : fitted first response = 1 - fitted response first := by
      dsimp [fitted]
      have hneg : reward first - reward response =
          -(reward response - reward first) := by ring
      rw [hneg, Real.sigmoid_neg]
    rw [hmass, hprobability, hfitted]
    ring
  calc
    (∑ first : Response, ∑ second : Response,
      mass first second * probability first second * (1 - fitted first second) *
        ((if first = response then (1 : ℝ) else 0) -
          if second = response then (1 : ℝ) else 0)) =
        (∑ first : Response, ∑ second : Response,
          mass first second * probability first second * (1 - fitted first second) *
            (if first = response then (1 : ℝ) else 0)) -
          ∑ first : Response, ∑ second : Response,
            mass first second * probability first second * (1 - fitted first second) *
              (if second = response then (1 : ℝ) else 0) := hsplit
    _ = (∑ second : Response,
          mass response second * probability response second * (1 - fitted response second)) -
          ∑ first : Response,
            mass response first * (1 - probability response first) * fitted response first := by
          rw [hfirst, hsecond, hsecond']
    _ = ∑ opponent : Response,
          (mass response opponent * probability response opponent *
              (1 - fitted response opponent) -
            mass response opponent * (1 - probability response opponent) *
              fitted response opponent) := by
          conv_lhs => rw [← Finset.sum_sub_distrib]
    _ = ∑ opponent : Response,
          (mass response opponent * probability response opponent -
            mass response opponent * fitted response opponent) := by
          refine Finset.sum_congr rfl ?_
          intro opponent _
          ring
    _ = (∑ opponent : Response, mass response opponent * probability response opponent) -
          ∑ opponent : Response, mass response opponent * fitted response opponent :=
          by rw [Finset.sum_sub_distrib]

/-- The correlated finite population objective has the source coordinate
derivative whenever the ordered-pair encoding is symmetric. -/
theorem hasCorrelatedBradleyTerryFitCoordinateDerivative
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response)
    (hsymmetric : sampling.IsSymmetric) (reward : Response → ℝ) :
    HasCorrelatedBradleyTerryFitCoordinateDerivative preference sampling reward := by
  intro response
  rw [← correlatedBradleyTerryFit_coordinateDerivative_raw_eq_source
    preference sampling hsymmetric reward response]
  exact hasDerivAt_correlatedBradleyTerryFitObjective_coordinate_raw
    preference sampling reward response

/-- A global correlated population optimum is a local optimum along every
single reward coordinate. -/
theorem correlatedBradleyTerryFitObjective_coordinate_isLocalMax_of_globalMax
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response) (reward : Response → ℝ)
    (hmax : ∀ candidate,
      correlatedBradleyTerryFitObjective preference sampling candidate ≤
        correlatedBradleyTerryFitObjective preference sampling reward)
    (response : Response) :
    IsLocalMax
      (fun amount =>
        correlatedBradleyTerryFitObjective preference sampling
          (rewardCoordinatePerturbation reward response amount)) 0 := by
  refine Filter.Eventually.of_forall ?_
  intro amount
  simpa [rewardCoordinatePerturbation_zero] using
    hmax (rewardCoordinatePerturbation reward response amount)

/-- At a correlated population optimum, every response satisfies the weighted
first-order equation comparing observed and fitted win totals. -/
theorem correlatedBradleyTerryFit_coordinate_stationary_of_globalMax
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response)
    (hsymmetric : sampling.IsSymmetric) (reward : Response → ℝ)
    (hmax : ∀ candidate,
      correlatedBradleyTerryFitObjective preference sampling candidate ≤
        correlatedBradleyTerryFitObjective preference sampling reward)
    (response : Response) :
    correlatedPreferenceAgainstSampling preference sampling response =
      correlatedBradleyTerryAgainstSampling sampling reward response := by
  have hlocal := correlatedBradleyTerryFitObjective_coordinate_isLocalMax_of_globalMax
    preference sampling reward hmax response
  have hderivative := hasCorrelatedBradleyTerryFitCoordinateDerivative
    preference sampling hsymmetric reward response
  exact sub_eq_zero.mp (hlocal.hasDerivAt_eq_zero hderivative)

/-- Expanded finite-sum form of the correlated MLE first-order equation. -/
theorem correlatedBradleyTerryFit_stationary_sum_of_globalMax
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response)
    (hsymmetric : sampling.IsSymmetric) (reward : Response → ℝ)
    (hmax : ∀ candidate,
      correlatedBradleyTerryFitObjective preference sampling candidate ≤
        correlatedBradleyTerryFitObjective preference sampling reward)
    (response : Response) :
    (∑ opponent : Response,
      (sampling (response, opponent)).toReal *
        (preference.prob () response opponent -
          Real.sigmoid (reward response - reward opponent))) = 0 := by
  have hstationary := correlatedBradleyTerryFit_coordinate_stationary_of_globalMax
    preference sampling hsymmetric reward hmax response
  rw [correlatedPreferenceAgainstSampling,
    correlatedBradleyTerryAgainstSampling] at hstationary
  calc
    (∑ opponent : Response,
      (sampling (response, opponent)).toReal *
        (preference.prob () response opponent -
          Real.sigmoid (reward response - reward opponent))) =
        (∑ opponent : Response,
          (sampling (response, opponent)).toReal * preference.prob () response opponent) -
          ∑ opponent : Response,
            (sampling (response, opponent)).toReal *
              Real.sigmoid (reward response - reward opponent) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro opponent _
          ring
    _ = 0 := sub_eq_zero.mpr hstationary

/-- For any correlated PMF component, the absolute first-order residual at a
single response is at most one.  Its row mass is at most the PMF's total mass,
and both an observed and a fitted Bradley--Terry probability lie in `[0,1]`. -/
theorem correlatedBradleyTerryResidual_abs_le_one
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response) (reward : Response → ℝ)
    (response : Response) :
    |∑ opponent : Response,
      (sampling (response, opponent)).toReal *
        (preference.prob () response opponent -
          Real.sigmoid (reward response - reward opponent))| ≤ 1 := by
  let term : Response → ℝ := fun opponent =>
    (sampling (response, opponent)).toReal *
      (preference.prob () response opponent -
        Real.sigmoid (reward response - reward opponent))
  have hgap : ∀ opponent : Response,
      |preference.prob () response opponent -
        Real.sigmoid (reward response - reward opponent)| ≤ 1 := by
    intro opponent
    simpa using abs_sub_le_of_le_of_le
      (preference.nonneg () response opponent)
      (preference.le_one () response opponent)
      (Real.sigmoid_nonneg (reward response - reward opponent))
      (Real.sigmoid_le_one (reward response - reward opponent))
  have hterm : ∀ opponent : Response,
      |term opponent| ≤ (sampling (response, opponent)).toReal := by
    intro opponent
    calc
      |term opponent| = (sampling (response, opponent)).toReal *
          |preference.prob () response opponent -
            Real.sigmoid (reward response - reward opponent)| := by
            dsimp [term]
            rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ (sampling (response, opponent)).toReal * 1 := by
            exact mul_le_mul_of_nonneg_left (hgap opponent) ENNReal.toReal_nonneg
      _ = (sampling (response, opponent)).toReal := by ring
  have hrow : ∑ opponent : Response,
      (sampling (response, opponent)).toReal ≤ 1 := by
    have htotal : ∑ pair : Response × Response, (sampling pair).toReal = 1 :=
      pmfToRealSum sampling
    rw [Fintype.sum_prod_type] at htotal
    calc
      (∑ opponent : Response, (sampling (response, opponent)).toReal) ≤
          ∑ first : Response, ∑ opponent : Response,
            (sampling (first, opponent)).toReal := by
            exact Finset.single_le_sum (s := Finset.univ)
              (f := fun first => ∑ opponent : Response,
                (sampling (first, opponent)).toReal) (fun first _ =>
              Finset.sum_nonneg fun opponent _ => ENNReal.toReal_nonneg)
              (Finset.mem_univ response)
      _ = 1 := htotal
  calc
    |∑ opponent : Response, term opponent| ≤ ∑ opponent : Response,
        |term opponent| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ opponent : Response, (sampling (response, opponent)).toReal := by
        exact Finset.sum_le_sum fun opponent _ => hterm opponent
    _ ≤ 1 := hrow

/-- A common reference normalization preserves the correlated population
objective, because every fitted score difference is unchanged. -/
theorem correlatedBradleyTerryFitObjective_referenceNormalize
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response)
    (reference : Response) (reward : Response → ℝ) :
    correlatedBradleyTerryFitObjective preference sampling
      (referenceNormalizeReward reference reward) =
      correlatedBradleyTerryFitObjective preference sampling reward := by
  unfold correlatedBradleyTerryFitObjective
  apply pmfExp_congr
  rintro ⟨first, second⟩
  rw [referenceNormalizeReward_sub]

/-- The correlated finite population objective is continuous in its reward
vector. -/
theorem continuous_correlatedBradleyTerryFitObjective
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response) :
    Continuous (correlatedBradleyTerryFitObjective preference sampling) := by
  unfold correlatedBradleyTerryFitObjective pmfExp
  apply continuous_finset_sum
  rintro ⟨first, second⟩ _
  apply Continuous.const_mul
  apply Continuous.const_mul
  have hsigmoid : Continuous (fun reward : Response → ℝ =>
      Real.sigmoid (reward first - reward second)) :=
    continuous_sigmoid.comp
      ((continuous_apply first).sub (continuous_apply second))
  exact hsigmoid.log fun reward => ne_of_gt (Real.sigmoid_pos _)

/-- Every individual correlated population log-likelihood summand is
nonpositive. -/
theorem correlatedBradleyTerryFitTerm_nonpos
    {Response : Type*} (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response) (reward : Response → ℝ)
    (first second : Response) :
    (sampling (first, second)).toReal * preference.prob () first second *
      Real.log (Real.sigmoid (reward first - reward second)) ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact mul_nonneg ENNReal.toReal_nonneg (preference.nonneg () first second)
  · apply Real.log_nonpos
    · exact Real.sigmoid_nonneg _
    · exact Real.sigmoid_le_one _

/-- The full correlated population objective is bounded above by any selected
ordered-pair term. -/
theorem correlatedBradleyTerryFitObjective_le_term
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response) (reward : Response → ℝ)
    (first second : Response) :
    correlatedBradleyTerryFitObjective preference sampling reward ≤
      (sampling (first, second)).toReal * preference.prob () first second *
        Real.log (Real.sigmoid (reward first - reward second)) := by
  classical
  unfold correlatedBradleyTerryFitObjective pmfExp
  let term : Response × Response → ℝ := fun pair =>
    (sampling pair).toReal *
      (preference.prob () pair.1 pair.2 *
        Real.log (Real.sigmoid (reward pair.1 - reward pair.2)))
  have hpoint : ∀ pair : Response × Response,
      term pair ≤ if pair = (first, second) then term pair else 0 := by
    intro pair
    by_cases hpair : pair = (first, second)
    · simp [hpair]
    · simp only [if_neg hpair]
      convert correlatedBradleyTerryFitTerm_nonpos preference sampling reward pair.1 pair.2 using 1; ring
  change (∑ pair : Response × Response, term pair) ≤ _
  calc
    (∑ pair : Response × Response, term pair) ≤
        ∑ pair : Response × Response,
          if pair = (first, second) then term pair else 0 := by
          exact Finset.sum_le_sum fun pair _ => hpoint pair
    _ = term (first, second) := by
          rw [Finset.sum_eq_single (first, second)]
          · simp [term]
          · intro pair _ hne
            simp [hne]
          · simp
    _ = (sampling (first, second)).toReal * preference.prob () first second *
          Real.log (Real.sigmoid (reward first - reward second)) := by
          dsimp [term]
          ring

/-- The positive coefficient of an off-diagonal correlated fit term. -/
noncomputable def correlatedBradleyTerryFitTermWeight {Response : Type*}
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response)
    (first second : Response) : ℝ :=
  (sampling (first, second)).toReal * preference.prob () first second

/-- An off-diagonal correlated fit coefficient is positive under full pair
support and strictly positive comparison probabilities. -/
theorem correlatedBradleyTerryFitTermWeight_pos
    {Response : Type*} [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response)
    (hsampling : sampling.HasFullOffDiagonalSupport)
    (hpreference : ∀ first second : Response, first ≠ second →
      0 < preference.prob () first second)
    {first second : Response} (hne : first ≠ second) :
    0 < correlatedBradleyTerryFitTermWeight preference sampling first second := by
  unfold correlatedBradleyTerryFitTermWeight
  exact mul_pos (hsampling first second hne) (hpreference first second hne)

/-- Full off-diagonal support and strictly noisy pairwise preferences make the
finite correlated population likelihood attain a global maximum.  The proof
normalizes one reference score and uses one positive comparison in either
direction to keep every other coordinate in a compact cube. -/
theorem exists_correlatedBradleyTerryFit_globalMax
    {Response : Type*} [Fintype Response] [DecidableEq Response] [Nonempty Response]
    (preference : PairwisePreference PUnit Response)
    (sampling : CorrelatedPairSampling Response)
    (hsampling : sampling.HasFullOffDiagonalSupport)
    (hpreference : ∀ first second : Response, first ≠ second →
      0 < preference.prob () first second) :
    ∃ reward : Response → ℝ, ∀ candidate : Response → ℝ,
      correlatedBradleyTerryFitObjective preference sampling candidate ≤
        correlatedBradleyTerryFitObjective preference sampling reward := by
  classical
  let reference : Response := Classical.choice inferInstance
  let weight : Response × Response → ℝ := fun pair =>
    if pair.1 = pair.2 then 1 else
      correlatedBradleyTerryFitTermWeight preference sampling pair.1 pair.2
  have hweight_pos : ∀ pair : Response × Response, 0 < weight pair := by
    rintro ⟨first, second⟩
    by_cases hsame : first = second
    · simp [weight, hsame]
    · simp only [weight, if_neg hsame]
      exact correlatedBradleyTerryFitTermWeight_pos preference sampling
        hsampling hpreference hsame
  let minWeight : ℝ := finiteMin weight
  have hminWeight_pos : 0 < minWeight := finiteMin_pos weight hweight_pos
  let zeroObjective : ℝ := correlatedBradleyTerryFitObjective preference sampling 0
  obtain ⟨bound, hbound_pos, htail⟩ :=
    exists_pos_log_sigmoid_neg_lt (zeroObjective / minWeight)
  let cube : Set (Response → ℝ) :=
    Set.univ.pi (fun _ : Response => Set.Icc (-bound) bound)
  have hcube_compact : IsCompact cube := by
    dsimp [cube]
    exact isCompact_univ_pi fun _ : Response => isCompact_Icc
  have hzero_cube : (0 : Response → ℝ) ∈ cube := by
    change ∀ response : Response, response ∈ Set.univ →
      -bound ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ bound
    intro response _
    constructor <;> linarith
  obtain ⟨maxReward, hmax_cube, hmax⟩ := hcube_compact.exists_isMaxOn ⟨0, hzero_cube⟩
    (continuous_correlatedBradleyTerryFitObjective preference sampling).continuousOn
  have hbarrier : ∀ reward : Response → ℝ,
      reward reference = 0 → reward ∉ cube →
      correlatedBradleyTerryFitObjective preference sampling reward < zeroObjective := by
    intro reward href houtside
    have houtside' : ∃ response : Response, reward response < -bound ∨ bound < reward response := by
      by_contra hnot
      push Not at hnot
      apply houtside
      intro response _
      exact ⟨hnot response |>.1, hnot response |>.2⟩
    rcases houtside' with ⟨response, hlow | hhigh⟩
    · have hne : response ≠ reference := by
        intro heq
        subst response
        rw [href] at hlow
        linarith
      have hgap : reward response - reward reference < -bound := by
        rw [href]
        simpa using hlow
      have hlog_gap : Real.log (Real.sigmoid (reward response - reward reference)) <
          Real.log (Real.sigmoid (-bound)) :=
        Real.strictMonoOn_log (Real.sigmoid_pos _) (Real.sigmoid_pos _)
          (Real.sigmoid_strictMono hgap)
      have hterm_weight : minWeight ≤
          correlatedBradleyTerryFitTermWeight preference sampling response reference := by
        calc
          minWeight ≤ weight (response, reference) := finiteMin_le weight (response, reference)
          _ = correlatedBradleyTerryFitTermWeight preference sampling response reference := by
            simp [weight, hne]
      have htail_nonpos : Real.log (Real.sigmoid (-bound)) ≤ 0 := by
        apply Real.log_nonpos
        · exact Real.sigmoid_nonneg _
        · exact Real.sigmoid_le_one _
      have hterm_weight_pos := correlatedBradleyTerryFitTermWeight_pos
        preference sampling hsampling hpreference hne
      have hterm_lt : correlatedBradleyTerryFitTermWeight preference sampling response reference *
          Real.log (Real.sigmoid (reward response - reward reference)) < zeroObjective := by
        calc
          correlatedBradleyTerryFitTermWeight preference sampling response reference *
              Real.log (Real.sigmoid (reward response - reward reference)) <
            correlatedBradleyTerryFitTermWeight preference sampling response reference *
              Real.log (Real.sigmoid (-bound)) :=
            mul_lt_mul_of_pos_left hlog_gap hterm_weight_pos
          _ ≤ minWeight * Real.log (Real.sigmoid (-bound)) :=
            mul_le_mul_of_nonpos_right hterm_weight htail_nonpos
          _ < zeroObjective := by
            have h := (lt_div_iff₀ hminWeight_pos).mp htail
            nlinarith
      calc
        correlatedBradleyTerryFitObjective preference sampling reward ≤
            correlatedBradleyTerryFitTermWeight preference sampling response reference *
              Real.log (Real.sigmoid (reward response - reward reference)) := by
          simpa only [correlatedBradleyTerryFitTermWeight, mul_assoc] using
            (correlatedBradleyTerryFitObjective_le_term preference sampling reward
              response reference)
        _ < zeroObjective := hterm_lt
    · have hne : reference ≠ response := by
        intro heq
        subst response
        rw [href] at hhigh
        linarith
      have hgap : reward reference - reward response < -bound := by
        rw [href]
        linarith
      have hlog_gap : Real.log (Real.sigmoid (reward reference - reward response)) <
          Real.log (Real.sigmoid (-bound)) :=
        Real.strictMonoOn_log (Real.sigmoid_pos _) (Real.sigmoid_pos _)
          (Real.sigmoid_strictMono hgap)
      have hterm_weight : minWeight ≤
          correlatedBradleyTerryFitTermWeight preference sampling reference response := by
        calc
          minWeight ≤ weight (reference, response) := finiteMin_le weight (reference, response)
          _ = correlatedBradleyTerryFitTermWeight preference sampling reference response := by
            simp [weight, hne]
      have htail_nonpos : Real.log (Real.sigmoid (-bound)) ≤ 0 := by
        apply Real.log_nonpos
        · exact Real.sigmoid_nonneg _
        · exact Real.sigmoid_le_one _
      have hterm_weight_pos := correlatedBradleyTerryFitTermWeight_pos
        preference sampling hsampling hpreference hne
      have hterm_lt : correlatedBradleyTerryFitTermWeight preference sampling reference response *
          Real.log (Real.sigmoid (reward reference - reward response)) < zeroObjective := by
        calc
          correlatedBradleyTerryFitTermWeight preference sampling reference response *
              Real.log (Real.sigmoid (reward reference - reward response)) <
            correlatedBradleyTerryFitTermWeight preference sampling reference response *
              Real.log (Real.sigmoid (-bound)) :=
            mul_lt_mul_of_pos_left hlog_gap hterm_weight_pos
          _ ≤ minWeight * Real.log (Real.sigmoid (-bound)) :=
            mul_le_mul_of_nonpos_right hterm_weight htail_nonpos
          _ < zeroObjective := by
            have h := (lt_div_iff₀ hminWeight_pos).mp htail
            nlinarith
      calc
        correlatedBradleyTerryFitObjective preference sampling reward ≤
            correlatedBradleyTerryFitTermWeight preference sampling reference response *
              Real.log (Real.sigmoid (reward reference - reward response)) := by
          simpa only [correlatedBradleyTerryFitTermWeight, mul_assoc] using
            (correlatedBradleyTerryFitObjective_le_term preference sampling reward
              reference response)
        _ < zeroObjective := hterm_lt
  refine ⟨maxReward, ?_⟩
  intro candidate
  let normalized : Response → ℝ := referenceNormalizeReward reference candidate
  have hnormalized_ref : normalized reference = 0 := by
    exact referenceNormalizeReward_apply_reference reference candidate
  have hnormalized_objective :
      correlatedBradleyTerryFitObjective preference sampling normalized =
        correlatedBradleyTerryFitObjective preference sampling candidate := by
    exact correlatedBradleyTerryFitObjective_referenceNormalize preference sampling reference candidate
  by_cases hnormalized_cube : normalized ∈ cube
  · calc
      correlatedBradleyTerryFitObjective preference sampling candidate =
          correlatedBradleyTerryFitObjective preference sampling normalized :=
            hnormalized_objective.symm
      _ ≤ correlatedBradleyTerryFitObjective preference sampling maxReward :=
        hmax hnormalized_cube
  · have hless := hbarrier normalized hnormalized_ref hnormalized_cube
    have hzero_max := hmax hzero_cube
    calc
      correlatedBradleyTerryFitObjective preference sampling candidate =
          correlatedBradleyTerryFitObjective preference sampling normalized :=
            hnormalized_objective.symm
      _ ≤ zeroObjective := hless.le
      _ = correlatedBradleyTerryFitObjective preference sampling 0 := rfl
      _ ≤ correlatedBradleyTerryFitObjective preference sampling maxReward := hzero_max

end HumanFeedback
end Learning
end AppliedModelingLib
