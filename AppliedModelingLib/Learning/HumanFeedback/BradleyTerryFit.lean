import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import AppliedModelingLib.Learning.HumanFeedback.BradleyTerry

/-!
# Finite Bradley--Terry reward fitting

This module records the finite, context-free objective in NLHF Appendix B.
The source writes an unconstrained `arg max` over reward vectors.  In Lean its
translation invariance and possible non-attainment are explicit: the main
calibration theorem takes a finite maximizer as a premise.  The finite
coordinate derivative identity used in the source proof is proved below.
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

/-- Add a scalar perturbation to one coordinate of a finite reward vector. -/
def rewardCoordinatePerturbation {Response : Type*} [DecidableEq Response]
    (reward : Response → ℝ) (response : Response) (amount : ℝ) : Response → ℝ :=
  fun candidate => reward candidate + if candidate = response then amount else 0

/-- A zero coordinate perturbation leaves a reward vector unchanged. -/
theorem rewardCoordinatePerturbation_zero {Response : Type*} [DecidableEq Response]
    (reward : Response → ℝ) (response : Response) :
    rewardCoordinatePerturbation reward response 0 = reward := by
  funext candidate
  simp [rewardCoordinatePerturbation]

/--
The finite ordered-pair Bradley--Terry log-likelihood from NLHF Appendix B,
Equation (9).  Summing both ordered pair orientations only rescales the usual
binary cross-entropy objective, so its maximizers and stationary points agree.
-/
noncomputable def bradleyTerryFitObjective {Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (reward : Response → ℝ) : ℝ :=
  pmfPairExp sampling sampling (fun first second =>
    preference.prob () first second *
      Real.log (Real.sigmoid (reward first - reward second)))

/-- The preference-model win probability of one response against a sampling PMF. -/
noncomputable def preferenceAgainstSampling {Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (response : Response) : ℝ :=
  pmfExp sampling (fun opponent => preference.prob () response opponent)

/-- The Bradley--Terry fitted win probability of one response against a sampling PMF. -/
noncomputable def bradleyTerryAgainstSampling {Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (reward : Response → ℝ) (sampling : PMF Response) (response : Response) : ℝ :=
  pmfExp sampling (fun opponent =>
    Real.sigmoid (reward response - reward opponent))

/-- The source coordinate-derivative formula for the finite ordered-pair objective. -/
def HasBradleyTerryFitCoordinateDerivative {Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (reward : Response → ℝ) : Prop :=
  ∀ response,
    HasDerivAt
      (fun amount =>
        bradleyTerryFitObjective preference sampling
          (rewardCoordinatePerturbation reward response amount))
      ((sampling response).toReal *
        (preferenceAgainstSampling preference sampling response -
          bradleyTerryAgainstSampling reward sampling response)) 0

/-- The scalar derivative used by every finite Bradley--Terry likelihood term. -/
theorem hasDerivAt_log_sigmoid (value : ℝ) :
    HasDerivAt (fun input : ℝ => Real.log (Real.sigmoid input))
      (1 - Real.sigmoid value) value := by
  have hsigmoid :=
    (Real.hasDerivAt_sigmoid value).log (ne_of_gt (Real.sigmoid_pos value))
  convert hsigmoid using 1
  field_simp [ne_of_gt (Real.sigmoid_pos value)]

/-- Derivative of one fitted-score gap under a single-coordinate perturbation. -/
theorem hasDerivAt_rewardCoordinateGap {Response : Type*} [DecidableEq Response]
    (reward : Response → ℝ) (response first second : Response) :
    HasDerivAt
      (fun amount =>
        rewardCoordinatePerturbation reward response amount first -
          rewardCoordinatePerturbation reward response amount second)
      ((if first = response then (1 : ℝ) else 0) -
        if second = response then (1 : ℝ) else 0) 0 := by
  by_cases hfirst : first = response
  · subst first
    by_cases hsecond : second = response
    · subst second
      convert (hasDerivAt_const (x := (0 : ℝ))
        (c := (reward response - reward response))) using 1 <;>
        simp [rewardCoordinatePerturbation]
    · convert (((hasDerivAt_const (x := (0 : ℝ)) (c := reward response)).add
        (hasDerivAt_id 0)).sub
        (hasDerivAt_const (x := (0 : ℝ)) (c := reward second))) using 1
      · funext amount
        simp [rewardCoordinatePerturbation, hsecond]
      · simp [rewardCoordinatePerturbation, hsecond]
  · by_cases hsecond : second = response
    · subst second
      convert
        ((hasDerivAt_const (x := (0 : ℝ)) (c := reward first)).sub
          ((hasDerivAt_const (x := (0 : ℝ)) (c := reward response)).add
            (hasDerivAt_id 0))) using 1
      · funext amount
        simp [rewardCoordinatePerturbation, hfirst]
      · simp [rewardCoordinatePerturbation, hfirst]
    · convert ((hasDerivAt_const (x := (0 : ℝ)) (c := reward first)).sub
        (hasDerivAt_const (x := (0 : ℝ)) (c := reward second))) using 1
      · funext amount
        simp [rewardCoordinatePerturbation, hfirst, hsecond]
      · simp [rewardCoordinatePerturbation, hfirst, hsecond]

/-- Derivative of one weighted finite Bradley--Terry log-likelihood term. -/
theorem hasDerivAt_bradleyTerryFitTerm {Response : Type*} [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (reward : Response → ℝ)
    (response first second : Response) :
    HasDerivAt
      (fun amount =>
        preference.prob () first second *
          Real.log (Real.sigmoid
            (rewardCoordinatePerturbation reward response amount first -
              rewardCoordinatePerturbation reward response amount second)))
      (preference.prob () first second *
        (1 - Real.sigmoid (reward first - reward second)) *
          ((if first = response then (1 : ℝ) else 0) -
            if second = response then (1 : ℝ) else 0)) 0 := by
  have hgap := hasDerivAt_rewardCoordinateGap reward response first second
  have hlog :=
    (hasDerivAt_log_sigmoid
      (rewardCoordinatePerturbation reward response 0 first -
        rewardCoordinatePerturbation reward response 0 second)).comp 0 hgap
  convert hlog.const_mul (preference.prob () first second) using 1 <;>
    simp [rewardCoordinatePerturbation] <;> ring

/--
Raw finite-sum form of the coordinate derivative of the Appendix-B objective.
The following algebraic simplification is the precise bridge to the source's
`π(z) [P(z ≻ π) - P_BT(z ≻ π)]` display.
-/
theorem hasDerivAt_bradleyTerryFitObjective_coordinate_raw
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (reward : Response → ℝ) (response : Response) :
    HasDerivAt
      (fun amount => bradleyTerryFitObjective preference sampling
        (rewardCoordinatePerturbation reward response amount))
      (∑ first : Response, (sampling first).toReal *
        ∑ second : Response, (sampling second).toReal *
          (preference.prob () first second *
            (1 - Real.sigmoid (reward first - reward second)) *
              ((if first = response then (1 : ℝ) else 0) -
                if second = response then (1 : ℝ) else 0))) 0 := by
  unfold bradleyTerryFitObjective pmfPairExp pmfExp
  have hinner : ∀ first : Response,
      HasDerivAt
        (fun amount => (sampling first).toReal *
          ∑ second : Response, (sampling second).toReal *
            (preference.prob () first second *
              Real.log (Real.sigmoid
                (rewardCoordinatePerturbation reward response amount first -
                  rewardCoordinatePerturbation reward response amount second))))
        ((sampling first).toReal *
          ∑ second : Response, (sampling second).toReal *
            (preference.prob () first second *
              (1 - Real.sigmoid (reward first - reward second)) *
                ((if first = response then (1 : ℝ) else 0) -
                  if second = response then (1 : ℝ) else 0))) 0 := by
    intro first
    apply HasDerivAt.const_mul
    convert (HasDerivAt.sum (u := Finset.univ) (fun second _ =>
        (hasDerivAt_bradleyTerryFitTerm preference reward response first second).const_mul
          (sampling second).toReal)) using 1
    funext amount
    simp
  convert (HasDerivAt.sum (u := Finset.univ) (fun first _ => hinner first)) using 1
  funext amount
  simp

/-- The raw coordinate derivative simplifies to the source's finite score equation. -/
theorem bradleyTerryFit_coordinateDerivative_raw_eq_source
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (reward : Response → ℝ) (response : Response) :
    (∑ first : Response, (sampling first).toReal *
      ∑ second : Response, (sampling second).toReal *
        (preference.prob () first second *
          (1 - Real.sigmoid (reward first - reward second)) *
            ((if first = response then (1 : ℝ) else 0) -
              if second = response then (1 : ℝ) else 0))) =
      (sampling response).toReal *
        (preferenceAgainstSampling preference sampling response -
          bradleyTerryAgainstSampling reward sampling response) := by
  classical
  let mass : Response → ℝ := fun response => (sampling response).toReal
  let probability : Response → Response → ℝ := fun first second =>
    preference.prob () first second
  let fitted : Response → Response → ℝ := fun first second =>
    Real.sigmoid (reward first - reward second)
  have hsplit :
      (∑ first : Response, mass first *
        ∑ second : Response, mass second * probability first second *
          (1 - fitted first second) *
            ((if first = response then (1 : ℝ) else 0) -
              if second = response then (1 : ℝ) else 0)) =
        (∑ first : Response, mass first *
          ∑ second : Response, mass second * probability first second *
            (1 - fitted first second) *
              (if first = response then (1 : ℝ) else 0)) -
          ∑ first : Response, mass first *
            ∑ second : Response, mass second * probability first second *
              (1 - fitted first second) *
                (if second = response then (1 : ℝ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro first _
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro second _
    ring
  have hfirst :
      (∑ first : Response, mass first *
        ∑ second : Response, mass second * probability first second *
          (1 - fitted first second) *
            (if first = response then (1 : ℝ) else 0)) =
        mass response *
          ∑ second : Response, mass second * probability response second *
            (1 - fitted response second) := by
    calc
      (∑ first : Response, mass first *
        ∑ second : Response, mass second * probability first second *
          (1 - fitted first second) *
            (if first = response then (1 : ℝ) else 0)) =
          ∑ first : Response, if first = response then
            mass first *
              ∑ second : Response, mass second * probability first second *
                (1 - fitted first second) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro first _
            by_cases hfirst : first = response <;> simp [hfirst]
      _ = mass response *
          ∑ second : Response, mass second * probability response second *
            (1 - fitted response second) := by
            rw [Finset.sum_ite_eq' (s := Finset.univ) (a := response)]
            simp
  have hsecond :
      (∑ first : Response, mass first *
        ∑ second : Response, mass second * probability first second *
          (1 - fitted first second) *
            (if second = response then (1 : ℝ) else 0)) =
        mass response *
          ∑ first : Response, mass first * probability first response *
            (1 - fitted first response) := by
    calc
      (∑ first : Response, mass first *
        ∑ second : Response, mass second * probability first second *
          (1 - fitted first second) *
            (if second = response then (1 : ℝ) else 0)) =
          ∑ first : Response, mass first *
            (∑ second : Response, if second = response then
              mass second * probability first second * (1 - fitted first second) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro first _
            congr 1
            refine Finset.sum_congr rfl ?_
            intro second _
            by_cases hsecond : second = response <;> simp [hsecond]
      _ = ∑ first : Response, mass first *
          (mass response * probability first response *
            (1 - fitted first response)) := by
            refine Finset.sum_congr rfl ?_
            intro first _
            simp
      _ = mass response *
          ∑ first : Response, mass first * probability first response *
            (1 - fitted first response) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro first _
            ring
  have hswap : ∀ first : Response,
      probability first response * (1 - fitted first response) =
        (1 - probability response first) * fitted response first := by
    intro first
    have hpreference := preference.complementary () response first
    have hneg : reward first - reward response = -(reward response - reward first) := by
      ring
    have hfitted : fitted first response = 1 - fitted response first := by
      simp only [fitted, hneg, Real.sigmoid_neg]
    have hprobability : probability first response = 1 - probability response first := by
      linarith
    rw [hprobability, hfitted]
    ring
  have hsum :
      (∑ second : Response, mass second * probability response second *
        (1 - fitted response second)) -
        (∑ second : Response, mass second *
          (1 - probability response second) * fitted response second) =
        ∑ second : Response, mass second *
          (probability response second - fitted response second) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro second _
    ring
  have hsecond' :
      (∑ first : Response, mass first * probability first response *
        (1 - fitted first response)) =
        ∑ first : Response, mass first *
          (1 - probability response first) * fitted response first := by
    refine Finset.sum_congr rfl ?_
    intro first _
    calc
      mass first * probability first response * (1 - fitted first response) =
          mass first * (probability first response * (1 - fitted first response)) := by
            ring
      _ = mass first * ((1 - probability response first) * fitted response first) := by
            rw [hswap first]
      _ = mass first * (1 - probability response first) * fitted response first := by
            ring
  dsimp only [mass, probability, fitted] at hsplit hfirst hsecond hswap hsum hsecond'
  calc
    _ = mass response *
        ((∑ second : Response, mass second * probability response second) -
          ∑ second : Response, mass second * fitted response second) := by
      calc
        _ =
            (∑ first : Response, (sampling first).toReal *
              ∑ second : Response, (sampling second).toReal *
                preference.prob () first second *
                  (1 - Real.sigmoid (reward first - reward second)) *
                    (if first = response then (1 : ℝ) else 0)) -
              ∑ first : Response, (sampling first).toReal *
                ∑ second : Response, (sampling second).toReal *
                  preference.prob () first second *
                    (1 - Real.sigmoid (reward first - reward second)) *
                      (if second = response then (1 : ℝ) else 0) := by
              simpa only [mul_assoc] using hsplit
        _ = (sampling response).toReal *
              (∑ second : Response, (sampling second).toReal *
                preference.prob () response second *
                  (1 - Real.sigmoid (reward response - reward second))) -
            (sampling response).toReal *
              ∑ first : Response, (sampling first).toReal *
                (1 - preference.prob () response first) *
                  Real.sigmoid (reward response - reward first) := by
              rw [hfirst, hsecond, hsecond']
        _ = (sampling response).toReal *
              ((∑ second : Response, (sampling second).toReal *
                preference.prob () response second) -
              ∑ second : Response, (sampling second).toReal *
                Real.sigmoid (reward response - reward second)) := by
              rw [← mul_sub, hsum]
              congr 1
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro second _
              ring
    _ = (sampling response).toReal *
        (preferenceAgainstSampling preference sampling response -
          bradleyTerryAgainstSampling reward sampling response) := by
      simp [mass, probability, fitted, preferenceAgainstSampling,
        bradleyTerryAgainstSampling, pmfExp]

/--
The finite analytic coordinate derivative required in Proposition 2.  This
closes the derivative premise used by the source-style reward-fit calibration
theorem below.
-/
theorem hasBradleyTerryFitCoordinateDerivative
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (reward : Response → ℝ) :
    HasBradleyTerryFitCoordinateDerivative preference sampling reward := by
  intro response
  rw [← bradleyTerryFit_coordinateDerivative_raw_eq_source
    preference sampling reward response]
  exact hasDerivAt_bradleyTerryFitObjective_coordinate_raw
    preference sampling reward response


/--
The Appendix-B Theorem-2 sampling perturbation: half the old sampling law and
half a point mass at the distinguished response.  Written this way, all other
masses are halved and the distinguished mass becomes `c * π(y')` for the
source's normalizing constant `c`.
-/
noncomputable def responseUpweightedSampling {Response : Type*}
    (sampling : PMF Response) (response : Response) : PMF Response :=
  binaryMixturePMF (1 / 2 : NNReal) (by norm_num) (PMF.pure response) sampling

/-- Two finite PMFs have the same support when exactly the same atoms have positive mass. -/
def SamePositiveSupport {Response : Type*} (first second : PMF Response) : Prop :=
  ∀ response, 0 < (first response).toReal ↔ 0 < (second response).toReal

/-- The Appendix-B perturbation preserves support when its distinguished atom was supported. -/
theorem responseUpweightedSampling_samePositiveSupport
    {Response : Type*} [DecidableEq Response]
    (sampling : PMF Response) (distinguished : Response)
    (hmass : 0 < (sampling distinguished).toReal) :
    SamePositiveSupport sampling (responseUpweightedSampling sampling distinguished) := by
  intro response
  by_cases hresponse : response = distinguished
  · subst response
    have hright :
        0 < (responseUpweightedSampling sampling distinguished distinguished).toReal := by
      unfold responseUpweightedSampling
      rw [binaryMixturePMF_apply_toReal]
      simp
      positivity
    exact iff_of_true hmass hright
  · unfold responseUpweightedSampling
    rw [binaryMixturePMF_apply_toReal]
    simp [hresponse]
    constructor <;> intro hpositive <;> nlinarith

/-- The Appendix-B perturbation is genuinely different when another supported response exists. -/
theorem responseUpweightedSampling_ne
    {Response : Type*} [DecidableEq Response]
    (sampling : PMF Response) (response distinguished : Response)
    (hresponse : response ≠ distinguished)
    (hmass : 0 < (sampling response).toReal) :
    responseUpweightedSampling sampling distinguished ≠ sampling := by
  intro hequality
  have heval := congrArg (fun distribution : PMF Response =>
    (distribution response).toReal) hequality
  change (responseUpweightedSampling sampling distinguished response).toReal =
    (sampling response).toReal at heval
  unfold responseUpweightedSampling at heval
  rw [binaryMixturePMF_apply_toReal] at heval
  simp [hresponse] at heval
  nlinarith

/-- Complementarity fixes every self-comparison probability at one half. -/
theorem pairwisePreference_self_eq_half {Response : Type*}
    (preference : PairwisePreference PUnit Response) (response : Response) :
    preference.prob () response response = 1 / 2 := by
  have hcomplementary := preference.complementary () response response
  linarith

/-- The exact average-preference identity for the Appendix-B sampling perturbation. -/
theorem preferenceAgainstSampling_responseUpweightedSampling
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (response distinguished : Response) :
    preferenceAgainstSampling preference
      (responseUpweightedSampling sampling distinguished) response =
      (1 / 2 : ℝ) * preference.prob () response distinguished +
        (1 / 2 : ℝ) * preferenceAgainstSampling preference sampling response := by
  unfold preferenceAgainstSampling responseUpweightedSampling
  rw [pmfExp_binaryMixturePMF, pmfExp_pure]
  norm_num

/--
The Appendix-B perturbation carries a pairwise model mismatch into a mismatch
of average win probabilities.  This is the algebraic core of Theorem 2.
-/
theorem responseUpweightedSampling_averageMismatch
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference fitted : PairwisePreference PUnit Response) (sampling : PMF Response)
    (response distinguished : Response)
    (haverage :
      preferenceAgainstSampling preference sampling response =
        preferenceAgainstSampling fitted sampling response)
    (hpair : fitted.prob () response distinguished ≠
      preference.prob () response distinguished) :
    preferenceAgainstSampling fitted
      (responseUpweightedSampling sampling distinguished) response ≠
        preferenceAgainstSampling preference
          (responseUpweightedSampling sampling distinguished) response := by
  intro hequality
  have hfitted := preferenceAgainstSampling_responseUpweightedSampling
    fitted sampling response distinguished
  have hpreference := preferenceAgainstSampling_responseUpweightedSampling
    preference sampling response distinguished
  rw [hfitted, hpreference] at hequality
  apply hpair
  linarith

/-- Distinct average win probabilities imply a pointwise disagreement. -/
theorem exists_response_of_preferenceAgainstSampling_ne
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (first second : PairwisePreference PUnit Response) (sampling : PMF Response)
    (response : Response)
    (haverage : preferenceAgainstSampling first sampling response ≠
      preferenceAgainstSampling second sampling response) :
    ∃ opponent, first.prob () response opponent ≠ second.prob () response opponent := by
  by_contra hno
  apply haverage
  unfold preferenceAgainstSampling
  apply pmfExp_congr
  intro opponent
  by_contra hpoint
  exact hno ⟨opponent, hpoint⟩

/--
For Bradley--Terry models, a pointwise preference disagreement yields a
disagreement in at least one reward difference because sigmoid is injective.
-/
theorem exists_rewardGap_ne_of_bradleyTerryAverage_ne
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (firstReward secondReward : Response → ℝ) (sampling : PMF Response)
    (response : Response)
    (haverage :
      preferenceAgainstSampling (bradleyTerryPreference fun _ => firstReward) sampling response ≠
        preferenceAgainstSampling (bradleyTerryPreference fun _ => secondReward)
          sampling response) :
    ∃ opponent,
      firstReward response - firstReward opponent ≠
        secondReward response - secondReward opponent := by
  obtain ⟨opponent, hpoint⟩ := exists_response_of_preferenceAgainstSampling_ne
    (bradleyTerryPreference fun _ => firstReward)
    (bradleyTerryPreference fun _ => secondReward) sampling response haverage
  refine ⟨opponent, ?_⟩
  intro hgap
  apply hpoint
  change Real.sigmoid (firstReward response - firstReward opponent) =
    Real.sigmoid (secondReward response - secondReward opponent)
  rw [hgap]

/--
Finite corrected form of NLHF Appendix-B Theorem 2.  The source proof uses
both distinguished responses in the support of the original sampling law;
those conditions are explicit here.  If the first fitted BT model disagrees
with the preference model on that supported pair, the source's same-support
upweighting produces a different fitted reward difference.
-/
theorem bradleyTerryFit_samplingSensitivity_of_calibration
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (firstReward secondReward : Response → ℝ)
    (response distinguished : Response)
    (hresponseMass : 0 < (sampling response).toReal)
    (hdistinguishedMass : 0 < (sampling distinguished).toReal)
    (hfirstCalibration :
      preferenceAgainstSampling preference sampling response =
        preferenceAgainstSampling
          (bradleyTerryPreference fun _ => firstReward) sampling response)
    (hpairMismatch :
      (bradleyTerryPreference fun _ => firstReward).prob () response distinguished ≠
        preference.prob () response distinguished)
    (hsecondCalibration :
      preferenceAgainstSampling preference
        (responseUpweightedSampling sampling distinguished) response =
        preferenceAgainstSampling
          (bradleyTerryPreference fun _ => secondReward)
          (responseUpweightedSampling sampling distinguished) response) :
    ∃ sampling', sampling' ≠ sampling ∧ SamePositiveSupport sampling sampling' ∧
      ∃ opponent,
        firstReward response - firstReward opponent ≠
          secondReward response - secondReward opponent := by
  have hresponse_ne : response ≠ distinguished := by
    intro hequality
    apply hpairMismatch
    subst distinguished
    exact (pairwisePreference_self_eq_half
      (bradleyTerryPreference fun _ => firstReward) response).trans
      (pairwisePreference_self_eq_half preference response).symm
  refine ⟨responseUpweightedSampling sampling distinguished, ?_, ?_, ?_⟩
  · exact responseUpweightedSampling_ne sampling response distinguished hresponse_ne hresponseMass
  · exact responseUpweightedSampling_samePositiveSupport
      sampling distinguished hdistinguishedMass
  · have haverageMismatch := responseUpweightedSampling_averageMismatch
      preference (bradleyTerryPreference fun _ => firstReward)
      sampling response distinguished hfirstCalibration hpairMismatch
    have hBTAverageMismatch :
        preferenceAgainstSampling
          (bradleyTerryPreference fun _ => firstReward)
          (responseUpweightedSampling sampling distinguished) response ≠
          preferenceAgainstSampling
            (bradleyTerryPreference fun _ => secondReward)
            (responseUpweightedSampling sampling distinguished) response := by
      intro hequality
      apply haverageMismatch
      calc
        preferenceAgainstSampling
            (bradleyTerryPreference fun _ => firstReward)
            (responseUpweightedSampling sampling distinguished) response =
            preferenceAgainstSampling
              (bradleyTerryPreference fun _ => secondReward)
              (responseUpweightedSampling sampling distinguished) response := hequality
        _ = preferenceAgainstSampling preference
              (responseUpweightedSampling sampling distinguished) response :=
              hsecondCalibration.symm
    exact exists_rewardGap_ne_of_bradleyTerryAverage_ne firstReward secondReward
      (responseUpweightedSampling sampling distinguished) response hBTAverageMismatch

/-- The same sampling-sensitivity conclusion also gives a changed BT preference model. -/
theorem bradleyTerryFit_samplingSensitivity_of_calibration_and_modelDifference
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (firstReward secondReward : Response → ℝ)
    (response distinguished : Response)
    (hresponseMass : 0 < (sampling response).toReal)
    (hdistinguishedMass : 0 < (sampling distinguished).toReal)
    (hfirstCalibration :
      preferenceAgainstSampling preference sampling response =
        preferenceAgainstSampling
          (bradleyTerryPreference fun _ => firstReward) sampling response)
    (hpairMismatch :
      (bradleyTerryPreference fun _ => firstReward).prob () response distinguished ≠
        preference.prob () response distinguished)
    (hsecondCalibration :
      preferenceAgainstSampling preference
        (responseUpweightedSampling sampling distinguished) response =
        preferenceAgainstSampling
          (bradleyTerryPreference fun _ => secondReward)
          (responseUpweightedSampling sampling distinguished) response) :
    ∃ sampling', sampling' ≠ sampling ∧ SamePositiveSupport sampling sampling' ∧
      ∃ opponent,
        firstReward response - firstReward opponent ≠
          secondReward response - secondReward opponent ∧
        (bradleyTerryPreference fun _ => firstReward).prob () response opponent ≠
          (bradleyTerryPreference fun _ => secondReward).prob () response opponent := by
  obtain ⟨sampling', hsampling', hsupport, opponent, hgap⟩ :=
    bradleyTerryFit_samplingSensitivity_of_calibration preference sampling
      firstReward secondReward response distinguished hresponseMass hdistinguishedMass
      hfirstCalibration hpairMismatch hsecondCalibration
  refine ⟨sampling', hsampling', hsupport, opponent, hgap, ?_⟩
  intro hmodel
  apply hgap
  apply Real.sigmoid_injective
  exact hmodel

/-- A global optimizer of the source finite reward-fit objective is a local optimum along each coordinate. -/
theorem bradleyTerryFitObjective_coordinate_isLocalMax_of_globalMax
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (reward : Response → ℝ)
    (hmax : ∀ candidate,
      bradleyTerryFitObjective preference sampling candidate ≤
        bradleyTerryFitObjective preference sampling reward)
    (response : Response) :
    IsLocalMax
      (fun amount => bradleyTerryFitObjective preference sampling
        (rewardCoordinatePerturbation reward response amount)) 0 := by
  refine Filter.Eventually.of_forall ?_
  intro amount
  simpa [rewardCoordinatePerturbation_zero] using
    hmax (rewardCoordinatePerturbation reward response amount)

/--
At a coordinatewise local maximum, the source derivative identity forces the
finite Bradley--Terry first-order equation.
-/
theorem bradleyTerryFit_coordinate_stationary_of_localMax
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (reward : Response → ℝ)
    (hlocal : ∀ response,
      IsLocalMax
        (fun amount => bradleyTerryFitObjective preference sampling
          (rewardCoordinatePerturbation reward response amount)) 0)
    (hderivative : HasBradleyTerryFitCoordinateDerivative preference sampling reward)
    (response : Response) :
    (sampling response).toReal *
      (preferenceAgainstSampling preference sampling response -
        bradleyTerryAgainstSampling reward sampling response) = 0 := by
  exact (hlocal response).hasDerivAt_eq_zero (hderivative response)

/--
The algebraic conclusion of NLHF Appendix-B Proposition 2: at every response
with positive sampling mass, the fitted Bradley--Terry model and the original
preference model have the same average win probability against that sampling
distribution.
-/
theorem bradleyTerryFit_averageCalibration_of_stationary
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (reward : Response → ℝ)
    (hstationary : ∀ response,
      (sampling response).toReal *
        (preferenceAgainstSampling preference sampling response -
          bradleyTerryAgainstSampling reward sampling response) = 0)
    (response : Response) (hmass : 0 < (sampling response).toReal) :
    preferenceAgainstSampling preference sampling response =
      bradleyTerryAgainstSampling reward sampling response := by
  have hzero := hstationary response
  nlinarith

/--
Proposition 2's calibration conclusion from a source-style finite global
optimizer.  Existence of such a finite optimizer remains an explicit source
assumption rather than an unproved compactness shortcut.
-/
theorem bradleyTerryFit_averageCalibration_of_globalMax
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (reward : Response → ℝ)
    (hmax : ∀ candidate,
      bradleyTerryFitObjective preference sampling candidate ≤
        bradleyTerryFitObjective preference sampling reward)
    (response : Response) (hmass : 0 < (sampling response).toReal) :
    preferenceAgainstSampling preference sampling response =
      bradleyTerryAgainstSampling reward sampling response := by
  apply bradleyTerryFit_averageCalibration_of_stationary preference sampling reward
    (response := response) (hmass := hmass)
  intro candidate
  exact bradleyTerryFit_coordinate_stationary_of_localMax preference sampling reward
    (fun coordinate =>
      bradleyTerryFitObjective_coordinate_isLocalMax_of_globalMax
        preference sampling reward hmax coordinate)
    (hasBradleyTerryFitCoordinateDerivative preference sampling reward) candidate

/--
For a fixed opponent-sampling distribution, fitted Bradley--Terry win rates
are strictly ordered by reward.  This is the finite monotonicity step behind
the MLE--Borda correspondence: every opponent sees the same strict reward-gap
increase.
-/
theorem bradleyTerryAgainstSampling_strictMono_reward
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (reward : Response → ℝ) (sampling : PMF Response)
    (first second : Response) (hreward : reward first < reward second) :
    bradleyTerryAgainstSampling reward sampling first <
      bradleyTerryAgainstSampling reward sampling second := by
  classical
  have hsupport : ∃ response : Response, 0 < (sampling response).toReal := by
    by_contra hnone
    push Not at hnone
    have hzero : ∀ response : Response, (sampling response).toReal = 0 := by
      intro response
      exact le_antisymm (hnone response) ENNReal.toReal_nonneg
    have hsum_zero : ∑ response : Response, (sampling response).toReal = 0 := by
      simp [hzero]
    have hsum_one : ∑ response : Response, (sampling response).toReal = 1 :=
      pmfToRealSum sampling
    linarith
  letI : Nonempty Response := ⟨Classical.choose hsupport⟩
  have hpoint : ∀ opponent : Response,
      Real.sigmoid (reward first - reward opponent) <
        Real.sigmoid (reward second - reward opponent) := by
    intro opponent
    apply Real.sigmoid_lt
    linarith
  have hpositive :
      0 < pmfExp sampling (fun opponent =>
        Real.sigmoid (reward second - reward opponent) -
          Real.sigmoid (reward first - reward opponent)) := by
    apply pmfExp_pos_of_support_forall_pos
    intro opponent _
    exact sub_pos.mpr (hpoint opponent)
  unfold bradleyTerryAgainstSampling
  rw [pmfExp_sub] at hpositive
  linarith

/-- Fitted Bradley--Terry win rates are weakly ordered by reward. -/
theorem bradleyTerryAgainstSampling_mono_reward
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (reward : Response → ℝ) (sampling : PMF Response)
    (first second : Response) (hreward : reward first ≤ reward second) :
    bradleyTerryAgainstSampling reward sampling first ≤
      bradleyTerryAgainstSampling reward sampling second := by
  unfold bradleyTerryAgainstSampling
  apply pmfExp_le_pmfExp_of_forall_le
  intro opponent
  apply Real.sigmoid_le
  linarith

/--
Finite unregularized Bradley--Terry maximum-likelihood fitting orders every
positive-mass pair exactly as their sampling-weighted Borda scores.  In the
notation of Siththaranjan--Laidlaw--Hadfield-Menell (2024),
`preferenceAgainstSampling` is the population Borda count and the global-max
hypothesis is their finite, attained unregularized MLE objective.
-/
theorem bradleyTerryFit_reward_lt_iff_preferenceAgainstSampling_lt_of_globalMax
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response) (sampling : PMF Response)
    (reward : Response → ℝ)
    (hmax : ∀ candidate,
      bradleyTerryFitObjective preference sampling candidate ≤
        bradleyTerryFitObjective preference sampling reward)
    (first second : Response)
    (hfirstMass : 0 < (sampling first).toReal)
    (hsecondMass : 0 < (sampling second).toReal) :
    reward first < reward second ↔
      preferenceAgainstSampling preference sampling first <
        preferenceAgainstSampling preference sampling second := by
  have hfirstCalibration := bradleyTerryFit_averageCalibration_of_globalMax
    preference sampling reward hmax first hfirstMass
  have hsecondCalibration := bradleyTerryFit_averageCalibration_of_globalMax
    preference sampling reward hmax second hsecondMass
  constructor
  · intro hreward
    calc
      preferenceAgainstSampling preference sampling first =
          bradleyTerryAgainstSampling reward sampling first := hfirstCalibration
      _ < bradleyTerryAgainstSampling reward sampling second :=
        bradleyTerryAgainstSampling_strictMono_reward reward sampling first second hreward
      _ = preferenceAgainstSampling preference sampling second := hsecondCalibration.symm
  · intro hpreference
    by_contra hnot
    have hreward : reward second ≤ reward first := le_of_not_gt hnot
    have hfitted : bradleyTerryAgainstSampling reward sampling second ≤
        bradleyTerryAgainstSampling reward sampling first :=
      bradleyTerryAgainstSampling_mono_reward reward sampling second first hreward
    have hreverse : preferenceAgainstSampling preference sampling second ≤
        preferenceAgainstSampling preference sampling first := by
      calc
        preferenceAgainstSampling preference sampling second =
            bradleyTerryAgainstSampling reward sampling second := hsecondCalibration
        _ ≤ bradleyTerryAgainstSampling reward sampling first := hfitted
        _ = preferenceAgainstSampling preference sampling first := hfirstCalibration.symm
    exact (not_le_of_gt hpreference) hreverse

end HumanFeedback
end Learning
end AppliedModelingLib
