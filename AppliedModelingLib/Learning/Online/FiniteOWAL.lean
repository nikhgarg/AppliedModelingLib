import AppliedModelingLib.Learning.Online.RewardHedge

/-!
# Finite online weak agnostic learning

The finite-class OWAL construction in Okoroafor--Kleinberg--Kim (2025) is
equal-prior Hedge on the centered rewards `c(x_t) y_t`.  The learner returns
the current weighted average of the candidate functions, rather than sampling
one candidate.  This module makes that executable deterministic strategy and
its comparator guarantee explicit.
-/

namespace AppliedModelingLib.Learning.Online

/-- One candidate's reward on one context-label example. -/
def finiteOWALReward {Candidate Context : Type*}
    (candidates : Candidate → Context → ℝ) (observation : Context × ℝ) : Candidate → ℝ :=
  fun candidate => candidates candidate observation.1 * observation.2

/-- The loss-form Hedge discount corresponding to the source gain learning
rate `η`.  After the affine reward-to-loss conversion, its common
`exp (-η)` factor cancels in normalization. -/
noncomputable def finiteOWALSourceDiscount (learningRate : ℝ) : ℝ :=
  Real.exp (-2 * learningRate)

/-- The source discount is strictly positive. -/
theorem finiteOWALSourceDiscount_pos (learningRate : ℝ) :
    0 < finiteOWALSourceDiscount learningRate :=
  Real.exp_pos _

/-- Each source-discount loss factor is a common factor times the intended
gain-form exponential reward factor.  Consequently normalized Hedge updates
are precisely the source's positive-exponent weight updates. -/
theorem finiteOWALSourceDiscount_centeredReward_factor
    (learningRate reward : ℝ) :
    finiteOWALSourceDiscount learningRate ^ ((1 - reward) / 2) =
      Real.exp (-learningRate) * Real.exp (learningRate * reward) := by
  unfold finiteOWALSourceDiscount
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The corrected signed-class prediction combines the positive expert with
the negation of the negative-label expert.  The coefficients are a PMF over
the two expert signs. -/
noncomputable def signedOWALCombinedPrediction
    (weights : PMF Bool) (positivePrediction negativePrediction : ℝ) : ℝ :=
  (weights true).toReal * positivePrediction -
    (weights false).toReal * negativePrediction

/-- The corrected signed mixture's reward is exactly the Hedge expectation of
the positive expert reward and the negated negative-label expert reward. -/
theorem signedOWALCombinedPrediction_mul_label_eq_expectation
    (weights : PMF Bool) (positivePrediction negativePrediction label : ℝ) :
    signedOWALCombinedPrediction weights positivePrediction negativePrediction * label =
      pmfExp weights (fun sign => if sign then positivePrediction * label else
        -negativePrediction * label) := by
  unfold signedOWALCombinedPrediction pmfExp
  rw [show (Finset.univ : Finset Bool) = {false, true} by decide]
  simp
  ring

/-- The two rewards compared by the signed-class combiner: the ordinary OWAL
reward and the reward of the negative-label OWAL after its prediction is
negated back to the original label convention. -/
def signedOWALTwoExpertReward (rewards : ℝ × ℝ) : Bool → ℝ :=
  fun sign => if sign then rewards.1 else rewards.2

/-- Cumulative reward of the two-expert Hedge layer in the corrected signed
OWAL construction. -/
noncomputable def signedOWALTwoExpertCumulativeReward
    (discount : ℝ) (hdiscount : 0 < discount) (roundRewards : List (ℝ × ℝ)) : ℝ :=
  hedgeWeightStateCumulativeCenteredReward discount hdiscount
    (uniformHedgeWeightState Bool) (roundRewards.map signedOWALTwoExpertReward)

/-- The exact regret penalty of the source's positive-exponent two-expert
Hedge combiner against one named signed base expert. -/
noncomputable def signedOWALTwoExpertSourceGainPenalty
    (learningRate : ℝ) (roundRewards : List (ℝ × ℝ)) (sign : Bool) : ℝ :=
  2 * ((-Real.log (1 / (Fintype.card Bool : ℝ)) -
    ((roundRewards.map signedOWALTwoExpertReward).map centeredRewardLoss |>.map
      fun loss => loss sign).sum * Real.log (finiteOWALSourceDiscount learningRate)) /
    (1 - finiteOWALSourceDiscount learningRate) -
    ((roundRewards.map signedOWALTwoExpertReward).map centeredRewardLoss |>.map
      fun loss => loss sign).sum)

/-- The source positive-exponent two-expert combiner is within its exact Hedge
penalty of either signed base-expert reward sequence. -/
theorem signedOWALTwoExpert_sourceGain_exact_regret_bound
    (learningRate : ℝ) (hlearningRate : 0 < learningRate)
    (roundRewards : List (ℝ × ℝ))
    (hbounded : ∀ rewards ∈ roundRewards,
      -1 ≤ rewards.1 ∧ rewards.1 ≤ 1 ∧ -1 ≤ rewards.2 ∧ rewards.2 ≤ 1)
    (sign : Bool) :
    (roundRewards.map fun rewards => if sign then rewards.1 else rewards.2).sum ≤
      signedOWALTwoExpertCumulativeReward
        (finiteOWALSourceDiscount learningRate)
        (finiteOWALSourceDiscount_pos learningRate) roundRewards +
        signedOWALTwoExpertSourceGainPenalty learningRate roundRewards sign := by
  have hdiscount_lt_one : finiteOWALSourceDiscount learningRate < 1 := by
    unfold finiteOWALSourceDiscount
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hrewardBound : ∀ reward ∈ roundRewards.map signedOWALTwoExpertReward,
      ∀ expert, -1 ≤ reward expert ∧ reward expert ≤ 1 := by
    intro reward hreward expert
    obtain ⟨rewards, hmember, rfl⟩ := List.mem_map.mp hreward
    obtain ⟨hpositiveLower, hpositiveUpper, hnegativeLower, hnegativeUpper⟩ :=
      hbounded rewards hmember
    cases expert <;> simp [signedOWALTwoExpertReward, *]
  have hhedge := uniformHedgeWeightState_coordinateCenteredReward_le_exact
    (finiteOWALSourceDiscount learningRate) (finiteOWALSourceDiscount_pos learningRate)
    hdiscount_lt_one (roundRewards.map signedOWALTwoExpertReward) hrewardBound sign
  simpa [signedOWALTwoExpertCumulativeReward, signedOWALTwoExpertSourceGainPenalty,
    signedOWALTwoExpertReward] using hhedge

/-- The exact two-expert source-gain penalty is bounded by the standard
`log 2 / η + 4ηT` expression in the small-rate regime. -/
theorem signedOWALTwoExpert_sourceGain_smallRate_penalty_le
    (learningRate : ℝ) (hlearningRate : 0 < learningRate)
    (hlearningRateSmall : learningRate ≤ 1 / 4)
    (roundRewards : List (ℝ × ℝ))
    (hbounded : ∀ rewards ∈ roundRewards,
      -1 ≤ rewards.1 ∧ rewards.1 ≤ 1 ∧ -1 ≤ rewards.2 ∧ rewards.2 ≤ 1)
    (sign : Bool) :
    signedOWALTwoExpertSourceGainPenalty learningRate roundRewards sign ≤
      2 * (Real.log (Fintype.card Bool : ℝ) / learningRate +
        4 * learningRate * (roundRewards.length : ℝ)) := by
  let rewards := roundRewards.map signedOWALTwoExpertReward
  let cumulativeLoss := (rewards.map centeredRewardLoss |>.map fun loss => loss sign).sum
  have hrewardBound : ∀ reward ∈ rewards, ∀ expert,
      -1 ≤ reward expert ∧ reward expert ≤ 1 := by
    intro reward hreward expert
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hreward
    obtain ⟨hpositiveLower, hpositiveUpper, hnegativeLower, hnegativeUpper⟩ :=
      hbounded pair hpair
    cases expert <;> simp [signedOWALTwoExpertReward, *]
  have hlossSum : cumulativeLoss ∈ Set.Icc (0 : ℝ) (roundRewards.length : ℝ) := by
    simpa [rewards, cumulativeLoss] using
      centeredRewardLoss_coordinateSum_mem_Icc_zero_length rewards hrewardBound sign
  have hpriorEq : -Real.log (1 / (Fintype.card Bool : ℝ)) =
      Real.log (Fintype.card Bool : ℝ) := by
    rw [one_div, Real.log_inv]
    ring
  have hpriorNonneg : 0 ≤ -Real.log (1 / (Fintype.card Bool : ℝ)) := by
    rw [hpriorEq]
    exact Real.log_nonneg (by norm_num)
  have hpenalty := exponentialGainHedgePenalty_le
    (learningRate := learningRate)
    (priorPenalty := -Real.log (1 / (Fintype.card Bool : ℝ)))
    (cumulativeLoss := cumulativeLoss) (lossBound := (roundRewards.length : ℝ))
    hlearningRate hlearningRateSmall hpriorNonneg hlossSum.1 hlossSum.2
  have hsumEq :
      ((roundRewards.map signedOWALTwoExpertReward).map centeredRewardLoss |>.map
        fun loss => loss sign).sum = cumulativeLoss := by
    simp [rewards, cumulativeLoss]
  have hnormalized : signedOWALTwoExpertSourceGainPenalty learningRate roundRewards sign =
      2 * ((-Real.log (1 / (Fintype.card Bool : ℝ)) +
        2 * learningRate * cumulativeLoss) /
        (1 - Real.exp (-2 * learningRate)) - cumulativeLoss) := by
    unfold signedOWALTwoExpertSourceGainPenalty
    rw [hsumEq, finiteOWALSourceDiscount, Real.log_exp]
    ring
  rw [hnormalized]
  rw [hpriorEq] at hpenalty ⊢
  exact hpenalty

/-- At the source learning rate `1 / sqrt T`, the corrected two-expert
source-gain combiner has an explicit `O(sqrt T)` penalty.  The deliberately
loose constant `10` keeps this reusable numerical corollary independent of
the later paper-specific oracle terms. -/
theorem signedOWALTwoExpert_sourceRate_penalty_le
    {horizon : ℕ} (horizonLarge : 16 ≤ horizon)
    (roundRewards : List (ℝ × ℝ)) (hlength : roundRewards.length = horizon)
    (hbounded : ∀ rewards ∈ roundRewards,
      -1 ≤ rewards.1 ∧ rewards.1 ≤ 1 ∧ -1 ≤ rewards.2 ∧ rewards.2 ≤ 1)
    (sign : Bool) :
    signedOWALTwoExpertSourceGainPenalty (1 / Real.sqrt (horizon : ℝ)) roundRewards sign ≤
      10 * Real.sqrt (horizon : ℝ) := by
  have hTpos : 0 < (horizon : ℝ) := by
    exact_mod_cast (show 0 < horizon by omega)
  have hsqrtPos : 0 < Real.sqrt (horizon : ℝ) := Real.sqrt_pos.2 hTpos
  have hsqrtLarge : 4 ≤ Real.sqrt (horizon : ℝ) := by
    apply (Real.le_sqrt (x := (4 : ℝ)) (y := (horizon : ℝ)) (by norm_num) hTpos.le).2
    norm_num
    exact_mod_cast horizonLarge
  have hratePos : 0 < 1 / Real.sqrt (horizon : ℝ) := one_div_pos.mpr hsqrtPos
  have hrateSmall : 1 / Real.sqrt (horizon : ℝ) ≤ 1 / 4 := by
    exact one_div_le_one_div_of_le (by norm_num) hsqrtLarge
  have hsmall := signedOWALTwoExpert_sourceGain_smallRate_penalty_le
    (1 / Real.sqrt (horizon : ℝ)) hratePos hrateSmall roundRewards hbounded sign
  have hlog : Real.log (Fintype.card Bool : ℝ) ≤ 1 := by
    calc
      Real.log (Fintype.card Bool : ℝ) = Real.log 2 := by norm_num
      _ ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hdivsqrt : (horizon : ℝ) / Real.sqrt (horizon : ℝ) = Real.sqrt (horizon : ℝ) := by
    exact Real.div_sqrt
  rw [hlength] at hsmall
  rw [show Real.log (Fintype.card Bool : ℝ) / (1 / Real.sqrt (horizon : ℝ)) =
      Real.log (Fintype.card Bool : ℝ) * Real.sqrt (horizon : ℝ) by
        field_simp [hsqrtPos.ne']] at hsmall
  have hscale : (1 / Real.sqrt (horizon : ℝ)) * (horizon : ℝ) =
      Real.sqrt (horizon : ℝ) := by
    calc
      (1 / Real.sqrt (horizon : ℝ)) * (horizon : ℝ) =
          (horizon : ℝ) / Real.sqrt (horizon : ℝ) := by ring
      _ = Real.sqrt (horizon : ℝ) := hdivsqrt
  have hlogscaled : Real.log (Fintype.card Bool : ℝ) * Real.sqrt (horizon : ℝ) ≤
      Real.sqrt (horizon : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hlog hsqrtPos.le
  nlinarith [hsmall, hscale, hlogscaled]

/-- Combining OWAL guarantees for the original and negated label streams with
a two-expert Hedge comparison gives a guarantee for the signed class.  This
is purely pathwise: the first two bounds come from the two base learners and
the last two from the corrected Hedge mixture. -/
theorem signedOWAL_transfer_of_twoExpertRegret
    {Comparator : Type*} (positiveTarget negativeTarget : Comparator → ℝ)
    (positiveReward negativeReward combinedReward oracleRegret metaRegret : ℝ)
    (hpositive : ∀ comparator,
      positiveTarget comparator ≤ positiveReward + oracleRegret)
    (hnegative : ∀ comparator,
      negativeTarget comparator ≤ negativeReward + oracleRegret)
    (hmetaPositive : positiveReward ≤ combinedReward + metaRegret)
    (hmetaNegative : negativeReward ≤ combinedReward + metaRegret) :
    ∀ sign : Bool, ∀ comparator,
      (if sign then positiveTarget comparator else negativeTarget comparator) ≤
        combinedReward + oracleRegret + metaRegret := by
  intro sign comparator
  cases sign
  · change negativeTarget comparator ≤ combinedReward + oracleRegret + metaRegret
    linarith [hnegative comparator, hmetaNegative]
  · change positiveTarget comparator ≤ combinedReward + oracleRegret + metaRegret
    linarith [hpositive comparator, hmetaPositive]

/-- The deterministic mixture prediction made by finite Hedge OWAL before
seeing the current label. -/
noncomputable def finiteHedgeOWALPrediction {Candidate Context : Type*}
    [Fintype Candidate] (state : HedgeWeightState Candidate)
    (candidates : Candidate → Context → ℝ) (context : Context) : ℝ :=
  state.expectation (fun candidate => candidates candidate context)

/-- Run the finite OWAL strategy on a finite context-label path.  The next
Hedge state uses exactly the reward vector induced by that revealed example. -/
noncomputable def finiteHedgeOWALCumulativeCorrelation
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    (discount : ℝ) (hdiscount : 0 < discount) (candidates : Candidate → Context → ℝ) :
    HedgeWeightState Candidate → List (Context × ℝ) → ℝ
  | _, [] => 0
  | state, observation :: remaining =>
      finiteHedgeOWALPrediction state candidates observation.1 * observation.2 +
        finiteHedgeOWALCumulativeCorrelation discount hdiscount candidates
          (hedgeWeightStateStep state (centeredRewardLoss (finiteOWALReward candidates observation))
            discount hdiscount) remaining

/-- The strategy's displayed prediction reward is the Hedge expectation of
the corresponding candidate-reward vector. -/
theorem finiteHedgeOWALPrediction_mul_label_eq_expectation_reward
    {Candidate Context : Type*} [Fintype Candidate] [DecidableEq Candidate]
    (state : HedgeWeightState Candidate) (candidates : Candidate → Context → ℝ)
    (context : Context) (label : ℝ) :
    finiteHedgeOWALPrediction state candidates context * label =
      state.expectation (finiteOWALReward candidates (context, label)) := by
  unfold finiteHedgeOWALPrediction finiteOWALReward HedgeWeightState.expectation
  rw [pmfExp_mul_const]

/-- The concrete deterministic OWAL execution is the centered-reward Hedge
trajectory on the candidate reward vectors. -/
theorem finiteHedgeOWALCumulativeCorrelation_eq_centeredReward
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [DecidableEq Candidate] (discount : ℝ) (hdiscount : 0 < discount)
    (state : HedgeWeightState Candidate) (candidates : Candidate → Context → ℝ)
    (examples : List (Context × ℝ)) :
    finiteHedgeOWALCumulativeCorrelation discount hdiscount candidates state examples =
      hedgeWeightStateCumulativeCenteredReward discount hdiscount state
        (examples.map (finiteOWALReward candidates)) := by
  induction examples generalizing state with
  | nil => simp [finiteHedgeOWALCumulativeCorrelation,
      hedgeWeightStateCumulativeCenteredReward]
  | cons observation remaining ih =>
      simp only [finiteHedgeOWALCumulativeCorrelation,
        hedgeWeightStateCumulativeCenteredReward, List.map_cons]
      rw [ih, finiteHedgeOWALPrediction_mul_label_eq_expectation_reward]

/-- Bounded candidates and labels yield the centered reward range needed by
Hedge. -/
theorem finiteOWALReward_mem_centered_unitInterval
    {Candidate Context : Type*} (candidates : Candidate → Context → ℝ)
    (examples : List (Context × ℝ))
    (hcandidates : ∀ candidate context,
      -1 ≤ candidates candidate context ∧ candidates candidate context ≤ 1)
    (hexamples : ∀ observation ∈ examples, -1 ≤ observation.2 ∧ observation.2 ≤ 1) :
    ∀ reward ∈ examples.map (finiteOWALReward candidates), ∀ candidate,
      -1 ≤ reward candidate ∧ reward candidate ≤ 1 := by
  intro reward hreward candidate
  obtain ⟨observation, hobservation, rfl⟩ := List.mem_map.mp hreward
  have hcandidateAbs : |candidates candidate observation.1| ≤ 1 :=
    (abs_le.mpr (hcandidates candidate observation.1))
  have hlabelAbs : |observation.2| ≤ 1 :=
    (abs_le.mpr (hexamples observation hobservation))
  have hrewardAbs : |candidates candidate observation.1 * observation.2| ≤ 1 := by
    rw [abs_mul]
    calc
      |candidates candidate observation.1| * |observation.2| ≤ 1 * 1 :=
        mul_le_mul hcandidateAbs hlabelAbs (abs_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  exact abs_le.mp hrewardAbs

/-- Finite Hedge OWAL's explicit `O(sqrt(T log |C|))` comparator guarantee.
The learner is the deterministic mixture above, so no sampling or oracle
certificate is hidden in this statement. -/
theorem finiteHedgeOWAL_sqrt_regret_bound
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [DecidableEq Candidate] (candidates : Candidate → Context → ℝ)
    (examples : List (Context × ℝ))
    (hcandidates : ∀ candidate context,
      -1 ≤ candidates candidate context ∧ candidates candidate context ≤ 1)
    (hexamples : ∀ observation ∈ examples, -1 ≤ observation.2 ∧ observation.2 ≤ 1)
    (hexamples_nonempty : examples ≠ []) (hcard : 1 < Fintype.card Candidate)
    (candidate : Candidate) :
    ((examples.map (finiteOWALReward candidates)).map fun reward => reward candidate).sum -
        2 * (Real.sqrt (2 * (examples.length : ℝ) *
          Real.log (Fintype.card Candidate : ℝ)) + Real.log (Fintype.card Candidate : ℝ)) ≤
      finiteHedgeOWALCumulativeCorrelation
        (hedgeDiscountFromBounds (examples.length : ℝ)
          (Real.log (Fintype.card Candidate : ℝ)))
        (by
          unfold hedgeDiscountFromBounds
          apply one_div_pos.mpr
          have hlength_nat_pos : 0 < examples.length :=
            List.length_pos_of_ne_nil hexamples_nonempty
          have hlength_pos : 0 < (examples.length : ℝ) := by
            exact_mod_cast hlength_nat_pos
          have hcard_real : 1 < (Fintype.card Candidate : ℝ) := by
            exact_mod_cast hcard
          have hlog_pos : 0 < Real.log (Fintype.card Candidate : ℝ) :=
            Real.log_pos hcard_real
          have hratio_pos : 0 < 2 * Real.log (Fintype.card Candidate : ℝ) /
              (examples.length : ℝ) := by
            exact div_pos (mul_pos (by norm_num) hlog_pos) hlength_pos
          nlinarith [Real.sqrt_pos.mpr hratio_pos])
        candidates (uniformHedgeWeightState Candidate) examples := by
  have hrewardBound := finiteOWALReward_mem_centered_unitInterval candidates examples
    hcandidates hexamples
  have hhedge := uniformHedgeWeightState_centeredReward_sqrt_regret_bound
    (examples.map (finiteOWALReward candidates)) hrewardBound
    (by simpa using hexamples_nonempty) hcard candidate
  rw [finiteHedgeOWALCumulativeCorrelation_eq_centeredReward]
  simpa using hhedge

/-- The exact discount-dependent finite OWAL comparator inequality.  Choosing
`discount = exp (-2η)` makes the normalized update proportional to
`exp (η · c(x_t)y_t)`, which is the gain-form multiplicative-weights update
used by the finite source algorithm. -/
theorem finiteHedgeOWAL_exact_regret_bound
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [DecidableEq Candidate] (discount : ℝ) (hdiscount : 0 < discount)
    (hdiscount_lt_one : discount < 1) (candidates : Candidate → Context → ℝ)
    (examples : List (Context × ℝ))
    (hcandidates : ∀ candidate context,
      -1 ≤ candidates candidate context ∧ candidates candidate context ≤ 1)
    (hexamples : ∀ observation ∈ examples, -1 ≤ observation.2 ∧ observation.2 ≤ 1)
    (candidate : Candidate) :
    ((examples.map (finiteOWALReward candidates)).map fun reward => reward candidate).sum ≤
      finiteHedgeOWALCumulativeCorrelation discount hdiscount candidates
        (uniformHedgeWeightState Candidate) examples +
        2 * ((-Real.log (1 / (Fintype.card Candidate : ℝ)) -
          ((examples.map (finiteOWALReward candidates)).map centeredRewardLoss |>.map
            fun loss => loss candidate).sum * Real.log discount) /
          (1 - discount) -
          ((examples.map (finiteOWALReward candidates)).map centeredRewardLoss |>.map
            fun loss => loss candidate).sum) := by
  have hrewardBound := finiteOWALReward_mem_centered_unitInterval candidates examples
    hcandidates hexamples
  have hhedge := uniformHedgeWeightState_coordinateCenteredReward_le_exact discount hdiscount
    hdiscount_lt_one (examples.map (finiteOWALReward candidates)) hrewardBound candidate
  rw [finiteHedgeOWALCumulativeCorrelation_eq_centeredReward]
  simpa using hhedge

/-- The literal positive-exponent finite OWAL update has the exact Hedge
comparator guarantee.  This is the non-asymptotic form of the source finite
class result; its prescribed `sqrt (log |C| / T)` rate is a later choice of
`learningRate`. -/
theorem finiteHedgeOWAL_sourceGain_exact_regret_bound
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [DecidableEq Candidate] (learningRate : ℝ) (hlearningRate : 0 < learningRate)
    (candidates : Candidate → Context → ℝ) (examples : List (Context × ℝ))
    (hcandidates : ∀ candidate context,
      -1 ≤ candidates candidate context ∧ candidates candidate context ≤ 1)
    (hexamples : ∀ observation ∈ examples, -1 ≤ observation.2 ∧ observation.2 ≤ 1)
    (candidate : Candidate) :
    ((examples.map (finiteOWALReward candidates)).map fun reward => reward candidate).sum ≤
      finiteHedgeOWALCumulativeCorrelation
        (finiteOWALSourceDiscount learningRate)
        (finiteOWALSourceDiscount_pos learningRate) candidates
        (uniformHedgeWeightState Candidate) examples +
        2 * ((-Real.log (1 / (Fintype.card Candidate : ℝ)) -
          ((examples.map (finiteOWALReward candidates)).map centeredRewardLoss |>.map
            fun loss => loss candidate).sum * Real.log (finiteOWALSourceDiscount learningRate)) /
          (1 - finiteOWALSourceDiscount learningRate) -
          ((examples.map (finiteOWALReward candidates)).map centeredRewardLoss |>.map
            fun loss => loss candidate).sum) := by
  have hdiscount_lt_one : finiteOWALSourceDiscount learningRate < 1 := by
    unfold finiteOWALSourceDiscount
    exact Real.exp_lt_one_iff.mpr (by linarith)
  exact finiteHedgeOWAL_exact_regret_bound (finiteOWALSourceDiscount learningRate)
    (finiteOWALSourceDiscount_pos learningRate) hdiscount_lt_one candidates examples
    hcandidates hexamples candidate

/-- The literal source gain update has the standard explicit small-rate
regret bound.  This is derived from its exact penalty rather than replacing
the source update by a different Hedge parameterization. -/
theorem finiteHedgeOWAL_sourceGain_smallRate_regret_bound
    {Candidate Context : Type*} [Fintype Candidate] [Nonempty Candidate]
    [DecidableEq Candidate] (learningRate : ℝ)
    (hlearningRate : 0 < learningRate) (hlearningRateSmall : learningRate ≤ 1 / 4)
    (candidates : Candidate → Context → ℝ) (examples : List (Context × ℝ))
    (hcandidates : ∀ candidate context,
      -1 ≤ candidates candidate context ∧ candidates candidate context ≤ 1)
    (hexamples : ∀ observation ∈ examples, -1 ≤ observation.2 ∧ observation.2 ≤ 1)
    (candidate : Candidate) :
    ((examples.map (finiteOWALReward candidates)).map fun reward => reward candidate).sum -
        2 * ((-Real.log (1 / (Fintype.card Candidate : ℝ))) / learningRate +
          4 * learningRate * (examples.length : ℝ)) ≤
      finiteHedgeOWALCumulativeCorrelation
        (finiteOWALSourceDiscount learningRate)
        (finiteOWALSourceDiscount_pos learningRate) candidates
        (uniformHedgeWeightState Candidate) examples := by
  let losses := (examples.map (finiteOWALReward candidates)).map centeredRewardLoss
  let cumulativeLoss := (losses.map fun loss => loss candidate).sum
  have hrewardBound := finiteOWALReward_mem_centered_unitInterval candidates examples
    hcandidates hexamples
  have hlossSum : cumulativeLoss ∈ Set.Icc (0 : ℝ) (examples.length : ℝ) := by
    simpa [losses, cumulativeLoss] using
      centeredRewardLoss_coordinateSum_mem_Icc_zero_length
        (examples.map (finiteOWALReward candidates)) hrewardBound candidate
  have hcardPositive : 0 < (Fintype.card Candidate : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Candidate)
  have hinvNonneg : 0 ≤ 1 / (Fintype.card Candidate : ℝ) := by positivity
  have hinvLeOne : 1 / (Fintype.card Candidate : ℝ) ≤ 1 := by
    exact (div_le_one hcardPositive).mpr (by
      exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card Candidate)))
  have hpriorNonneg : 0 ≤ -Real.log (1 / (Fintype.card Candidate : ℝ)) := by
    exact neg_nonneg.mpr (Real.log_nonpos hinvNonneg hinvLeOne)
  have hpenalty := exponentialGainHedgePenalty_le
    (learningRate := learningRate)
    (priorPenalty := -Real.log (1 / (Fintype.card Candidate : ℝ)))
    (cumulativeLoss := cumulativeLoss) (lossBound := (examples.length : ℝ))
    hlearningRate hlearningRateSmall hpriorNonneg hlossSum.1 hlossSum.2
  have hraw := finiteHedgeOWAL_sourceGain_exact_regret_bound learningRate hlearningRate
    candidates examples hcandidates hexamples candidate
  have hsumEq :
      ((examples.map (finiteOWALReward candidates)).map centeredRewardLoss |>.map
        fun loss => loss candidate).sum = cumulativeLoss := by
    simp [losses, cumulativeLoss, Function.comp_def]
  have hsumEq' :
      (examples.map ((fun reward => reward candidate) ∘ centeredRewardLoss ∘
        finiteOWALReward candidates)).sum = cumulativeLoss := by
    simpa [Function.comp_def] using hsumEq
  have hpriorEq : -Real.log (1 / (Fintype.card Candidate : ℝ)) =
      Real.log (Fintype.card Candidate : ℝ) := by
    rw [one_div, Real.log_inv]
    ring
  have hrawNormalized :
      ((examples.map (finiteOWALReward candidates)).map fun reward => reward candidate).sum ≤
        finiteHedgeOWALCumulativeCorrelation
          (finiteOWALSourceDiscount learningRate)
          (finiteOWALSourceDiscount_pos learningRate) candidates
          (uniformHedgeWeightState Candidate) examples +
          2 * ((Real.log (Fintype.card Candidate : ℝ) +
            cumulativeLoss * (2 * learningRate)) /
            (1 - Real.exp (-(2 * learningRate))) - cumulativeLoss) := by
    simpa [finiteOWALSourceDiscount, Real.log_exp, hsumEq'] using hraw
  have hraw' :
      ((examples.map (finiteOWALReward candidates)).map fun reward => reward candidate).sum ≤
        finiteHedgeOWALCumulativeCorrelation
          (finiteOWALSourceDiscount learningRate)
          (finiteOWALSourceDiscount_pos learningRate) candidates
          (uniformHedgeWeightState Candidate) examples +
          2 * ((-Real.log (1 / (Fintype.card Candidate : ℝ)) +
            2 * learningRate * cumulativeLoss) /
            (1 - Real.exp (-2 * learningRate)) - cumulativeLoss) := by
    rw [hpriorEq]
    have hnegExponent : -(2 * learningRate) = -2 * learningRate := by ring
    rw [← hnegExponent]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hrawNormalized
  linarith

end AppliedModelingLib.Learning.Online
