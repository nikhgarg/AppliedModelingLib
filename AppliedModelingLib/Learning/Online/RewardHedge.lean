import AppliedModelingLib.Learning.Online.Hedge

/-!
# Hedge for centered rewards

The finite weak-agnostic-learning reduction uses rewards in `[-1,1]`, while
the shared Hedge development is stated for losses in `[0,1]`.  This module
records their exact affine conversion and the corresponding trajectory
identity, so a source paper can invoke Hedge without treating its reward
regret as an oracle certificate.
-/

namespace AppliedModelingLib.Learning.Online

open scoped BigOperators

/-- Convert a reward in `[-1,1]` to a loss in `[0,1]`. -/
noncomputable def centeredRewardLoss {Action : Type*} (reward : Action → ℝ) : Action → ℝ :=
  fun action => (1 - reward action) / 2

/-- Convert a normalized loss back to its centered reward. -/
def normalizedLossReward {Action : Type*} (loss : Action → ℝ) : Action → ℝ :=
  fun action => 1 - 2 * loss action

/-- The centered reward/loss conversion is pointwise inverse. -/
theorem normalizedLossReward_centeredRewardLoss
    {Action : Type*} (reward : Action → ℝ) :
    normalizedLossReward (centeredRewardLoss reward) = reward := by
  funext action
  unfold normalizedLossReward centeredRewardLoss
  ring

/-- A reward in `[-1,1]` converts to a loss in `[0,1]`. -/
theorem centeredRewardLoss_mem_unitInterval
    {Action : Type*} (reward : Action → ℝ)
    (hbounded : ∀ action, -1 ≤ reward action ∧ reward action ≤ 1) :
    ∀ action, 0 ≤ centeredRewardLoss reward action ∧ centeredRewardLoss reward action ≤ 1 := by
  intro action
  unfold centeredRewardLoss
  constructor <;> linarith [(hbounded action).1, (hbounded action).2]

/-- A fixed coordinate's normalized losses over a centered-reward prefix lie
between zero and the prefix length. -/
theorem centeredRewardLoss_coordinateSum_mem_Icc_zero_length
    {Action : Type*} (rewards : List (Action → ℝ))
    (hrewards : ∀ reward ∈ rewards, ∀ action,
      -1 ≤ reward action ∧ reward action ≤ 1) (action : Action) :
    ((rewards.map centeredRewardLoss).map fun loss => loss action).sum ∈
      Set.Icc (0 : ℝ) (rewards.length : ℝ) := by
  induction rewards with
  | nil => simp
  | cons reward remaining ih =>
      have hhead := centeredRewardLoss_mem_unitInterval reward
        (fun candidate => hrewards reward (by simp) candidate) action
      have htail := ih
        (fun candidate hcandidate coordinate =>
          hrewards candidate (by simp [hcandidate]) coordinate)
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      constructor <;> linarith [hhead.1, hhead.2, htail.1, htail.2]

/-- Elementary local bounds for the exponential discount used by a gain-form
Hedge update.  They are stated in the small-rate regime needed to turn an
exact finite Hedge comparison into a square-root bound. -/
theorem one_sub_exp_neg_two_mul_bounds
    {learningRate : ℝ} (hlearningRate : 0 < learningRate)
    (hlearningRateSmall : learningRate ≤ 1 / 4) :
    learningRate ≤ 1 - Real.exp (-2 * learningRate) ∧
      0 ≤ 2 * learningRate - (1 - Real.exp (-2 * learningRate)) ∧
      2 * learningRate - (1 - Real.exp (-2 * learningRate)) ≤ 4 * learningRate ^ 2 := by
  have hnorm : ‖-2 * learningRate‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hquadratic := Real.norm_exp_sub_one_sub_id_le hnorm
  simp only [Real.norm_eq_abs] at hquadratic
  have hargumentAbs : |-2 * learningRate| = 2 * learningRate := by
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [hargumentAbs] at hquadratic
  have hquadratic' :
      |Real.exp (-2 * learningRate) - 1 + 2 * learningRate| ≤ 4 * learningRate ^ 2 := by
    convert hquadratic using 1 <;> ring_nf
  have herrorUpper : Real.exp (-2 * learningRate) - 1 + 2 * learningRate ≤
      4 * learningRate ^ 2 := (le_abs_self _).trans hquadratic'
  have herrorLower : 0 ≤ Real.exp (-2 * learningRate) - 1 + 2 * learningRate := by
    have hsource := Real.one_sub_le_exp_neg (2 * learningRate)
    have hsource' : 1 - 2 * learningRate ≤ Real.exp (-2 * learningRate) := by
      have hargument : -(2 * learningRate) = -2 * learningRate := by ring
      rw [hargument] at hsource
      exact hsource
    linarith
  have hquadraticScale : learningRate ^ 2 ≤ learningRate / 4 := by
    nlinarith [mul_nonneg (le_of_lt hlearningRate) (sub_nonneg.mpr hlearningRateSmall)]
  constructor
  · nlinarith
  constructor <;> linarith

/-- The exact discount-dependent comparator penalty is at most the familiar
`prior / η + η·T` expression in the small-rate regime.  This lemma is kept
independent of any particular action class or paper. -/
theorem exponentialGainHedgePenalty_le
    {learningRate priorPenalty cumulativeLoss lossBound : ℝ}
    (hlearningRate : 0 < learningRate) (hlearningRateSmall : learningRate ≤ 1 / 4)
    (hpriorPenalty : 0 ≤ priorPenalty) (hlossNonneg : 0 ≤ cumulativeLoss)
    (hlossBound : cumulativeLoss ≤ lossBound) :
    2 * ((priorPenalty + 2 * learningRate * cumulativeLoss) /
        (1 - Real.exp (-2 * learningRate)) - cumulativeLoss) ≤
      2 * (priorPenalty / learningRate + 4 * learningRate * lossBound) := by
  rcases one_sub_exp_neg_two_mul_bounds hlearningRate hlearningRateSmall with
    ⟨hdenominatorLower, herrorNonneg, herrorUpper⟩
  let denominator : ℝ := 1 - Real.exp (-2 * learningRate)
  let error : ℝ := 2 * learningRate - denominator
  have hdenominatorPos : 0 < denominator :=
    lt_of_lt_of_le hlearningRate hdenominatorLower
  have hratioPrior : priorPenalty / denominator ≤ priorPenalty / learningRate :=
    div_le_div_of_nonneg_left hpriorPenalty hlearningRate hdenominatorLower
  have hratioError : error / denominator ≤ 4 * learningRate := by
    calc
      error / denominator ≤ (4 * learningRate ^ 2) / denominator :=
        div_le_div_of_nonneg_right (by simpa [error, denominator] using herrorUpper)
          hdenominatorPos.le
      _ ≤ (4 * learningRate ^ 2) / learningRate :=
        div_le_div_of_nonneg_left (by positivity) hlearningRate hdenominatorLower
      _ = 4 * learningRate := by field_simp [hlearningRate.ne']
  have herrorRatioNonneg : 0 ≤ error / denominator :=
    div_nonneg (by simpa [error, denominator] using herrorNonneg) hdenominatorPos.le
  have hscaledLoss : (error / denominator) * cumulativeLoss ≤
      4 * learningRate * lossBound := by
    calc
      (error / denominator) * cumulativeLoss ≤
          (4 * learningRate) * cumulativeLoss :=
        mul_le_mul_of_nonneg_right hratioError hlossNonneg
      _ ≤ (4 * learningRate) * lossBound :=
        mul_le_mul_of_nonneg_left hlossBound (by positivity)
  have hrearrange :
      (priorPenalty + 2 * learningRate * cumulativeLoss) / denominator - cumulativeLoss =
        priorPenalty / denominator + (error / denominator) * cumulativeLoss := by
    field_simp [hdenominatorPos.ne']
    dsimp [error]
    ring
  change 2 * ((priorPenalty + 2 * learningRate * cumulativeLoss) / denominator -
    cumulativeLoss) ≤ 2 * (priorPenalty / learningRate + 4 * learningRate * lossBound)
  rw [hrearrange]
  nlinarith [hratioPrior, hscaledLoss]

/-- The equal-prior initial state used by the finite centered-reward learner. -/
noncomputable def uniformHedgeWeightState
    (Action : Type*) [Fintype Action] [Nonempty Action] : HedgeWeightState Action where
  weight := fun _ => 1 / (Fintype.card Action : ℝ)
  nonneg := by
    intro action
    exact le_of_lt (one_div_pos.mpr (by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Action)))
  total_pos := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [show (Fintype.card Action : ℝ) ≠ 0 by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Action).ne']
    norm_num

/-- The preceding state has exactly the equal-prior weights required by the
shared finite Hedge theorem. -/
theorem uniformHedgeWeightState_weight
    (Action : Type*) [Fintype Action] [Nonempty Action] (action : Action) :
    (uniformHedgeWeightState Action).weight action = 1 / (Fintype.card Action : ℝ) :=
  rfl

/-- The Hedge trajectory's cumulative centered reward when updates use the
affinely equivalent loss vectors. -/
noncomputable def hedgeWeightStateCumulativeCenteredReward
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) :
    HedgeWeightState Action → List (Action → ℝ) → ℝ
  | _, [] => 0
  | state, reward :: remaining =>
      state.expectation reward +
        hedgeWeightStateCumulativeCenteredReward discount hdiscount
          (hedgeWeightStateStep state (centeredRewardLoss reward) discount hdiscount) remaining

/-- Running finite Hedge over a concatenated loss sequence is the same as
first running the prefix and then continuing from its terminal state.  This
small trajectory lemma lets paper-level adaptive executions reuse the shared
fixed-sequence Hedge theorem after exposing their sampled reward prefix. -/
theorem hedgeWeightStateRun_append
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount)
    (state : HedgeWeightState Action) (earlier later : List (Action → ℝ)) :
    hedgeWeightStateRun discount hdiscount state (earlier ++ later) =
      hedgeWeightStateRun discount hdiscount
        (hedgeWeightStateRun discount hdiscount state earlier) later := by
  induction earlier generalizing state with
  | nil => simp [hedgeWeightStateRun]
  | cons loss earlier ih =>
      simp only [List.cons_append, hedgeWeightStateRun]
      exact ih (hedgeWeightStateStep state loss discount hdiscount)

/-- Cumulative centered reward also composes across a chronological append.
The terminal state of the first segment is represented by the shared loss-run
on its affine loss image. -/
theorem hedgeWeightStateCumulativeCenteredReward_append
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (state : HedgeWeightState Action)
    (earlier later : List (Action → ℝ)) :
    hedgeWeightStateCumulativeCenteredReward discount hdiscount state (earlier ++ later) =
      hedgeWeightStateCumulativeCenteredReward discount hdiscount state earlier +
        hedgeWeightStateCumulativeCenteredReward discount hdiscount
          (hedgeWeightStateRun discount hdiscount state (earlier.map centeredRewardLoss)) later := by
  induction earlier generalizing state with
  | nil =>
      simp only [List.nil_append, List.map_nil, hedgeWeightStateRun]
      rw [hedgeWeightStateCumulativeCenteredReward.eq_1, zero_add]
  | cons reward earlier ih =>
      simp only [List.cons_append, List.map_cons,
        hedgeWeightStateCumulativeCenteredReward.eq_2, hedgeWeightStateRun]
      rw [ih]
      ring

/-- A pathwise upper bound on the current expected reward at every state of a
centered-reward Hedge run.  This is the exact shape supplied by a Blackwell
halfspace response oracle. -/
def HedgeCenteredRewardStepUpperBound
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) :
    HedgeWeightState Action → List (Action → ℝ) → ℝ → Prop
  | _, [], _ => True
  | state, reward :: remaining, bound =>
      state.expectation reward ≤ bound ∧
        HedgeCenteredRewardStepUpperBound discount hdiscount
          (hedgeWeightStateStep state (centeredRewardLoss reward) discount hdiscount)
          remaining bound

/-- Summing a pathwise halfspace bound controls the full expected-reward
trajectory. -/
theorem hedgeWeightStateCumulativeCenteredReward_le_of_stepUpperBound
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (state : HedgeWeightState Action)
    (rewards : List (Action → ℝ)) (bound : ℝ)
    (hbound : HedgeCenteredRewardStepUpperBound discount hdiscount state rewards bound) :
    hedgeWeightStateCumulativeCenteredReward discount hdiscount state rewards ≤
      (rewards.length : ℝ) * bound := by
  induction rewards generalizing state with
  | nil => simp [hedgeWeightStateCumulativeCenteredReward]
  | cons reward remaining ih =>
      simp only [HedgeCenteredRewardStepUpperBound] at hbound
      simp only [hedgeWeightStateCumulativeCenteredReward, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      have htail := ih
        (hedgeWeightStateStep state (centeredRewardLoss reward) discount hdiscount) hbound.2
      nlinarith [hbound.1]

/-- Expected centered reward and expected normalized loss are affinely dual
under every Hedge allocation. -/
theorem HedgeWeightState.expectation_centeredReward_eq
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    (state : HedgeWeightState Action) (reward : Action → ℝ) :
    state.expectation reward = 1 - 2 * state.expectation (centeredRewardLoss reward) := by
  have hrewards : reward = fun action => 1 - 2 * centeredRewardLoss reward action := by
    funext action
    unfold centeredRewardLoss
    ring
  calc
    state.expectation reward =
        state.expectation (fun action => 1 - 2 * centeredRewardLoss reward action) :=
      congrArg state.expectation hrewards
    _ = 1 - 2 * state.expectation (centeredRewardLoss reward) := by
      unfold HedgeWeightState.expectation
      rw [pmfExp_sub, pmfExp_const, pmfExp_const_mul]

/-- The entire centered-reward Hedge trajectory is exactly `T - 2L`, where
`L` is the shared normalized-loss trajectory. -/
theorem hedgeWeightStateCumulativeCenteredReward_eq_length_sub_two_mul_loss
    {Action : Type*} [Fintype Action] [Nonempty Action] [DecidableEq Action]
    (discount : ℝ) (hdiscount : 0 < discount) (state : HedgeWeightState Action)
    (rewards : List (Action → ℝ)) :
    hedgeWeightStateCumulativeCenteredReward discount hdiscount state rewards =
      (rewards.length : ℝ) - 2 * hedgeWeightStateCumulativeLoss discount hdiscount state
        (rewards.map centeredRewardLoss) := by
  induction rewards generalizing state with
  | nil => simp [hedgeWeightStateCumulativeCenteredReward, hedgeWeightStateCumulativeLoss]
  | cons reward remaining ih =>
      simp only [hedgeWeightStateCumulativeCenteredReward,
        hedgeWeightStateCumulativeLoss.eq_2, List.map_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one]
      rw [ih, HedgeWeightState.expectation_centeredReward_eq]
      ring

/-- A fixed action's cumulative centered reward is `T - 2` times its
cumulative normalized loss. -/
theorem centeredReward_sum_eq_length_sub_two_mul_loss_sum
    {Action : Type*} (rewards : List (Action → ℝ)) (action : Action) :
    (rewards.map fun reward => reward action).sum =
      (rewards.length : ℝ) - 2 *
        ((rewards.map centeredRewardLoss).map fun loss => loss action).sum := by
  induction rewards with
  | nil => simp
  | cons reward remaining ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [ih]
      unfold centeredRewardLoss
      ring

/-- Exact finite comparator bound for gain-form Hedge at an arbitrary
interior discount.  This is the reward-language form of the shared
Freund--Schapire finite theorem, retaining the exact discount-dependent
penalty for applications whose source algorithm fixes its own learning rate. -/
theorem uniformHedgeWeightState_coordinateCenteredReward_le_exact
    {Action : Type*} [Fintype Action] [Nonempty Action] [DecidableEq Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_lt_one : discount < 1)
    (rewards : List (Action → ℝ))
    (hrewards : ∀ reward ∈ rewards, ∀ action,
      -1 ≤ reward action ∧ reward action ≤ 1)
    (action : Action) :
    (rewards.map fun reward => reward action).sum ≤
      hedgeWeightStateCumulativeCenteredReward discount hdiscount
        (uniformHedgeWeightState Action) rewards +
        2 * ((-Real.log (1 / (Fintype.card Action : ℝ)) -
          ((rewards.map centeredRewardLoss).map fun loss => loss action).sum * Real.log discount) /
          (1 - discount) -
          ((rewards.map centeredRewardLoss).map fun loss => loss action).sum) := by
  have hcardPos : 0 < (Fintype.card Action : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Action)
  have hinitial : (∑ candidate, (uniformHedgeWeightState Action).weight candidate) = 1 := by
    calc
      (∑ candidate, (uniformHedgeWeightState Action).weight candidate) =
          ∑ _candidate : Action, 1 / (Fintype.card Action : ℝ) := by
            apply Finset.sum_congr rfl
            intro candidate _
            exact uniformHedgeWeightState_weight Action candidate
      _ = (Fintype.card Action : ℝ) * (1 / (Fintype.card Action : ℝ)) := by
            simp [nsmul_eq_mul]
      _ = 1 := by field_simp [hcardPos.ne']
  have hweight : 0 < (uniformHedgeWeightState Action).weight action := by
    rw [uniformHedgeWeightState_weight]
    exact one_div_pos.mpr hcardPos
  have hloss : ∀ loss ∈ rewards.map centeredRewardLoss, ∀ candidate,
      0 ≤ loss candidate ∧ loss candidate ≤ 1 := by
    intro loss hlossMem candidate
    obtain ⟨reward, hreward, rfl⟩ := List.mem_map.mp hlossMem
    exact centeredRewardLoss_mem_unitInterval reward (hrewards reward hreward) candidate
  have hhedge := hedgeWeightState_theorem2_single_finite discount hdiscount hdiscount_lt_one
    (uniformHedgeWeightState Action) hinitial (rewards.map centeredRewardLoss) hloss action hweight
  rw [uniformHedgeWeightState_weight] at hhedge
  rw [centeredReward_sum_eq_length_sub_two_mul_loss_sum,
    hedgeWeightStateCumulativeCenteredReward_eq_length_sub_two_mul_loss]
  nlinarith

/-- The actual equal-prior Hedge execution, viewed as a centered-reward
learner, is within twice Hedge's loss regret of every fixed action.  This is
the finite online weak-agnostic-learning primitive used by the paper. -/
theorem uniformHedgeWeightState_centeredReward_sqrt_regret_bound
    {Action : Type*} [Fintype Action] [Nonempty Action] [DecidableEq Action]
    (rewards : List (Action → ℝ)) (hrewards : ∀ reward ∈ rewards, ∀ action,
      -1 ≤ reward action ∧ reward action ≤ 1)
    (hrewards_nonempty : rewards ≠ []) (hcard : 1 < Fintype.card Action)
    (action : Action) :
    (rewards.map fun reward => reward action).sum -
        2 * (Real.sqrt (2 * (rewards.length : ℝ) * Real.log (Fintype.card Action : ℝ)) +
          Real.log (Fintype.card Action : ℝ)) ≤
      hedgeWeightStateCumulativeCenteredReward
        (hedgeDiscountFromBounds (rewards.length : ℝ) (Real.log (Fintype.card Action : ℝ)))
        (by
          unfold hedgeDiscountFromBounds
          apply one_div_pos.mpr
          have hlength_nat_pos : 0 < rewards.length := List.length_pos_of_ne_nil hrewards_nonempty
          have hlength_pos : 0 < (rewards.length : ℝ) := by
            exact_mod_cast hlength_nat_pos
          have hcard_real : 1 < (Fintype.card Action : ℝ) := by
            exact_mod_cast hcard
          have hlog_pos : 0 < Real.log (Fintype.card Action : ℝ) :=
            Real.log_pos hcard_real
          have hratio_pos : 0 < 2 * Real.log (Fintype.card Action : ℝ) /
              (rewards.length : ℝ) := by
            exact div_pos (mul_pos (by norm_num) hlog_pos) hlength_pos
          nlinarith [Real.sqrt_pos.mpr hratio_pos])
        (uniformHedgeWeightState Action) rewards := by
  let discount := hedgeDiscountFromBounds (rewards.length : ℝ)
    (Real.log (Fintype.card Action : ℝ))
  have hdiscount : 0 < discount := by
    unfold discount hedgeDiscountFromBounds
    apply one_div_pos.mpr
    have hlength_nat_pos : 0 < rewards.length := List.length_pos_of_ne_nil hrewards_nonempty
    have hlength_pos : 0 < (rewards.length : ℝ) := by
      exact_mod_cast hlength_nat_pos
    have hcard_real : 1 < (Fintype.card Action : ℝ) := by
      exact_mod_cast hcard
    have hlog_pos : 0 < Real.log (Fintype.card Action : ℝ) := Real.log_pos hcard_real
    have hratio_pos : 0 < 2 * Real.log (Fintype.card Action : ℝ) /
        (rewards.length : ℝ) := by
      exact div_pos (mul_pos (by norm_num) hlog_pos) hlength_pos
    nlinarith [Real.sqrt_pos.mpr hratio_pos]
  have hnormalized : ∀ loss ∈ rewards.map centeredRewardLoss, ∀ action,
      0 ≤ loss action ∧ loss action ≤ 1 := by
    intro loss hloss
    obtain ⟨reward, hreward, rfl⟩ := List.mem_map.mp hloss
    exact centeredRewardLoss_mem_unitInterval reward (hrewards reward hreward)
  have hbound := hedgeWeightState_uniform_sqrt_regret_bound
    (uniformHedgeWeightState Action) (uniformHedgeWeightState_weight Action)
    (rewards.map centeredRewardLoss) (by simpa using hrewards_nonempty) hnormalized hcard
  have hbound' :
      hedgeWeightStateCumulativeLoss discount hdiscount (uniformHedgeWeightState Action)
          (rewards.map centeredRewardLoss) ≤
        (Finset.univ.inf' Finset.univ_nonempty
          (fun candidate => ((rewards.map centeredRewardLoss).map fun loss =>
            loss candidate).sum)) +
          Real.sqrt (2 * (rewards.length : ℝ) * Real.log (Fintype.card Action : ℝ)) +
            Real.log (Fintype.card Action : ℝ) := by
    simpa [discount] using hbound
  have hbest :
      Finset.univ.inf' Finset.univ_nonempty
          (fun candidate => ((rewards.map centeredRewardLoss).map fun loss =>
            loss candidate).sum) ≤
        ((rewards.map centeredRewardLoss).map fun loss => loss action).sum :=
    Finset.inf'_le _ (Finset.mem_univ action)
  rw [centeredReward_sum_eq_length_sub_two_mul_loss_sum,
    hedgeWeightStateCumulativeCenteredReward_eq_length_sub_two_mul_loss]
  dsimp [discount] at hbound'
  nlinarith

/-- Combining a Blackwell halfspace response bound with equal-prior Hedge
controls every individual reward coordinate.  This is the reusable
gain-form exponential-weights step behind the proper-calibration and
augmented-calibrator algorithms. -/
theorem uniformHedgeWeightState_coordinateReward_le_of_stepUpperBound
    {Action : Type*} [Fintype Action] [Nonempty Action] [DecidableEq Action]
    (rewards : List (Action → ℝ)) (hrewards : ∀ reward ∈ rewards, ∀ action,
      -1 ≤ reward action ∧ reward action ≤ 1)
    (hrewards_nonempty : rewards ≠ []) (hcard : 1 < Fintype.card Action)
    (bound : ℝ)
    (hhalfspace : HedgeCenteredRewardStepUpperBound
      (hedgeDiscountFromBounds (rewards.length : ℝ) (Real.log (Fintype.card Action : ℝ)))
      (by
        unfold hedgeDiscountFromBounds
        apply one_div_pos.mpr
        have hlength_nat_pos : 0 < rewards.length := List.length_pos_of_ne_nil hrewards_nonempty
        have hlength_pos : 0 < (rewards.length : ℝ) := by
          exact_mod_cast hlength_nat_pos
        have hcard_real : 1 < (Fintype.card Action : ℝ) := by
          exact_mod_cast hcard
        have hlog_pos : 0 < Real.log (Fintype.card Action : ℝ) :=
          Real.log_pos hcard_real
        have hratio_pos : 0 < 2 * Real.log (Fintype.card Action : ℝ) /
            (rewards.length : ℝ) := by
          exact div_pos (mul_pos (by norm_num) hlog_pos) hlength_pos
        nlinarith [Real.sqrt_pos.mpr hratio_pos])
      (uniformHedgeWeightState Action) rewards bound)
    (action : Action) :
    (rewards.map fun reward => reward action).sum ≤
      (rewards.length : ℝ) * bound +
        2 * (Real.sqrt (2 * (rewards.length : ℝ) * Real.log (Fintype.card Action : ℝ)) +
          Real.log (Fintype.card Action : ℝ)) := by
  have hregret := uniformHedgeWeightState_centeredReward_sqrt_regret_bound
    rewards hrewards hrewards_nonempty hcard action
  have htrajectory := hedgeWeightStateCumulativeCenteredReward_le_of_stepUpperBound
    (hedgeDiscountFromBounds (rewards.length : ℝ) (Real.log (Fintype.card Action : ℝ)))
    (by
      unfold hedgeDiscountFromBounds
      apply one_div_pos.mpr
      have hlength_nat_pos : 0 < rewards.length := List.length_pos_of_ne_nil hrewards_nonempty
      have hlength_pos : 0 < (rewards.length : ℝ) := by
        exact_mod_cast hlength_nat_pos
      have hcard_real : 1 < (Fintype.card Action : ℝ) := by
        exact_mod_cast hcard
      have hlog_pos : 0 < Real.log (Fintype.card Action : ℝ) :=
        Real.log_pos hcard_real
      have hratio_pos : 0 < 2 * Real.log (Fintype.card Action : ℝ) /
          (rewards.length : ℝ) := by
        exact div_pos (mul_pos (by norm_num) hlog_pos) hlength_pos
      nlinarith [Real.sqrt_pos.mpr hratio_pos])
    (uniformHedgeWeightState Action) rewards bound hhalfspace
  nlinarith

end AppliedModelingLib.Learning.Online
