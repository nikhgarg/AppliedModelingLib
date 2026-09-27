import AppliedModelingLib.GameTheory.PerformativePrediction

/-!
# Actual supercritical sample-count rates for Theorem 3.10

The concrete Theorem 3.10 schedule is the positive natural ceiling of thirteen
visible gates: six compact-head gates, four logarithmic all-shell gates, and
three source square-rate gates.  This file bounds that *actual* natural count,
rather than postulating a count with the desired asymptotic behavior.

There is an unavoidable endpoint convention in the logarithm.  At the first
Lean round and failure probability one, `log ((round + 1) / p) = 0`, whereas a
sample count is positive.  The uniform statement therefore uses
`1 + log ((round + 1) / p) = log (exp 1 * (round + 1) / p)`.  A literal-log
corollary is given on the range where that logarithm is at least one.
-/

namespace PZMH20PerformativePrediction

open AppliedModelingLib

/-- The source-shaped shifted logarithm.  The shift makes the first-round,
`p = 1` endpoint honest while retaining the same asymptotic rate. -/
noncomputable def theorem310ShiftedRoundLog (p : ℝ) (round : ℕ) : ℝ :=
  1 + Real.log (((round + 1 : ℕ) : ℝ) / p)

/-- A positive constant which simultaneously bounds the five fixed
multipliers appearing inside the confidence and all-shell logarithms. -/
noncomputable def theorem310RoundLogCoefficient : ℝ :=
  2 +
    |Real.log (Real.pi ^ 2 / 3)| +
    |Real.log (8 * Real.pi ^ 2 / 3)| +
    |Real.log (16 * Real.pi ^ 2 / 3)| +
    |Real.log (4 * Real.pi ^ 2 / 3)| +
    |Real.log (4 * Real.pi ^ 2 / (3 * (1 - Real.exp (-1))))|

theorem theorem310RoundLogCoefficient_pos : 0 < theorem310RoundLogCoefficient := by
  unfold theorem310RoundLogCoefficient
  positivity

theorem theorem310ShiftedRoundLog_one_le
    {p : ℝ} (hp : 0 < p) (hp_le_one : p ≤ 1) (round : ℕ) :
    1 ≤ theorem310ShiftedRoundLog p round := by
  have htime : (1 : ℝ) ≤ ((round + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega : round + 1 ≠ 0)
  have hratio : 1 ≤ ((round + 1 : ℕ) : ℝ) / p := by
    apply (one_le_div hp).mpr
    exact hp_le_one.trans htime
  unfold theorem310ShiftedRoundLog
  linarith [Real.log_nonneg hratio]

/-- A reusable elementary comparison for the inverse-square round allocation:
every fixed multiple of `(round+1)^2 / p` has logarithm controlled by the
shifted source logarithm when `p` is a probability. -/
theorem log_constant_mul_time_sq_div_le
    {constant p time : ℝ} (hconstant : 0 < constant)
    (hp : 0 < p) (hp_le_one : p ≤ 1) (htime : 1 ≤ time) :
    Real.log (constant * time ^ 2 / p) ≤
      (2 + |Real.log constant|) * (1 + Real.log (time / p)) := by
  have htime_pos : 0 < time := lt_of_lt_of_le zero_lt_one htime
  have hratio_one : 1 ≤ time / p := by
    apply (one_le_div hp).mpr
    exact hp_le_one.trans htime
  have hratio_pos : 0 < time / p := lt_of_lt_of_le zero_lt_one hratio_one
  have htime_sq_nonneg : 0 ≤ time ^ 2 := sq_nonneg time
  have htime_div : time ^ 2 / p ≤ (time / p) ^ 2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ hp (sq_pos_of_pos hp)).mpr
    have hp_sq_le : p ^ 2 ≤ p := by
      nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hp_le_one)]
    exact mul_le_mul_of_nonneg_left hp_sq_le htime_sq_nonneg
  have hargument_le : constant * time ^ 2 / p ≤ constant * (time / p) ^ 2 := by
    calc
      constant * time ^ 2 / p = constant * (time ^ 2 / p) := by ring
      _ ≤ constant * (time / p) ^ 2 :=
        mul_le_mul_of_nonneg_left htime_div hconstant.le
  have hargument_pos : 0 < constant * time ^ 2 / p := by positivity
  have hupper_pos : 0 < constant * (time / p) ^ 2 := by positivity
  have hlog_le := Real.log_le_log hargument_pos hargument_le
  have hlog_upper :
      Real.log (constant * (time / p) ^ 2) =
        Real.log constant + 2 * Real.log (time / p) := by
    rw [Real.log_mul hconstant.ne' (pow_ne_zero 2 hratio_pos.ne'), Real.log_pow]
    norm_num
  rw [hlog_upper] at hlog_le
  have hlog_ratio_nonneg : 0 ≤ Real.log (time / p) := Real.log_nonneg hratio_one
  have hlog_constant_le : Real.log constant ≤ |Real.log constant| := le_abs_self _
  have habs_nonneg : 0 ≤ |Real.log constant| := abs_nonneg _
  nlinarith [mul_nonneg habs_nonneg hlog_ratio_nonneg]

/-- The one universal logarithmic coefficient dominates the coefficient for
each of the five concrete roundwise logarithms. -/
theorem two_add_abs_log_le_theorem310RoundLogCoefficient (constant : ℝ)
    (hconstant :
      constant = Real.pi ^ 2 / 3 ∨
      constant = 8 * Real.pi ^ 2 / 3 ∨
      constant = 16 * Real.pi ^ 2 / 3 ∨
      constant = 4 * Real.pi ^ 2 / 3 ∨
      constant = 4 * Real.pi ^ 2 / (3 * (1 - Real.exp (-1)))) :
    2 + |Real.log constant| ≤ theorem310RoundLogCoefficient := by
  rcases hconstant with rfl | rfl | rfl | rfl | rfl <;>
    unfold theorem310RoundLogCoefficient <;>
    have hzero := abs_nonneg (Real.log (Real.pi ^ 2 / 3)) <;>
    have hone := abs_nonneg (Real.log (8 * Real.pi ^ 2 / 3)) <;>
    have htwo := abs_nonneg (Real.log (16 * Real.pi ^ 2 / 3)) <;>
    have hthree := abs_nonneg (Real.log (4 * Real.pi ^ 2 / 3)) <;>
    have hfour := abs_nonneg
      (Real.log (4 * Real.pi ^ 2 / (3 * (1 - Real.exp (-1))))) <;>
    linarith

/-- All five logarithms used by the actual concrete count are bounded by one
round factor.  The first component is the nonnegative confidence selector;
the remaining four are exactly the all-shell mass logarithms. -/
theorem theorem310_concrete_round_logs_le
    {p : ℝ} (hp : 0 < p) (hp_le_one : p ≤ 1) (round : ℕ) :
    let budget := theorem310FailureBudget p round
    let tolerance := budget / 2
    let bound := theorem310RoundLogCoefficient * theorem310ShiftedRoundLog p round
    Math.expConfidenceForHalfBudget budget ≤ bound ∧
      Real.log (8 / tolerance) ≤ bound ∧
      Real.log (16 / tolerance) ≤ bound ∧
      Real.log (4 / tolerance) ≤ bound ∧
      Real.log (4 / (tolerance * (1 - Real.exp (-1)))) ≤ bound := by
  dsimp only
  let time : ℝ := ((round + 1 : ℕ) : ℝ)
  let shifted := theorem310ShiftedRoundLog p round
  let coefficient := theorem310RoundLogCoefficient
  have htime : 1 ≤ time := by
    dsimp [time]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega : round + 1 ≠ 0)
  have htime_pos : 0 < time := lt_of_lt_of_le zero_lt_one htime
  have hshifted_one : 1 ≤ shifted := by
    dsimp [shifted]
    exact theorem310ShiftedRoundLog_one_le hp hp_le_one round
  have hcoefficient_pos : 0 < coefficient := by
    dsimp [coefficient]
    exact theorem310RoundLogCoefficient_pos
  have hpi_sq_pos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hone_sub_exp_pos : 0 < 1 - Real.exp (-1) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hgeneric : ∀ constant : ℝ, 0 < constant →
      (constant = Real.pi ^ 2 / 3 ∨
        constant = 8 * Real.pi ^ 2 / 3 ∨
        constant = 16 * Real.pi ^ 2 / 3 ∨
        constant = 4 * Real.pi ^ 2 / 3 ∨
        constant = 4 * Real.pi ^ 2 / (3 * (1 - Real.exp (-1)))) →
      Real.log (constant * time ^ 2 / p) ≤ coefficient * shifted := by
    intro constant hconstant hlisted
    calc
      Real.log (constant * time ^ 2 / p) ≤
          (2 + |Real.log constant|) * (1 + Real.log (time / p)) :=
        log_constant_mul_time_sq_div_le hconstant hp hp_le_one htime
      _ ≤ coefficient * shifted := by
        have hcoefficient := two_add_abs_log_le_theorem310RoundLogCoefficient
          constant hlisted
        have hshifted : 1 + Real.log (time / p) = shifted := by
          dsimp [shifted, theorem310ShiftedRoundLog, time]
        rw [hshifted]
        exact mul_le_mul_of_nonneg_right hcoefficient (zero_le_one.trans hshifted_one)
  have hbudget_pos : 0 < theorem310FailureBudget p round := by
    unfold theorem310FailureBudget
    positivity
  have hconfidence_argument :
      2 / theorem310FailureBudget p round =
        (Real.pi ^ 2 / 3) * time ^ 2 / p := by
    dsimp [time]
    unfold theorem310FailureBudget
    field_simp [hp.ne', Real.pi_ne_zero]
    <;> ring
  have htolEight :
      8 / (theorem310FailureBudget p round / 2) =
        (8 * Real.pi ^ 2 / 3) * time ^ 2 / p := by
    dsimp [time]
    unfold theorem310FailureBudget
    field_simp [hp.ne', Real.pi_ne_zero]
    <;> ring
  have htolSixteen :
      16 / (theorem310FailureBudget p round / 2) =
        (16 * Real.pi ^ 2 / 3) * time ^ 2 / p := by
    dsimp [time]
    unfold theorem310FailureBudget
    field_simp [hp.ne', Real.pi_ne_zero]
    <;> ring
  have htolFour :
      4 / (theorem310FailureBudget p round / 2) =
        (4 * Real.pi ^ 2 / 3) * time ^ 2 / p := by
    dsimp [time]
    unfold theorem310FailureBudget
    field_simp [hp.ne', Real.pi_ne_zero]
    <;> ring
  have htolFourTail :
      4 / ((theorem310FailureBudget p round / 2) * (1 - Real.exp (-1))) =
        (4 * Real.pi ^ 2 / (3 * (1 - Real.exp (-1)))) * time ^ 2 / p := by
    dsimp [time]
    unfold theorem310FailureBudget
    field_simp [hp.ne', Real.pi_ne_zero, hone_sub_exp_pos.ne']
    <;> ring
  have hconfidenceLog : Real.log (2 / theorem310FailureBudget p round) ≤
      coefficient * shifted := by
    rw [hconfidence_argument]
    exact hgeneric _ (by positivity) (Or.inl rfl)
  have hbound_nonneg : 0 ≤ coefficient * shifted :=
    mul_nonneg hcoefficient_pos.le (zero_le_one.trans hshifted_one)
  constructor
  · unfold Math.expConfidenceForHalfBudget
    exact max_le hbound_nonneg hconfidenceLog
  constructor
  · rw [htolEight]
    exact hgeneric _ (by positivity) (Or.inr (Or.inl rfl))
  constructor
  · rw [htolSixteen]
    exact hgeneric _ (by positivity) (Or.inr (Or.inr (Or.inl rfl)))
  constructor
  · rw [htolFour]
    exact hgeneric _ (by positivity) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · rw [htolFourTail]
    exact hgeneric _ (by positivity) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- The shell depth used by the rate specialization is the repository's
existing Fournier--Guillin small-deviation cutoff. -/
noncomputable def theorem310SupercriticalRateCutoff (eta radius : ℝ) : ℕ :=
  Probability.pOneFournierGuillinHeadCutoff eta radius

/-- The actual capped Theorem 3.10 schedule, specialized so that both its
scaled deviation and its compact-head tolerance are the same statistical
radius. -/
noncomputable def theorem310SupercriticalRateCountSchedule
    (dimension : ℕ) (eta alpha gamma momentBound tailBound radius p : ℝ) : ℕ → ℕ :=
  pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
    dimension (theorem310SupercriticalRateCutoff eta radius)
    eta alpha gamma momentBound tailBound radius p radius

/-- In a supercritical dimension, every fixed inverse power up through the
dimension is bounded by the dimension-rate inverse power on `(0,1]`. -/
theorem one_div_pow_le_one_div_pow_dimension
    {radius : ℝ} (hradius : 0 < radius) (hradius_le_one : radius ≤ 1)
    {power dimension : ℕ} (hpower : power ≤ dimension) :
    1 / radius ^ power ≤ 1 / radius ^ dimension := by
  have hpow : radius ^ dimension ≤ radius ^ power :=
    pow_le_pow_of_le_one hradius.le hradius_le_one hpower
  exact one_div_le_one_div_of_le (pow_pos hradius dimension) hpow

/-- The concrete logarithmic shell cutoff contributes no extra radius factor
in dimension greater than two: its `cutoff / r²` term is absorbed by `r⁻ᵈ`.
This is the precise analytic bridge missing from the schedule label alone. -/
theorem theorem310SupercriticalRateCutoff_add_one_div_sq_le
    (dimension : ℕ) (hdimension : 2 < dimension)
    {eta radius : ℝ} (heta : 0 < eta)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1) :
    ((theorem310SupercriticalRateCutoff eta radius + 1 : ℕ) : ℝ) / radius ^ 2 ≤
      3 / radius ^ dimension := by
  let exponent : ℝ := 1 / (2 * (1 + eta))
  let remaining : ℕ := dimension - 2
  have hexponent_pos : 0 < exponent := by
    dsimp [exponent]
    positivity
  have hexponent_le_one : exponent ≤ 1 := by
    dsimp [exponent]
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * (1 + eta))).mpr
    linarith
  have hremaining : 1 ≤ remaining := by
    dsimp [remaining]
    omega
  have hexponent_le_remaining : exponent ≤ (remaining : ℝ) := by
    exact hexponent_le_one.trans (by exact_mod_cast hremaining)
  have hnegative : -((remaining : ℝ)) ≤ -exponent := neg_le_neg hexponent_le_remaining
  have hrpow_le : Real.rpow radius (-exponent) ≤
      Real.rpow radius (-((remaining : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_ge hradius hradius_le_one hnegative
  have hcutoff :=
    Probability.pOneFournierGuillinHeadCutoff_lt_two_mul_rpow_neg
      heta hradius hradius_le_one
  have hcutoff' : (theorem310SupercriticalRateCutoff eta radius : ℝ) <
      2 * Real.rpow radius (-((remaining : ℝ))) := by
    unfold theorem310SupercriticalRateCutoff
    exact hcutoff.trans_le (mul_le_mul_of_nonneg_left hrpow_le (by norm_num))
  have hinverse_eq : Real.rpow radius (-((remaining : ℝ))) =
      1 / radius ^ remaining := by
    calc
      Real.rpow radius (-((remaining : ℝ))) =
          (Real.rpow radius (remaining : ℝ))⁻¹ := Real.rpow_neg hradius.le _
      _ = (radius ^ remaining)⁻¹ := by
        congr 1
        exact Real.rpow_natCast radius remaining
      _ = 1 / radius ^ remaining := by rw [one_div]
  have hinverse_one : 1 ≤ 1 / radius ^ remaining := by
    simpa using (one_div_pow_le_one_div_pow_dimension hradius hradius_le_one
      (Nat.zero_le remaining))
  rw [hinverse_eq] at hcutoff'
  have hcutoff_add :
      ((theorem310SupercriticalRateCutoff eta radius + 1 : ℕ) : ℝ) ≤
        3 * (1 / radius ^ remaining) := by
    push_cast
    nlinarith
  have hradius_sq_pos : 0 < radius ^ 2 := pow_pos hradius _
  calc
    ((theorem310SupercriticalRateCutoff eta radius + 1 : ℕ) : ℝ) / radius ^ 2 ≤
        (3 * (1 / radius ^ remaining)) / radius ^ 2 :=
      div_le_div_of_nonneg_right hcutoff_add hradius_sq_pos.le
    _ = 3 / radius ^ dimension := by
      have hsplit : remaining + 2 = dimension := by
        dsimp [remaining]
        omega
      rw [← hsplit, pow_add]
      field_simp [hradius.ne']
      <;> ring

/-- An explicit parameter-only coefficient for the thirteen gates in the
supercritical concrete schedule.  It is independent of the target radius,
round, and failure probability. -/
noncomputable def theorem310SupercriticalSampleRateConstant
    (dimension : ℕ) (eta alpha gamma tailBound : ℝ) : ℝ :=
  let logCoefficient := theorem310RoundLogCoefficient
  let decay := Real.rpow 2 (-(1 + eta))
  let shellCoefficient := Probability.pOneFournierGuillinShellCoefficient eta
  let rateCoefficient :=
    Probability.selectedShellGeometricSupercriticalRateCoefficient dimension
  let tailMultiplier := Probability.selectedShellGeometricTailMultiplier tailBound
  let centralLogCoefficient := logCoefficient + Real.log 2
  let successorLogCoefficient := logCoefficient + 3 * Real.log 2
  1 + max
    (rateCoefficient ^ dimension * 6 ^ dimension)
    (max
      (6 ^ 2 * (2 * Real.sqrt dimension) ^ 2 * centralLogCoefficient)
      (max
        (6 * (2 * Real.sqrt dimension) *
          (16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * centralLogCoefficient))
        (max
          ((rateCoefficient * tailMultiplier) ^ dimension * 6 ^ dimension)
          (max
            (6 ^ 2 * (2 * Real.sqrt dimension * tailMultiplier) ^ 2 *
              successorLogCoefficient)
            (max
              (6 ^ 2 * (2 * Real.sqrt dimension * tailMultiplier) ^ 2 *
                (16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * successorLogCoefficient))
              (max
                (logCoefficient / (2 * (shellCoefficient / decay) ^ 2))
                (max
                  (logCoefficient / (shellCoefficient ^ 2 / (18 * tailBound)))
                  (max
                    (logCoefficient / (shellCoefficient * decay * Real.log 9 / 4))
                    (max
                      (logCoefficient / (shellCoefficient * gamma / 4))
                      (max
                        (1 / (shellCoefficient ^ 2 / (18 * tailBound)))
                        (max
                          (1 / (shellCoefficient * decay * Real.log 9 / 8))
                          (1 / ((shellCoefficient * gamma / 4) *
                            (Real.rpow 2 (alpha - 1 - eta) - 1))))))))))))))

theorem theorem310SupercriticalSampleRateConstant_pos
    (dimension : ℕ) (hdimension : 2 < dimension)
    {eta alpha gamma tailBound : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound) :
    0 < theorem310SupercriticalSampleRateConstant dimension eta alpha gamma tailBound := by
  let logCoefficient := theorem310RoundLogCoefficient
  let decay := Real.rpow 2 (-(1 + eta))
  let shellCoefficient := Probability.pOneFournierGuillinShellCoefficient eta
  let rateCoefficient :=
    Probability.selectedShellGeometricSupercriticalRateCoefficient dimension
  let tailMultiplier := Probability.selectedShellGeometricTailMultiplier tailBound
  let centralLogCoefficient := logCoefficient + Real.log 2
  let successorLogCoefficient := logCoefficient + 3 * Real.log 2
  have hlogCoefficient : 0 < logCoefficient := by
    dsimp [logCoefficient]
    exact theorem310RoundLogCoefficient_pos
  have hdecay : 0 < decay := by
    dsimp [decay]
    positivity
  have hshellCoefficient : 0 < shellCoefficient := by
    dsimp [shellCoefficient]
    exact Probability.pOneFournierGuillinShellCoefficient_pos heta
  have hrateCoefficient : 0 < rateCoefficient := by
    dsimp [rateCoefficient]
    exact Probability.selectedShellGeometricSupercriticalRateCoefficient_pos
      dimension hdimension
  have htailMultiplier : 0 < tailMultiplier := by
    dsimp [tailMultiplier, Probability.selectedShellGeometricTailMultiplier]
    positivity
  have hcentralLogCoefficient : 0 < centralLogCoefficient := by
    dsimp [centralLogCoefficient]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hsuccessorLogCoefficient : 0 < successorLogCoefficient := by
    dsimp [successorLogCoefficient]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hbase : 1 < Real.rpow 2 (alpha - 1 - eta) := by
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  unfold theorem310SupercriticalSampleRateConstant
  dsimp only
  positivity

theorem one_le_theorem310SupercriticalSampleRateConstant
    (dimension : ℕ) (hdimension : 2 < dimension)
    {eta alpha gamma tailBound : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound) :
    1 ≤ theorem310SupercriticalSampleRateConstant dimension eta alpha gamma tailBound := by
  let logCoefficient := theorem310RoundLogCoefficient
  let decay := Real.rpow 2 (-(1 + eta))
  let shellCoefficient := Probability.pOneFournierGuillinShellCoefficient eta
  let rateCoefficient :=
    Probability.selectedShellGeometricSupercriticalRateCoefficient dimension
  let tailMultiplier := Probability.selectedShellGeometricTailMultiplier tailBound
  let centralLogCoefficient := logCoefficient + Real.log 2
  let successorLogCoefficient := logCoefficient + 3 * Real.log 2
  have hrateCoefficient : 0 < rateCoefficient := by
    dsimp [rateCoefficient]
    exact Probability.selectedShellGeometricSupercriticalRateCoefficient_pos
      dimension hdimension
  unfold theorem310SupercriticalSampleRateConstant
  dsimp only
  apply le_add_of_nonneg_right
  exact (le_max_left _ _).trans' (by positivity)

set_option maxHeartbeats 1000000 in
/-- The real thirteen-gate requirement underlying the specialized concrete
count has the claimed supercritical rate.  The cap hypothesis is precisely
the honest small-radius regime in which the wrapper's capped deviation equals
the requested radius. -/
theorem theorem310SupercriticalAllShellRequirement_le_sampleRate
    (dimension : ℕ) (hdimension : 2 < dimension)
    {eta alpha gamma momentBound tailBound radius p : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1)
    (hp : 0 < p) (hp_le_one : p ≤ 1)
    (hcap : radius ≤ Probability.pOneFournierGuillinHeadGateRadius eta
      (Probability.pOneFournierGuillinUniformAllShellMassGateScale
        dimension eta alpha gamma momentBound))
    (round : ℕ) :
    Probability.pOneFournierGuillinSupercriticalAllShellEffectiveCountRequirement
      dimension (theorem310SupercriticalRateCutoff eta radius)
      eta alpha gamma tailBound
      (Probability.pOneFournierGuillinUniformCappedDeviation
        dimension eta alpha gamma momentBound radius)
      (Probability.pOneFournierGuillinUniformCappedScaledDeviation
        dimension eta alpha gamma momentBound radius)
      (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p round)
      radius (theorem310FailureBudget p round / 2) ≤
    theorem310SupercriticalSampleRateConstant dimension eta alpha gamma tailBound *
      (1 / radius ^ dimension) * theorem310ShiftedRoundLog p round := by
  let cutoff := theorem310SupercriticalRateCutoff eta radius
  let confidence := pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p round
  let tolerance := theorem310FailureBudget p round / 2
  let logCoefficient := theorem310RoundLogCoefficient
  let shifted := theorem310ShiftedRoundLog p round
  let inverseDimension := 1 / radius ^ dimension
  let decay := Real.rpow 2 (-(1 + eta))
  let shellCoefficient := Probability.pOneFournierGuillinShellCoefficient eta
  let rateCoefficient :=
    Probability.selectedShellGeometricSupercriticalRateCoefficient dimension
  let tailMultiplier := Probability.selectedShellGeometricTailMultiplier tailBound
  let centralLogCoefficient := logCoefficient + Real.log 2
  let successorLogCoefficient := logCoefficient + 3 * Real.log 2
  let constant :=
    theorem310SupercriticalSampleRateConstant dimension eta alpha gamma tailBound
  let coefficientOne := rateCoefficient ^ dimension * 6 ^ dimension
  let coefficientTwo :=
    6 ^ 2 * (2 * Real.sqrt dimension) ^ 2 * centralLogCoefficient
  let coefficientThree :=
    6 * (2 * Real.sqrt dimension) *
      (16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * centralLogCoefficient)
  let coefficientFour :=
    (rateCoefficient * tailMultiplier) ^ dimension * 6 ^ dimension
  let coefficientFive :=
    6 ^ 2 * (2 * Real.sqrt dimension * tailMultiplier) ^ 2 *
      successorLogCoefficient
  let coefficientSix :=
    6 ^ 2 * (2 * Real.sqrt dimension * tailMultiplier) ^ 2 *
      (16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * successorLogCoefficient)
  let coefficientSeven :=
    logCoefficient / (2 * (shellCoefficient / decay) ^ 2)
  let coefficientEight :=
    logCoefficient / (shellCoefficient ^ 2 / (18 * tailBound))
  let coefficientNine :=
    logCoefficient / (shellCoefficient * decay * Real.log 9 / 4)
  let coefficientTen := logCoefficient / (shellCoefficient * gamma / 4)
  let coefficientEleven := 1 / (shellCoefficient ^ 2 / (18 * tailBound))
  let coefficientTwelve := 1 / (shellCoefficient * decay * Real.log 9 / 8)
  let coefficientThirteen := 1 / ((shellCoefficient * gamma / 4) *
    (Real.rpow 2 (alpha - 1 - eta) - 1))
  let coefficientMax := max coefficientOne (max coefficientTwo
    (max coefficientThree (max coefficientFour (max coefficientFive
      (max coefficientSix (max coefficientSeven (max coefficientEight
        (max coefficientNine (max coefficientTen (max coefficientEleven
          (max coefficientTwelve coefficientThirteen)))))))))))
  have hlogCoefficient : 0 < logCoefficient := by
    dsimp [logCoefficient]
    exact theorem310RoundLogCoefficient_pos
  have hshifted_one : 1 ≤ shifted := by
    dsimp [shifted]
    exact theorem310ShiftedRoundLog_one_le hp hp_le_one round
  have hinverseDimension_one : 1 ≤ inverseDimension := by
    dsimp [inverseDimension]
    simpa using (one_div_pow_le_one_div_pow_dimension hradius hradius_le_one
      (Nat.zero_le dimension))
  have hdecay : 0 < decay := by
    dsimp [decay]
    positivity
  have hshellCoefficient : 0 < shellCoefficient := by
    dsimp [shellCoefficient]
    exact Probability.pOneFournierGuillinShellCoefficient_pos heta
  have hrateCoefficient : 0 < rateCoefficient := by
    dsimp [rateCoefficient]
    exact Probability.selectedShellGeometricSupercriticalRateCoefficient_pos
      dimension hdimension
  have htailMultiplier : 0 < tailMultiplier := by
    dsimp [tailMultiplier, Probability.selectedShellGeometricTailMultiplier]
    positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcentralLogCoefficient : 0 < centralLogCoefficient := by
    dsimp [centralLogCoefficient]
    positivity
  have hsuccessorLogCoefficient : 0 < successorLogCoefficient := by
    dsimp [successorLogCoefficient]
    positivity
  have hbase : 1 < Real.rpow 2 (alpha - 1 - eta) := by
    exact Real.one_lt_rpow (by norm_num) (by linarith)
  have hconstant : 0 < constant := by
    dsimp [constant]
    exact theorem310SupercriticalSampleRateConstant_pos dimension hdimension
      heta halphaGap hgamma htailBound
  have hconstant_eq : constant = 1 + coefficientMax := by
    rfl
  have hcoefficient_nonneg :
      0 ≤ coefficientOne ∧ 0 ≤ coefficientTwo ∧ 0 ≤ coefficientThree ∧
      0 ≤ coefficientFour ∧ 0 ≤ coefficientFive ∧ 0 ≤ coefficientSix ∧
      0 ≤ coefficientSeven ∧ 0 ≤ coefficientEight ∧ 0 ≤ coefficientNine ∧
      0 ≤ coefficientTen ∧ 0 ≤ coefficientEleven ∧ 0 ≤ coefficientTwelve ∧
      0 ≤ coefficientThirteen := by
    dsimp [coefficientOne, coefficientTwo, coefficientThree, coefficientFour,
      coefficientFive, coefficientSix, coefficientSeven, coefficientEight,
      coefficientNine, coefficientTen, coefficientEleven, coefficientTwelve,
      coefficientThirteen]
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    · apply one_div_nonneg.mpr
      exact mul_nonneg (div_nonneg (mul_nonneg hshellCoefficient.le hgamma.le) (by norm_num))
        (sub_nonneg.mpr hbase.le)
  have hcoefficient_le_max :
      coefficientOne ≤ coefficientMax ∧ coefficientTwo ≤ coefficientMax ∧
      coefficientThree ≤ coefficientMax ∧ coefficientFour ≤ coefficientMax ∧
      coefficientFive ≤ coefficientMax ∧ coefficientSix ≤ coefficientMax ∧
      coefficientSeven ≤ coefficientMax ∧ coefficientEight ≤ coefficientMax ∧
      coefficientNine ≤ coefficientMax ∧ coefficientTen ≤ coefficientMax ∧
      coefficientEleven ≤ coefficientMax ∧ coefficientTwelve ≤ coefficientMax ∧
      coefficientThirteen ≤ coefficientMax := by
    dsimp [coefficientMax]
    constructor
    · exact le_max_left _ _
    constructor
    · exact (le_max_left _ _).trans (le_max_right _ _)
    constructor
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    constructor
    · exact (((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)
    constructor
    · exact ((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
    constructor
    · exact (((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)
    constructor
    · exact ((((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
    constructor
    · exact (((((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)
    constructor
    · exact ((((((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
    constructor
    · exact (((((((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)
    constructor
    · exact ((((((((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
    constructor
    · exact (((((((((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)
    · exact (((((((((((le_max_right _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)
  have hcappedScaled :
      Probability.pOneFournierGuillinUniformCappedScaledDeviation
        dimension eta alpha gamma momentBound radius = radius := by
    unfold Probability.pOneFournierGuillinUniformCappedScaledDeviation
      Probability.pOneFournierGuillinCappedScaledDeviation
    rw [min_eq_left hcap]
  have hcappedRaw :
      Probability.pOneFournierGuillinUniformCappedDeviation
        dimension eta alpha gamma momentBound radius = radius / decay := by
    unfold Probability.pOneFournierGuillinUniformCappedDeviation
      Probability.pOneFournierGuillinCappedDeviation
      Probability.pOneFournierGuillinCappedScaledDeviation
    rw [min_eq_left hcap]
  obtain ⟨hconfidence, hlogEight, hlogSixteen, hlogFour, hlogFourTail⟩ :=
    theorem310_concrete_round_logs_le hp hp_le_one round
  change confidence ≤ logCoefficient * shifted at hconfidence
  change Real.log (8 / tolerance) ≤ logCoefficient * shifted at hlogEight
  change Real.log (16 / tolerance) ≤ logCoefficient * shifted at hlogSixteen
  change Real.log (4 / tolerance) ≤ logCoefficient * shifted at hlogFour
  change Real.log (4 / (tolerance * (1 - Real.exp (-1)))) ≤
    logCoefficient * shifted at hlogFourTail
  have hconfidence_nonneg : 0 ≤ confidence := by
    dsimp [confidence, pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule]
    exact Math.expConfidenceForHalfBudget_nonneg _
  have hinverseDimension_nonneg : 0 ≤ inverseDimension :=
    (zero_lt_one.trans_le hinverseDimension_one).le
  have hshifted_nonneg : 0 ≤ shifted := zero_le_one.trans hshifted_one
  have hlogScale_nonneg : 0 ≤ logCoefficient * shifted := by positivity
  have hinversePower : ∀ power : ℕ, power ≤ dimension →
      1 / radius ^ power ≤ inverseDimension := by
    intro power hpower
    dsimp [inverseDimension]
    exact one_div_pow_le_one_div_pow_dimension hradius hradius_le_one hpower
  have hscaledLog : ∀ {value : ℝ}, value ≤ logCoefficient * shifted →
      ∀ power : ℕ, power ≤ dimension →
        value / radius ^ power ≤ logCoefficient * inverseDimension * shifted := by
    intro value hvalue power hpower
    have hpower_pos : 0 < radius ^ power := pow_pos hradius _
    calc
      value / radius ^ power ≤ (logCoefficient * shifted) / radius ^ power :=
        div_le_div_of_nonneg_right hvalue hpower_pos.le
      _ = (logCoefficient * shifted) * (1 / radius ^ power) := by ring
      _ ≤ (logCoefficient * shifted) * inverseDimension :=
        mul_le_mul_of_nonneg_left (hinversePower power hpower) hlogScale_nonneg
      _ = logCoefficient * inverseDimension * shifted := by ring
  have hcentralScale :
      (confidence + Real.log 2) / radius ^ 2 ≤
        centralLogCoefficient * inverseDimension * shifted := by
    have hconf := hscaledLog hconfidence 2 (by omega)
    have htwo := hinversePower 2 (by omega)
    calc
      (confidence + Real.log 2) / radius ^ 2 =
          confidence / radius ^ 2 + Real.log 2 * (1 / radius ^ 2) := by ring
      _ ≤ logCoefficient * inverseDimension * shifted +
          Real.log 2 * inverseDimension :=
        add_le_add hconf (mul_le_mul_of_nonneg_left htwo hlogTwo.le)
      _ ≤ centralLogCoefficient * inverseDimension * shifted := by
        dsimp [centralLogCoefficient]
        have hlogTerm : Real.log 2 * inverseDimension ≤
            (Real.log 2 * inverseDimension) * shifted := by
          calc
            Real.log 2 * inverseDimension =
                (Real.log 2 * inverseDimension) * 1 := by ring
            _ ≤ (Real.log 2 * inverseDimension) * shifted :=
              mul_le_mul_of_nonneg_left hshifted_one
                (mul_nonneg hlogTwo.le hinverseDimension_nonneg)
        calc
          logCoefficient * inverseDimension * shifted + Real.log 2 * inverseDimension ≤
              logCoefficient * inverseDimension * shifted +
                (Real.log 2 * inverseDimension) * shifted := by
            exact add_le_add le_rfl hlogTerm
          _ = (logCoefficient + Real.log 2) * inverseDimension * shifted := by ring
  have hcutoffScale : ((cutoff + 1 : ℕ) : ℝ) / radius ^ 2 ≤
      3 * inverseDimension := by
    dsimp [cutoff, inverseDimension]
    simpa [div_eq_mul_inv] using
      (theorem310SupercriticalRateCutoff_add_one_div_sq_le
        dimension hdimension heta hradius hradius_le_one)
  have hsuccessorScale :
      (confidence + (cutoff + 1 : ℝ) * Real.log 2) / radius ^ 2 ≤
        successorLogCoefficient * inverseDimension * shifted := by
    have hconf := hscaledLog hconfidence 2 (by omega)
    calc
      (confidence + (cutoff + 1 : ℝ) * Real.log 2) / radius ^ 2 =
          confidence / radius ^ 2 +
            (((cutoff + 1 : ℕ) : ℝ) / radius ^ 2) * Real.log 2 := by
        push_cast
        ring
      _ ≤ logCoefficient * inverseDimension * shifted +
          (3 * inverseDimension) * Real.log 2 :=
        add_le_add hconf (mul_le_mul_of_nonneg_right hcutoffScale hlogTwo.le)
      _ ≤ successorLogCoefficient * inverseDimension * shifted := by
        dsimp [successorLogCoefficient]
        have hlogTerm : (3 * inverseDimension) * Real.log 2 ≤
            ((3 * inverseDimension) * Real.log 2) * shifted := by
          calc
            (3 * inverseDimension) * Real.log 2 =
                ((3 * inverseDimension) * Real.log 2) * 1 := by ring
            _ ≤ ((3 * inverseDimension) * Real.log 2) * shifted :=
              mul_le_mul_of_nonneg_left hshifted_one (by positivity)
        calc
          logCoefficient * inverseDimension * shifted +
              (3 * inverseDimension) * Real.log 2 ≤
            logCoefficient * inverseDimension * shifted +
              ((3 * inverseDimension) * Real.log 2) * shifted := by
                exact add_le_add le_rfl hlogTerm
          _ = (logCoefficient + 3 * Real.log 2) * inverseDimension * shifted := by ring
  have hcentralAffineScale :
      (16 * ((2 ^ dimension : ℕ) : ℝ) +
        8 * (confidence + Real.log 2)) / radius ≤
      (16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * centralLogCoefficient) *
        inverseDimension * shifted := by
    have hconfOne := hscaledLog hconfidence 1 (by omega)
    have hinvOne := hinversePower 1 (by omega)
    have hconfOne' : confidence / radius ≤
        logCoefficient * inverseDimension * shifted := by simpa using hconfOne
    have hinvOne' : 1 / radius ≤ inverseDimension := by simpa using hinvOne
    have hpow_nonneg : 0 ≤ ((2 ^ dimension : ℕ) : ℝ) := by positivity
    calc
      (16 * ((2 ^ dimension : ℕ) : ℝ) +
          8 * (confidence + Real.log 2)) / radius =
          16 * ((2 ^ dimension : ℕ) : ℝ) * (1 / radius) +
            8 * (confidence / radius + Real.log 2 * (1 / radius)) := by ring
      _ ≤ 16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension +
          8 * (logCoefficient * inverseDimension * shifted +
            Real.log 2 * inverseDimension) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hinvOne' (by positivity)
        · apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact add_le_add hconfOne'
            (mul_le_mul_of_nonneg_left hinvOne' hlogTwo.le)
      _ ≤ (16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * centralLogCoefficient) *
          inverseDimension * shifted := by
        dsimp [centralLogCoefficient]
        have hconstantTerm :
            16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension ≤
              (16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension) * shifted := by
          calc
            16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension =
                (16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension) * 1 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hshifted_one (by positivity)
        have hlogTerm : 8 * (Real.log 2 * inverseDimension) ≤
            (8 * (Real.log 2 * inverseDimension)) * shifted := by
          calc
            8 * (Real.log 2 * inverseDimension) =
                (8 * (Real.log 2 * inverseDimension)) * 1 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hshifted_one (by positivity)
        calc
          16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension +
              8 * (logCoefficient * inverseDimension * shifted +
                Real.log 2 * inverseDimension) ≤
            (16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension) * shifted +
              8 * (logCoefficient * inverseDimension * shifted) +
              (8 * (Real.log 2 * inverseDimension)) * shifted := by
                nlinarith
          _ = (16 * ((2 ^ dimension : ℕ) : ℝ) +
              8 * (logCoefficient + Real.log 2)) * inverseDimension * shifted := by ring
  have hsuccessorAffineScale :
      (16 * ((2 ^ dimension : ℕ) : ℝ) +
        8 * (confidence + (cutoff + 1 : ℝ) * Real.log 2)) / radius ^ 2 ≤
      (16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * successorLogCoefficient) *
        inverseDimension * shifted := by
    have hinvTwo := hinversePower 2 (by omega)
    have hpow_nonneg : 0 ≤ ((2 ^ dimension : ℕ) : ℝ) := by positivity
    calc
      (16 * ((2 ^ dimension : ℕ) : ℝ) +
          8 * (confidence + (cutoff + 1 : ℝ) * Real.log 2)) / radius ^ 2 =
          16 * ((2 ^ dimension : ℕ) : ℝ) * (1 / radius ^ 2) +
            8 * ((confidence + (cutoff + 1 : ℝ) * Real.log 2) / radius ^ 2) := by
        ring
      _ ≤ 16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension +
          8 * (successorLogCoefficient * inverseDimension * shifted) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hinvTwo (by positivity))
          (mul_le_mul_of_nonneg_left hsuccessorScale (by norm_num))
      _ ≤ (16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * successorLogCoefficient) *
          inverseDimension * shifted := by
        have hconstantTerm :
            16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension ≤
              (16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension) * shifted := by
          calc
            16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension =
                (16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension) * 1 := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hshifted_one (by positivity)
        calc
          16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension +
              8 * (successorLogCoefficient * inverseDimension * shifted) ≤
            (16 * ((2 ^ dimension : ℕ) : ℝ) * inverseDimension) * shifted +
              8 * (successorLogCoefficient * inverseDimension * shifted) :=
                add_le_add hconstantTerm le_rfl
          _ = (16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * successorLogCoefficient) *
              inverseDimension * shifted := by ring
  obtain ⟨hcoefficientOne_nonneg, hcoefficientTwo_nonneg, hcoefficientThree_nonneg,
    hcoefficientFour_nonneg, hcoefficientFive_nonneg, hcoefficientSix_nonneg,
    hcoefficientSeven_nonneg, hcoefficientEight_nonneg, hcoefficientNine_nonneg,
    hcoefficientTen_nonneg, hcoefficientEleven_nonneg, hcoefficientTwelve_nonneg,
    hcoefficientThirteen_nonneg⟩ := hcoefficient_nonneg
  obtain ⟨hcoefficientOne_le, hcoefficientTwo_le, hcoefficientThree_le,
    hcoefficientFour_le, hcoefficientFive_le, hcoefficientSix_le,
    hcoefficientSeven_le, hcoefficientEight_le, hcoefficientNine_le,
    hcoefficientTen_le, hcoefficientEleven_le, hcoefficientTwelve_le,
    hcoefficientThirteen_le⟩ := hcoefficient_le_max
  have hcoefficientMax_le_constant : coefficientMax ≤ constant := by
    rw [hconstant_eq]
    linarith
  have hcoefficientRate : ∀ {coefficient : ℝ}, 0 ≤ coefficient →
      coefficient ≤ coefficientMax →
      coefficient * inverseDimension ≤ constant * inverseDimension * shifted := by
    intro coefficient hcoefficient_nonneg hcoefficient_le
    calc
      coefficient * inverseDimension ≤ constant * inverseDimension :=
        mul_le_mul_of_nonneg_right
          (hcoefficient_le.trans hcoefficientMax_le_constant) hinverseDimension_nonneg
      _ ≤ constant * inverseDimension * shifted := by
        nlinarith [mul_nonneg hconstant.le hinverseDimension_nonneg,
          sub_nonneg.mpr hshifted_one]
  have hcoefficientRateShifted : ∀ {coefficient : ℝ}, 0 ≤ coefficient →
      coefficient ≤ coefficientMax →
      coefficient * inverseDimension * shifted ≤
        constant * inverseDimension * shifted := by
    intro coefficient hcoefficient_nonneg hcoefficient_le
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (hcoefficient_le.trans hcoefficientMax_le_constant)
        hinverseDimension_nonneg) hshifted_nonneg
  have hheadOne :
      rateCoefficient ^ dimension / (radius / 6) ^ dimension ≤
        constant * inverseDimension * shifted := by
    calc
      rateCoefficient ^ dimension / (radius / 6) ^ dimension =
          coefficientOne * inverseDimension := by
        dsimp [coefficientOne, inverseDimension]
        rw [div_pow]
        field_simp [hradius.ne']
        <;> ring
      _ ≤ constant * inverseDimension * shifted :=
        hcoefficientRate hcoefficientOne_nonneg hcoefficientOne_le
  have hcentralArgument_nonneg : 0 ≤ confidence + Real.log 2 :=
    add_nonneg hconfidence_nonneg hlogTwo.le
  have hheadTwo :
      6 ^ 2 *
        (2 * Real.sqrt dimension * Real.sqrt (confidence + Real.log 2)) ^ 2 /
          radius ^ 2 ≤ constant * inverseDimension * shifted := by
    calc
      6 ^ 2 *
          (2 * Real.sqrt dimension * Real.sqrt (confidence + Real.log 2)) ^ 2 /
            radius ^ 2 =
          (6 ^ 2 * (2 * Real.sqrt dimension) ^ 2) *
            ((confidence + Real.log 2) / radius ^ 2) := by
        simp only [mul_pow]
        rw [Real.sq_sqrt hcentralArgument_nonneg]
        ring
      _ ≤ (6 ^ 2 * (2 * Real.sqrt dimension) ^ 2) *
          (centralLogCoefficient * inverseDimension * shifted) :=
        mul_le_mul_of_nonneg_left hcentralScale (by positivity)
      _ = coefficientTwo * inverseDimension * shifted := by
        dsimp [coefficientTwo]
        ring
      _ ≤ constant * inverseDimension * shifted :=
        hcoefficientRateShifted hcoefficientTwo_nonneg hcoefficientTwo_le
  have hheadThree :
      6 * (2 * Real.sqrt dimension *
        (16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * (confidence + Real.log 2))) /
          radius ≤ constant * inverseDimension * shifted := by
    calc
      6 * (2 * Real.sqrt dimension *
          (16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * (confidence + Real.log 2))) /
            radius =
          (6 * (2 * Real.sqrt dimension)) *
            ((16 * ((2 ^ dimension : ℕ) : ℝ) +
              8 * (confidence + Real.log 2)) / radius) := by ring
      _ ≤ (6 * (2 * Real.sqrt dimension)) *
          ((16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * centralLogCoefficient) *
            inverseDimension * shifted) :=
        mul_le_mul_of_nonneg_left hcentralAffineScale (by positivity)
      _ = coefficientThree * inverseDimension * shifted := by
        dsimp [coefficientThree]
        ring
      _ ≤ constant * inverseDimension * shifted :=
        hcoefficientRateShifted hcoefficientThree_nonneg hcoefficientThree_le
  have hheadFour :
      (rateCoefficient * tailMultiplier) ^ dimension / (radius / 6) ^ dimension ≤
        constant * inverseDimension * shifted := by
    calc
      (rateCoefficient * tailMultiplier) ^ dimension / (radius / 6) ^ dimension =
          coefficientFour * inverseDimension := by
        dsimp [coefficientFour, inverseDimension]
        rw [div_pow]
        field_simp [hradius.ne']
        <;> ring
      _ ≤ constant * inverseDimension * shifted :=
        hcoefficientRate hcoefficientFour_nonneg hcoefficientFour_le
  have hsuccessorArgument_nonneg :
      0 ≤ confidence + (cutoff + 1 : ℝ) * Real.log 2 := by positivity
  have hheadFive :
      6 ^ 2 *
        (2 * Real.sqrt dimension *
          Real.sqrt (confidence + (cutoff + 1 : ℝ) * Real.log 2) *
          tailMultiplier) ^ 2 / radius ^ 2 ≤
        constant * inverseDimension * shifted := by
    calc
      6 ^ 2 *
          (2 * Real.sqrt dimension *
            Real.sqrt (confidence + (cutoff + 1 : ℝ) * Real.log 2) *
            tailMultiplier) ^ 2 / radius ^ 2 =
          (6 ^ 2 * (2 * Real.sqrt dimension * tailMultiplier) ^ 2) *
            ((confidence + (cutoff + 1 : ℝ) * Real.log 2) / radius ^ 2) := by
        simp only [mul_pow]
        rw [Real.sq_sqrt hsuccessorArgument_nonneg]
        ring
      _ ≤ (6 ^ 2 * (2 * Real.sqrt dimension * tailMultiplier) ^ 2) *
          (successorLogCoefficient * inverseDimension * shifted) :=
        mul_le_mul_of_nonneg_left hsuccessorScale (by positivity)
      _ = coefficientFive * inverseDimension * shifted := by
        dsimp [coefficientFive]
        ring
      _ ≤ constant * inverseDimension * shifted :=
        hcoefficientRateShifted hcoefficientFive_nonneg hcoefficientFive_le
  have hsuccessorAffine_nonneg :
      0 ≤ 16 * ((2 ^ dimension : ℕ) : ℝ) +
        8 * (confidence + (cutoff + 1 : ℝ) * Real.log 2) := by positivity
  have hheadSix :
      6 ^ 2 *
        (2 * Real.sqrt dimension *
          Real.sqrt (16 * ((2 ^ dimension : ℕ) : ℝ) +
            8 * (confidence + (cutoff + 1 : ℝ) * Real.log 2)) *
          tailMultiplier) ^ 2 / radius ^ 2 ≤
        constant * inverseDimension * shifted := by
    calc
      6 ^ 2 *
          (2 * Real.sqrt dimension *
            Real.sqrt (16 * ((2 ^ dimension : ℕ) : ℝ) +
              8 * (confidence + (cutoff + 1 : ℝ) * Real.log 2)) *
            tailMultiplier) ^ 2 / radius ^ 2 =
          (6 ^ 2 * (2 * Real.sqrt dimension * tailMultiplier) ^ 2) *
            ((16 * ((2 ^ dimension : ℕ) : ℝ) +
              8 * (confidence + (cutoff + 1 : ℝ) * Real.log 2)) / radius ^ 2) := by
        simp only [mul_pow]
        rw [Real.sq_sqrt hsuccessorAffine_nonneg]
        ring
      _ ≤ (6 ^ 2 * (2 * Real.sqrt dimension * tailMultiplier) ^ 2) *
          ((16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * successorLogCoefficient) *
            inverseDimension * shifted) :=
        mul_le_mul_of_nonneg_left hsuccessorAffineScale (by positivity)
      _ = coefficientSix * inverseDimension * shifted := by
        dsimp [coefficientSix]
        ring
      _ ≤ constant * inverseDimension * shifted :=
        hcoefficientRateShifted hcoefficientSix_nonneg hcoefficientSix_le
  have hlogEightScale := hscaledLog hlogEight 2 (by omega)
  have hlogSixteenScale := hscaledLog hlogSixteen 2 (by omega)
  have hlogFourScale := hscaledLog hlogFour 2 (by omega)
  have hlogFourTailScale := hscaledLog hlogFourTail 2 (by omega)
  have hmassSeven :
      Real.log (8 / tolerance) /
          (2 * (shellCoefficient * (radius / decay)) ^ 2) ≤
        constant * inverseDimension * shifted := by
    have hfixed : 0 ≤ 1 / (2 * (shellCoefficient / decay) ^ 2) := by positivity
    calc
      Real.log (8 / tolerance) /
          (2 * (shellCoefficient * (radius / decay)) ^ 2) =
        (1 / (2 * (shellCoefficient / decay) ^ 2)) *
          (Real.log (8 / tolerance) / radius ^ 2) := by
            field_simp [hradius.ne', hdecay.ne', hshellCoefficient.ne']
            <;> ring
      _ ≤ (1 / (2 * (shellCoefficient / decay) ^ 2)) *
          (logCoefficient * inverseDimension * shifted) :=
        mul_le_mul_of_nonneg_left hlogEightScale hfixed
      _ = coefficientSeven * inverseDimension * shifted := by
        dsimp [coefficientSeven]
        ring
      _ ≤ constant * inverseDimension * shifted :=
        hcoefficientRateShifted hcoefficientSeven_nonneg hcoefficientSeven_le
  have hmassEight :
      Real.log (16 / tolerance) /
          (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)) ≤
        constant * inverseDimension * shifted := by
    have hfixed : 0 ≤ 1 / (shellCoefficient ^ 2 / (18 * tailBound)) := by positivity
    calc
      Real.log (16 / tolerance) /
          (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)) =
        (1 / (shellCoefficient ^ 2 / (18 * tailBound))) *
          (Real.log (16 / tolerance) / radius ^ 2) := by
            field_simp [hradius.ne', hshellCoefficient.ne', htailBound.ne']
            <;> ring
      _ ≤ (1 / (shellCoefficient ^ 2 / (18 * tailBound))) *
          (logCoefficient * inverseDimension * shifted) :=
        mul_le_mul_of_nonneg_left hlogSixteenScale hfixed
      _ = coefficientEight * inverseDimension * shifted := by
        dsimp [coefficientEight]
        ring
      _ ≤ constant * inverseDimension * shifted :=
        hcoefficientRateShifted hcoefficientEight_nonneg hcoefficientEight_le
  have hmassNine :
      Real.log (4 / tolerance) /
          (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 4) ≤
        constant * inverseDimension * shifted := by
    have hlogNine : 0 < Real.log 9 := Real.log_pos (by norm_num)
    have hfixed : 0 ≤ 1 / (shellCoefficient * decay * Real.log 9 / 4) := by positivity
    calc
      Real.log (4 / tolerance) /
          (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 4) =
        (1 / (shellCoefficient * decay * Real.log 9 / 4)) *
          (Real.log (4 / tolerance) / radius ^ 2) := by
            field_simp [hradius.ne', hshellCoefficient.ne', hdecay.ne', hlogNine.ne']
            <;> ring
      _ ≤ (1 / (shellCoefficient * decay * Real.log 9 / 4)) *
          (logCoefficient * inverseDimension * shifted) :=
        mul_le_mul_of_nonneg_left hlogFourScale hfixed
      _ = coefficientNine * inverseDimension * shifted := by
        dsimp [coefficientNine]
        ring
      _ ≤ constant * inverseDimension * shifted :=
        hcoefficientRateShifted hcoefficientNine_nonneg hcoefficientNine_le
  have hmassTen :
      Real.log (4 / (tolerance * (1 - Real.exp (-1)))) /
          (shellCoefficient * radius ^ 2 * gamma / 4) ≤
        constant * inverseDimension * shifted := by
    have hfixed : 0 ≤ 1 / (shellCoefficient * gamma / 4) := by positivity
    calc
      Real.log (4 / (tolerance * (1 - Real.exp (-1)))) /
          (shellCoefficient * radius ^ 2 * gamma / 4) =
        (1 / (shellCoefficient * gamma / 4)) *
          (Real.log (4 / (tolerance * (1 - Real.exp (-1)))) / radius ^ 2) := by
            field_simp [hradius.ne', hshellCoefficient.ne', hgamma.ne']
            <;> ring
      _ ≤ (1 / (shellCoefficient * gamma / 4)) *
          (logCoefficient * inverseDimension * shifted) :=
        mul_le_mul_of_nonneg_left hlogFourTailScale hfixed
      _ = coefficientTen * inverseDimension * shifted := by
        dsimp [coefficientTen]
        ring
      _ ≤ constant * inverseDimension * shifted :=
        hcoefficientRateShifted hcoefficientTen_nonneg hcoefficientTen_le
  have hinverseTwo := hinversePower 2 (by omega)
  have hsquareEleven :
      1 / (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)) ≤
        constant * inverseDimension * shifted := by
    calc
      1 / (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)) =
          coefficientEleven * (1 / radius ^ 2) := by
            dsimp [coefficientEleven]
            field_simp [hradius.ne', hshellCoefficient.ne', htailBound.ne']
            <;> ring
      _ ≤ coefficientEleven * inverseDimension :=
        mul_le_mul_of_nonneg_left hinverseTwo hcoefficientEleven_nonneg
      _ ≤ constant * inverseDimension * shifted :=
        hcoefficientRate hcoefficientEleven_nonneg hcoefficientEleven_le
  have hsquareTwelve :
      1 / (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 8) ≤
        constant * inverseDimension * shifted := by
    have hlogNine : 0 < Real.log 9 := Real.log_pos (by norm_num)
    calc
      1 / (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 8) =
          coefficientTwelve * (1 / radius ^ 2) := by
            dsimp [coefficientTwelve]
            field_simp [hradius.ne', hshellCoefficient.ne', hdecay.ne', hlogNine.ne']
            <;> ring
      _ ≤ coefficientTwelve * inverseDimension :=
        mul_le_mul_of_nonneg_left hinverseTwo hcoefficientTwelve_nonneg
      _ ≤ constant * inverseDimension * shifted :=
        hcoefficientRate hcoefficientTwelve_nonneg hcoefficientTwelve_le
  have hsquareThirteen :
      1 / ((shellCoefficient * radius ^ 2 * gamma / 4) *
        (Real.rpow 2 (alpha - 1 - eta) - 1)) ≤
        constant * inverseDimension * shifted := by
    have hbase_sub : 0 < Real.rpow 2 (alpha - 1 - eta) - 1 := sub_pos.mpr hbase
    calc
      1 / ((shellCoefficient * radius ^ 2 * gamma / 4) *
          (Real.rpow 2 (alpha - 1 - eta) - 1)) =
        coefficientThirteen * (1 / radius ^ 2) := by
          dsimp [coefficientThirteen]
          field_simp [hradius.ne', hshellCoefficient.ne', hgamma.ne', hbase_sub.ne']
          <;> ring
      _ ≤ coefficientThirteen * inverseDimension :=
        mul_le_mul_of_nonneg_left hinverseTwo hcoefficientThirteen_nonneg
      _ ≤ constant * inverseDimension * shifted :=
        hcoefficientRate hcoefficientThirteen_nonneg hcoefficientThirteen_le
  have hheadRequirement :
      Probability.selectedShellGeometricSupercriticalEffectiveCountRequirement
        dimension cutoff confidence tailBound radius ≤
          constant * inverseDimension * shifted := by
    unfold Probability.selectedShellGeometricSupercriticalEffectiveCountRequirement
    change max
      (rateCoefficient ^ dimension / (radius / 6) ^ dimension)
      (max
        (6 ^ 2 * (2 * Real.sqrt dimension * Real.sqrt (confidence + Real.log 2)) ^ 2 /
          radius ^ 2)
        (max
          (6 * (2 * Real.sqrt dimension *
            (16 * ((2 ^ dimension : ℕ) : ℝ) + 8 * (confidence + Real.log 2))) / radius)
          (max
            ((rateCoefficient * tailMultiplier) ^ dimension /
              (radius / 6) ^ dimension)
            (max
              (6 ^ 2 * (2 * Real.sqrt dimension *
                Real.sqrt (confidence + (cutoff + 1 : ℝ) * Real.log 2) *
                tailMultiplier) ^ 2 / radius ^ 2)
              (6 ^ 2 * (2 * Real.sqrt dimension * Real.sqrt
                (16 * ((2 ^ dimension : ℕ) : ℝ) +
                  8 * (confidence + (cutoff + 1 : ℝ) * Real.log 2)) *
                tailMultiplier) ^ 2 / radius ^ 2))))) ≤
        constant * inverseDimension * shifted
    exact max_le hheadOne (max_le hheadTwo (max_le hheadThree
      (max_le hheadFour (max_le hheadFive hheadSix))))
  have hmassRequirement :
      Probability.pOneFournierGuillinUniformAllShellMassEffectiveCountRequirement
        eta (radius / decay) radius gamma tailBound tolerance ≤
          constant * inverseDimension * shifted := by
    unfold Probability.pOneFournierGuillinUniformAllShellMassEffectiveCountRequirement
      Probability.pOneFournierGuillinShellWeight
    simp only [Nat.cast_zero, mul_zero, neg_zero]
    have hrpowZero : Real.rpow (2 : ℝ) 0 = 1 := by
      rw [Real.rpow_eq_pow, Real.rpow_zero]
    rw [hrpowZero, mul_one]
    change max
      (Real.log (8 / tolerance) /
        (2 * (shellCoefficient * (radius / decay)) ^ 2))
      (max
        (Real.log (16 / tolerance) /
          (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)))
        (max
          (Real.log (4 / tolerance) /
            (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 4))
          (Real.log (4 / (tolerance * (1 - Real.exp (-1)))) /
            (shellCoefficient * radius ^ 2 * gamma / 4)))) ≤
      constant * inverseDimension * shifted
    exact max_le hmassSeven (max_le hmassEight (max_le hmassNine hmassTen))
  have hsquareRequirement :
      Probability.pOneFournierGuillinUniformSquareRateEffectiveCountRequirement
        eta alpha gamma tailBound radius ≤ constant * inverseDimension * shifted := by
    unfold Probability.pOneFournierGuillinUniformSquareRateEffectiveCountRequirement
    change max
      (1 / (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)))
      (max
        (1 / (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 8))
        (1 / ((shellCoefficient * radius ^ 2 * gamma / 4) *
          (Real.rpow 2 (alpha - 1 - eta) - 1)))) ≤
      constant * inverseDimension * shifted
    exact max_le hsquareEleven (max_le hsquareTwelve hsquareThirteen)
  rw [hcappedRaw, hcappedScaled]
  change max
    (Probability.selectedShellGeometricSupercriticalEffectiveCountRequirement
      dimension cutoff confidence tailBound radius)
    (max
      (Probability.pOneFournierGuillinUniformAllShellMassEffectiveCountRequirement
        eta (radius / decay) radius gamma tailBound tolerance)
      (Probability.pOneFournierGuillinUniformSquareRateEffectiveCountRequirement
        eta alpha gamma tailBound radius)) ≤ constant * inverseDimension * shifted
  exact max_le hheadRequirement (max_le hmassRequirement hsquareRequirement)

/-- The actual natural-valued capped schedule is at most a parameter-only
constant times `r⁻ᵈ` and the shifted round logarithm. -/
theorem theorem310SupercriticalRateCountSchedule_le
    (dimension : ℕ) (hdimension : 2 < dimension)
    {eta alpha gamma momentBound tailBound radius p : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1)
    (hp : 0 < p) (hp_le_one : p ≤ 1)
    (hcap : radius ≤ Probability.pOneFournierGuillinHeadGateRadius eta
      (Probability.pOneFournierGuillinUniformAllShellMassGateScale
        dimension eta alpha gamma momentBound))
    (round : ℕ) :
    (theorem310SupercriticalRateCountSchedule dimension eta alpha gamma momentBound
      tailBound radius p round : ℝ) ≤
      2 * theorem310SupercriticalSampleRateConstant dimension eta alpha gamma tailBound *
        (1 / radius ^ dimension) * theorem310ShiftedRoundLog p round := by
  let requirement :=
    Probability.pOneFournierGuillinSupercriticalAllShellEffectiveCountRequirement
      dimension (theorem310SupercriticalRateCutoff eta radius)
      eta alpha gamma tailBound
      (Probability.pOneFournierGuillinUniformCappedDeviation
        dimension eta alpha gamma momentBound radius)
      (Probability.pOneFournierGuillinUniformCappedScaledDeviation
        dimension eta alpha gamma momentBound radius)
      (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p round)
      radius (theorem310FailureBudget p round / 2)
  let envelope :=
    theorem310SupercriticalSampleRateConstant dimension eta alpha gamma tailBound *
      (1 / radius ^ dimension) * theorem310ShiftedRoundLog p round
  have hrequirement : requirement ≤ envelope := by
    dsimp [requirement, envelope]
    exact theorem310SupercriticalAllShellRequirement_le_sampleRate dimension hdimension
      heta halphaGap hgamma htailBound hradius hradius_le_one hp hp_le_one hcap round
  have hinverse_one : 1 ≤ 1 / radius ^ dimension := by
    simpa using (one_div_pow_le_one_div_pow_dimension hradius hradius_le_one
      (Nat.zero_le dimension))
  have hshifted_one := theorem310ShiftedRoundLog_one_le hp hp_le_one round
  have hconstant_one := one_le_theorem310SupercriticalSampleRateConstant
    dimension hdimension heta halphaGap hgamma htailBound
  have henvelope_one : 1 ≤ envelope := by
    dsimp [envelope]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hconstant_one hinverse_one) hshifted_one
  have hmax : max 1 requirement ≤ envelope := max_le henvelope_one hrequirement
  have hceil : (Math.positiveNatCeil requirement : ℝ) < max 1 requirement + 1 := by
    unfold Math.positiveNatCeil
    exact Nat.ceil_lt_add_one (zero_le_one.trans (le_max_left _ _))
  have hcount_lt : (Math.positiveNatCeil requirement : ℝ) < 2 * envelope := by
    calc
      (Math.positiveNatCeil requirement : ℝ) < max 1 requirement + 1 := hceil
      _ ≤ envelope + 1 := add_le_add hmax le_rfl
      _ ≤ 2 * envelope := by linarith
  unfold theorem310SupercriticalRateCountSchedule
    pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
    Probability.pOneFournierGuillinSupercriticalCappedAllShellConcreteCountSchedule
    Probability.pOneFournierGuillinSupercriticalAllShellEffectiveCount
  simpa only [requirement, envelope,
    pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule, mul_assoc] using
      hcount_lt.le

/-- Literal source logarithm on a range where it is at least one.  The extra
`p ≤ exp (-1)` hypothesis is only an endpoint normalization: without it the
literal right-hand side vanishes at the first round when `p = 1`. -/
theorem theorem310SupercriticalRateCountSchedule_le_literal_log
    (dimension : ℕ) (hdimension : 2 < dimension)
    {eta alpha gamma momentBound tailBound radius p : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1)
    (hp : 0 < p) (hp_le_exp_neg_one : p ≤ Real.exp (-1))
    (hcap : radius ≤ Probability.pOneFournierGuillinHeadGateRadius eta
      (Probability.pOneFournierGuillinUniformAllShellMassGateScale
        dimension eta alpha gamma momentBound))
    (round : ℕ) :
    (theorem310SupercriticalRateCountSchedule dimension eta alpha gamma momentBound
      tailBound radius p round : ℝ) ≤
      4 * theorem310SupercriticalSampleRateConstant dimension eta alpha gamma tailBound *
        (1 / radius ^ dimension) *
          Real.log (((round + 1 : ℕ) : ℝ) / p) := by
  have hexp_neg_one_lt_one : Real.exp (-1) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  have hp_le_one : p ≤ 1 := hp_le_exp_neg_one.trans hexp_neg_one_lt_one.le
  have hbase := theorem310SupercriticalRateCountSchedule_le dimension hdimension
    heta halphaGap hgamma htailBound hradius hradius_le_one hp hp_le_one hcap round
  have htime : (1 : ℝ) ≤ ((round + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega : round + 1 ≠ 0)
  have hratio_exp : Real.exp 1 ≤ ((round + 1 : ℕ) : ℝ) / p := by
    apply (le_div_iff₀ hp).mpr
    have hpexp : p * Real.exp 1 ≤ 1 := by
      calc
        p * Real.exp 1 ≤ Real.exp (-1) * Real.exp 1 :=
          mul_le_mul_of_nonneg_right hp_le_exp_neg_one (Real.exp_pos 1).le
        _ = 1 := by rw [← Real.exp_add]; norm_num
    simpa [mul_comm] using hpexp.trans htime
  have hlog_one : 1 ≤ Real.log (((round + 1 : ℕ) : ℝ) / p) := by
    have hlog := Real.log_le_log (Real.exp_pos 1) hratio_exp
    simpa using hlog
  have hshifted : theorem310ShiftedRoundLog p round ≤
      2 * Real.log (((round + 1 : ℕ) : ℝ) / p) := by
    unfold theorem310ShiftedRoundLog
    linarith
  calc
    (theorem310SupercriticalRateCountSchedule dimension eta alpha gamma momentBound
        tailBound radius p round : ℝ) ≤
      2 * theorem310SupercriticalSampleRateConstant dimension eta alpha gamma tailBound *
        (1 / radius ^ dimension) * theorem310ShiftedRoundLog p round := hbase
    _ ≤ 2 * theorem310SupercriticalSampleRateConstant dimension eta alpha gamma tailBound *
        (1 / radius ^ dimension) *
          (2 * Real.log (((round + 1 : ℕ) : ℝ) / p)) := by
      exact mul_le_mul_of_nonneg_left hshifted
        (mul_nonneg
          (mul_nonneg (by positivity)
            (theorem310SupercriticalSampleRateConstant_pos dimension hdimension
              heta halphaGap hgamma htailBound).le) (by positivity))
    _ = 4 * theorem310SupercriticalSampleRateConstant dimension eta alpha gamma tailBound *
        (1 / radius ^ dimension) *
          Real.log (((round + 1 : ℕ) : ℝ) / p) := by ring

/-- The radius used by the unrestricted source-facing schedule.  Capping is
now part of the selector, rather than a premise on the requested radius. -/
noncomputable def theorem310SupercriticalEffectiveRadius
    (dimension : ℕ) (eta alpha gamma momentBound radius : ℝ) : ℝ :=
  min radius (Probability.pOneFournierGuillinHeadGateRadius eta
    (Probability.pOneFournierGuillinUniformAllShellMassGateScale
      dimension eta alpha gamma momentBound))

/-- The actual concrete schedule at the capped effective radius.  Its
certificate is at least as accurate as one requested at the original radius. -/
noncomputable def theorem310SupercriticalUniformRateCountSchedule
    (dimension : ℕ) (eta alpha gamma momentBound tailBound radius p : ℝ) : ℕ → ℕ :=
  theorem310SupercriticalRateCountSchedule dimension eta alpha gamma momentBound tailBound
    (theorem310SupercriticalEffectiveRadius dimension eta alpha gamma momentBound radius) p

/-- The cap loses only a parameter-dependent constant factor on `(0,1]`.
This removes the small-radius condition from the final sample-rate wrapper. -/
theorem min_one_gate_mul_radius_le_effectiveRadius
    (dimension : ℕ) (eta alpha gamma momentBound : ℝ)
    {radius : ℝ} (hradius : 0 < radius) (hradius_le_one : radius ≤ 1) :
    min 1 (Probability.pOneFournierGuillinHeadGateRadius eta
      (Probability.pOneFournierGuillinUniformAllShellMassGateScale
        dimension eta alpha gamma momentBound)) * radius ≤
      theorem310SupercriticalEffectiveRadius dimension eta alpha gamma momentBound radius := by
  let gate := Probability.pOneFournierGuillinHeadGateRadius eta
    (Probability.pOneFournierGuillinUniformAllShellMassGateScale
      dimension eta alpha gamma momentBound)
  have hgate : 0 < gate := by
    dsimp [gate, Probability.pOneFournierGuillinHeadGateRadius]
    positivity
  have hminimum_nonneg : 0 ≤ min 1 gate := by positivity
  unfold theorem310SupercriticalEffectiveRadius
  change min 1 gate * radius ≤ min radius gate
  apply le_min
  · calc
      min 1 gate * radius ≤ 1 * radius :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hradius.le
      _ = radius := one_mul _
  · calc
      min 1 gate * radius ≤ min 1 gate * 1 :=
        mul_le_mul_of_nonneg_left hradius_le_one hminimum_nonneg
      _ = min 1 gate := mul_one _
      _ ≤ gate := min_le_right _ _

/-- The final parameter-only count coefficient, including the bounded loss
from the uniform moment-class cap. -/
noncomputable def theorem310SupercriticalUniformSampleRateConstant
    (dimension : ℕ) (eta alpha gamma momentBound tailBound : ℝ) : ℝ :=
  let gate := Probability.pOneFournierGuillinHeadGateRadius eta
    (Probability.pOneFournierGuillinUniformAllShellMassGateScale
      dimension eta alpha gamma momentBound)
  2 * theorem310SupercriticalSampleRateConstant dimension eta alpha gamma tailBound /
    (min 1 gate) ^ dimension

/-- Unrestricted honest-radius version of the actual-count theorem.  No
small-deviation premise remains: it has been absorbed into the displayed
parameter-only coefficient. -/
theorem theorem310SupercriticalUniformRateCountSchedule_le
    (dimension : ℕ) (hdimension : 2 < dimension)
    {eta alpha gamma momentBound tailBound radius p : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1)
    (hp : 0 < p) (hp_le_one : p ≤ 1) (round : ℕ) :
    (theorem310SupercriticalUniformRateCountSchedule dimension eta alpha gamma momentBound
      tailBound radius p round : ℝ) ≤
      theorem310SupercriticalUniformSampleRateConstant
        dimension eta alpha gamma momentBound tailBound *
        (1 / radius ^ dimension) * theorem310ShiftedRoundLog p round := by
  let gate := Probability.pOneFournierGuillinHeadGateRadius eta
    (Probability.pOneFournierGuillinUniformAllShellMassGateScale
      dimension eta alpha gamma momentBound)
  let capFactor := min 1 gate
  let effectiveRadius :=
    theorem310SupercriticalEffectiveRadius dimension eta alpha gamma momentBound radius
  have hgate : 0 < gate := by
    dsimp [gate, Probability.pOneFournierGuillinHeadGateRadius]
    positivity
  have hcapFactor : 0 < capFactor := by
    dsimp [capFactor]
    exact lt_min zero_lt_one hgate
  have heffective_pos : 0 < effectiveRadius := by
    dsimp [effectiveRadius, theorem310SupercriticalEffectiveRadius, gate]
    exact lt_min hradius hgate
  have heffective_le_one : effectiveRadius ≤ 1 := by
    dsimp [effectiveRadius, theorem310SupercriticalEffectiveRadius]
    exact (min_le_left _ _).trans hradius_le_one
  have heffective_le_gate : effectiveRadius ≤ gate := by
    dsimp [effectiveRadius, theorem310SupercriticalEffectiveRadius, gate]
    exact min_le_right _ _
  have hlower : capFactor * radius ≤ effectiveRadius := by
    dsimp [capFactor, effectiveRadius, gate]
    exact min_one_gate_mul_radius_le_effectiveRadius dimension eta alpha gamma momentBound
      hradius hradius_le_one
  have hinverse : 1 / effectiveRadius ^ dimension ≤
      (1 / capFactor ^ dimension) * (1 / radius ^ dimension) := by
    have hpower := pow_le_pow_left₀ (mul_pos hcapFactor hradius).le hlower dimension
    calc
      1 / effectiveRadius ^ dimension ≤ 1 / (capFactor * radius) ^ dimension :=
        one_div_le_one_div_of_le (pow_pos (mul_pos hcapFactor hradius) _) hpower
      _ = (1 / capFactor ^ dimension) * (1 / radius ^ dimension) := by
        rw [mul_pow]
        field_simp [hcapFactor.ne', hradius.ne']
  have hsmall := theorem310SupercriticalRateCountSchedule_le dimension hdimension
    heta halphaGap hgamma htailBound heffective_pos heffective_le_one hp hp_le_one
      heffective_le_gate round
  change (theorem310SupercriticalRateCountSchedule dimension eta alpha gamma momentBound
    tailBound effectiveRadius p round : ℝ) ≤ _
  calc
    (theorem310SupercriticalRateCountSchedule dimension eta alpha gamma momentBound
        tailBound effectiveRadius p round : ℝ) ≤
      2 * theorem310SupercriticalSampleRateConstant dimension eta alpha gamma tailBound *
        (1 / effectiveRadius ^ dimension) * theorem310ShiftedRoundLog p round := hsmall
    _ ≤ 2 * theorem310SupercriticalSampleRateConstant dimension eta alpha gamma tailBound *
        ((1 / capFactor ^ dimension) * (1 / radius ^ dimension)) *
          theorem310ShiftedRoundLog p round := by
      apply mul_le_mul_of_nonneg_right _
        (zero_le_one.trans (theorem310ShiftedRoundLog_one_le hp hp_le_one round))
      exact mul_le_mul_of_nonneg_left hinverse
        (mul_nonneg (by norm_num)
          (theorem310SupercriticalSampleRateConstant_pos dimension hdimension
            heta halphaGap hgamma htailBound).le)
    _ = theorem310SupercriticalUniformSampleRateConstant
          dimension eta alpha gamma momentBound tailBound *
        (1 / radius ^ dimension) * theorem310ShiftedRoundLog p round := by
      dsimp [theorem310SupercriticalUniformSampleRateConstant, capFactor, gate]
      ring

/-- Literal-log corollary of the unrestricted actual-count theorem. -/
theorem theorem310SupercriticalUniformRateCountSchedule_le_literal_log
    (dimension : ℕ) (hdimension : 2 < dimension)
    {eta alpha gamma momentBound tailBound radius p : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1)
    (hp : 0 < p) (hp_le_exp_neg_one : p ≤ Real.exp (-1)) (round : ℕ) :
    (theorem310SupercriticalUniformRateCountSchedule dimension eta alpha gamma momentBound
      tailBound radius p round : ℝ) ≤
      2 * theorem310SupercriticalUniformSampleRateConstant
        dimension eta alpha gamma momentBound tailBound *
        (1 / radius ^ dimension) *
          Real.log (((round + 1 : ℕ) : ℝ) / p) := by
  have hp_le_one : p ≤ 1 :=
    hp_le_exp_neg_one.trans (Real.exp_lt_one_iff.mpr (by norm_num)).le
  have hbase := theorem310SupercriticalUniformRateCountSchedule_le dimension hdimension
    (momentBound := momentBound) heta halphaGap hgamma htailBound hradius hradius_le_one
      hp hp_le_one round
  have htime : (1 : ℝ) ≤ ((round + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega : round + 1 ≠ 0)
  have hratio_exp : Real.exp 1 ≤ ((round + 1 : ℕ) : ℝ) / p := by
    apply (le_div_iff₀ hp).mpr
    calc
      Real.exp 1 * p = p * Real.exp 1 := by ring
      _ ≤ Real.exp (-1) * Real.exp 1 :=
        mul_le_mul_of_nonneg_right hp_le_exp_neg_one (Real.exp_pos 1).le
      _ = 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ ((round + 1 : ℕ) : ℝ) := htime
  have hlog_one : 1 ≤ Real.log (((round + 1 : ℕ) : ℝ) / p) := by
    simpa using Real.log_le_log (Real.exp_pos 1) hratio_exp
  have hshifted : theorem310ShiftedRoundLog p round ≤
      2 * Real.log (((round + 1 : ℕ) : ℝ) / p) := by
    unfold theorem310ShiftedRoundLog
    linarith
  calc
    (theorem310SupercriticalUniformRateCountSchedule dimension eta alpha gamma momentBound
        tailBound radius p round : ℝ) ≤
      theorem310SupercriticalUniformSampleRateConstant
          dimension eta alpha gamma momentBound tailBound *
        (1 / radius ^ dimension) * theorem310ShiftedRoundLog p round := hbase
    _ ≤ theorem310SupercriticalUniformSampleRateConstant
          dimension eta alpha gamma momentBound tailBound *
        (1 / radius ^ dimension) *
          (2 * Real.log (((round + 1 : ℕ) : ℝ) / p)) := by
      have hgate : 0 < Probability.pOneFournierGuillinHeadGateRadius eta
          (Probability.pOneFournierGuillinUniformAllShellMassGateScale
            dimension eta alpha gamma momentBound) := by
        unfold Probability.pOneFournierGuillinHeadGateRadius
        exact Real.rpow_pos_of_pos (by positivity) _
      have hcapFactor : 0 < min 1
          (Probability.pOneFournierGuillinHeadGateRadius eta
            (Probability.pOneFournierGuillinUniformAllShellMassGateScale
              dimension eta alpha gamma momentBound)) :=
        lt_min zero_lt_one hgate
      have hconstant_nonneg : 0 ≤ theorem310SupercriticalUniformSampleRateConstant
          dimension eta alpha gamma momentBound tailBound := by
        unfold theorem310SupercriticalUniformSampleRateConstant
        exact (div_pos
          (mul_pos (by norm_num)
            (theorem310SupercriticalSampleRateConstant_pos dimension hdimension
              heta halphaGap hgamma htailBound))
          (pow_pos hcapFactor dimension)).le
      exact mul_le_mul_of_nonneg_left hshifted
        (mul_nonneg hconstant_nonneg (by positivity))
    _ = 2 * theorem310SupercriticalUniformSampleRateConstant
          dimension eta alpha gamma momentBound tailBound *
        (1 / radius ^ dimension) *
          Real.log (((round + 1 : ℕ) : ℝ) / p) := by ring

end PZMH20PerformativePrediction
