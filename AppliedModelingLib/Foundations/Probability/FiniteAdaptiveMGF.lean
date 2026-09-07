import AppliedModelingLib.Foundations.Probability.FiniteAdaptiveSuccessTail
import AppliedModelingLib.Foundations.Probability.FinitePinsker

/-!
# Exponential supermartingales for finite adaptive traces

This module supplies the finite-PMF induction behind adaptive concentration.
The next-round law may depend on the full preceding trace; no independence
between rounds is assumed.  It is the finite counterpart of the
Ionescu--Tulcea product-supermartingale argument used in privacy composition.
-/

namespace AppliedModelingLib

noncomputable section

/-- A centered finite-PMF increment with absolute bound `bound` has the
Hoeffding exponential-moment bound at every real step size. -/
theorem pmfExp_exp_mul_le_exp_half_bound_sq_mul_sq
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (increment : Outcome → ℝ) (bound step : ℝ)
    (hbound : 0 ≤ bound)
    (hmean : pmfExp law increment = 0)
    (hincrement : ∀ outcome, |increment outcome| ≤ bound) :
    pmfExp law (fun outcome ↦ Real.exp (step * increment outcome)) ≤
      Real.exp (bound ^ 2 * step ^ 2 / 2) := by
  by_cases hboundZero : bound = 0
  · have hincrementZero : ∀ outcome, increment outcome = 0 := by
      intro outcome
      have habs : |increment outcome| = 0 :=
        le_antisymm (by simpa [hboundZero] using hincrement outcome) (abs_nonneg _)
      exact abs_eq_zero.mp habs
    simp [hincrementZero, hboundZero]
  · have hboundPos : 0 < bound := lt_of_le_of_ne hbound (Ne.symm hboundZero)
    let normalized : Outcome → ℝ := fun outcome ↦ increment outcome / bound
    have hnormalizedLower : ∀ outcome, -1 ≤ normalized outcome := by
      intro outcome
      have hlower : -bound ≤ increment outcome := (abs_le.mp (hincrement outcome)).1
      exact (le_div_iff₀ hboundPos).2 (by simpa using hlower)
    have hnormalizedUpper : ∀ outcome, normalized outcome ≤ 1 := by
      intro outcome
      have hupper : increment outcome ≤ bound := (abs_le.mp (hincrement outcome)).2
      exact (div_le_one hboundPos).2 hupper
    have hnormalizedMean : pmfExp law normalized = 0 := by
      dsimp [normalized]
      rw [show (fun outcome ↦ increment outcome / bound) =
          (fun outcome ↦ increment outcome * bound⁻¹) by
        funext outcome
        rw [div_eq_mul_inv]]
      rw [pmfExp_mul_const, hmean, zero_mul]
    have hmgf := finiteMGF_centered_le_exp_half_sq law normalized
      hnormalizedLower hnormalizedUpper (step * bound)
    rw [hnormalizedMean] at hmgf
    simp only [sub_zero] at hmgf
    calc
      pmfExp law (fun outcome ↦ Real.exp (step * increment outcome)) =
          Probability.finiteMGF law normalized (step * bound) := by
            unfold pmfExp Probability.finiteMGF
            apply Finset.sum_congr rfl
            intro outcome _
            congr 2
            dsimp [normalized]
            field_simp
      _ ≤ Real.exp ((step * bound) ^ 2 / 2) := hmgf
      _ = Real.exp (bound ^ 2 * step ^ 2 / 2) := by
        congr 1
        ring

/-- A finite-PMF score in `[-bound, bound]` has the same Hoeffding
exponential-moment estimate after subtraction of its own mean.  This form
retains a separately supplied upper bound on that mean, which is the form
needed for privacy-loss composition. -/
theorem pmfExp_exp_mul_sub_pmfExp_le_exp_half_bound_sq_mul_sq
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (score : Outcome → ℝ) (bound step : ℝ)
    (hbound : 0 ≤ bound)
    (hscore : ∀ outcome, |score outcome| ≤ bound) :
    pmfExp law (fun outcome ↦ Real.exp
      (step * (score outcome - pmfExp law score))) ≤
      Real.exp (bound ^ 2 * step ^ 2 / 2) := by
  by_cases hboundZero : bound = 0
  · have hscoreZero : ∀ outcome, score outcome = 0 := by
      intro outcome
      exact abs_eq_zero.mp <| le_antisymm
        (by simpa [hboundZero] using hscore outcome) (abs_nonneg _)
    have hmeanZero : pmfExp law score = 0 := by
      simp [pmfExp, hscoreZero]
    simp [hscoreZero, hmeanZero, hboundZero]
  · have hboundPos : 0 < bound := lt_of_le_of_ne hbound (Ne.symm hboundZero)
    let normalized : Outcome → ℝ := fun outcome ↦ score outcome / bound
    have hnormalizedLower : ∀ outcome, -1 ≤ normalized outcome := by
      intro outcome
      have hlower : -bound ≤ score outcome := (abs_le.mp (hscore outcome)).1
      exact (le_div_iff₀ hboundPos).2 (by simpa using hlower)
    have hnormalizedUpper : ∀ outcome, normalized outcome ≤ 1 := by
      intro outcome
      have hupper : score outcome ≤ bound := (abs_le.mp (hscore outcome)).2
      exact (div_le_one hboundPos).2 hupper
    have hmeanNormalized : pmfExp law normalized = pmfExp law score / bound := by
      dsimp [normalized]
      rw [show (fun outcome ↦ score outcome / bound) =
          (fun outcome ↦ score outcome * bound⁻¹) by
        funext outcome
        rw [div_eq_mul_inv]]
      rw [pmfExp_mul_const]
      rw [div_eq_mul_inv]
    have hmgf := finiteMGF_centered_le_exp_half_sq law normalized
      hnormalizedLower hnormalizedUpper (step * bound)
    calc
      pmfExp law (fun outcome ↦ Real.exp
          (step * (score outcome - pmfExp law score))) =
          Probability.finiteMGF law
            (fun outcome ↦ normalized outcome - pmfExp law normalized)
            (step * bound) := by
            change pmfExp law (fun outcome ↦ Real.exp
              (step * (score outcome - pmfExp law score))) =
              pmfExp law (fun outcome ↦ Real.exp
                ((step * bound) *
                  (normalized outcome - pmfExp law normalized)))
            apply pmfExp_congr
            intro outcome
            rw [hmeanNormalized]
            dsimp [normalized]
            field_simp
      _ ≤ Real.exp ((step * bound) ^ 2 / 2) := hmgf
      _ = Real.exp (bound ^ 2 * step ^ 2 / 2) := by
        congr 1
        ring

/-- A product of history-dependent, one-step nonnegative multipliers along a
finite adaptive trace. -/
def finiteAdaptiveProductWeight
    {Outcome : Type*}
    (multiplier : ∀ round, (Fin round → Outcome) → Outcome → ℝ) :
    (rounds : ℕ) → (Fin rounds → Outcome) → ℝ
  | 0, _ => 1
  | rounds + 1, trace =>
      finiteAdaptiveProductWeight multiplier rounds (Fin.init trace) *
        multiplier rounds (Fin.init trace) (trace (Fin.last rounds))

/-- Appending one outcome multiplies the accumulated adaptive weight by its
new one-step factor. -/
theorem finiteAdaptiveProductWeight_snoc
    {Outcome : Type*}
    (multiplier : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    {rounds : ℕ} (history : Fin rounds → Outcome) (outcome : Outcome) :
    finiteAdaptiveProductWeight multiplier (rounds + 1) (Fin.snoc history outcome) =
      finiteAdaptiveProductWeight multiplier rounds history *
        multiplier rounds history outcome := by
  simp [finiteAdaptiveProductWeight]

/-- Nonnegative one-step multipliers give a nonnegative adaptive product. -/
theorem finiteAdaptiveProductWeight_nonneg
    {Outcome : Type*}
    (multiplier : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    (hnonneg : ∀ round history outcome, 0 ≤ multiplier round history outcome) :
    ∀ rounds (trace : Fin rounds → Outcome),
      0 ≤ finiteAdaptiveProductWeight multiplier rounds trace := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace
      simp [finiteAdaptiveProductWeight]
  | succ rounds ih =>
      intro trace
      unfold finiteAdaptiveProductWeight
      exact mul_nonneg (ih (Fin.init trace))
        (hnonneg rounds (Fin.init trace) (trace (Fin.last rounds)))

/--
If every history-conditioned multiplier has expectation at most one, their
product has expectation at most one under the corresponding adaptive trace
law.  This is an exact finite induction, so the history may encode all prior
analyst messages and outputs.
-/
theorem pmfExp_finiteAdaptiveProductWeight_le_one
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (multiplier : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    (hnonneg : ∀ round history outcome, 0 ≤ multiplier round history outcome)
    (hconditional : ∀ round history,
      pmfExp (nextLaw round history) (multiplier round history) ≤ 1) :
    ∀ rounds,
      pmfExp (finiteAdaptiveTraceLaw nextLaw rounds)
        (finiteAdaptiveProductWeight multiplier rounds) ≤ 1 := by
  intro rounds
  induction rounds with
  | zero => simp [finiteAdaptiveTraceLaw, finiteAdaptiveProductWeight]
  | succ rounds ih =>
      rw [pmfExp_finiteAdaptiveTraceLaw_succ]
      calc
        pmfExp (finiteAdaptiveTraceLaw nextLaw rounds) (fun history =>
            pmfExp (nextLaw rounds history) (fun outcome =>
              finiteAdaptiveProductWeight multiplier (rounds + 1)
                (Fin.snoc history outcome))) =
            pmfExp (finiteAdaptiveTraceLaw nextLaw rounds) (fun history =>
              finiteAdaptiveProductWeight multiplier rounds history *
                pmfExp (nextLaw rounds history) (multiplier rounds history)) := by
              apply pmfExp_congr
              intro history
              simp_rw [finiteAdaptiveProductWeight_snoc]
              exact pmfExp_const_mul _ _ _
        _ ≤ pmfExp (finiteAdaptiveTraceLaw nextLaw rounds)
            (finiteAdaptiveProductWeight multiplier rounds) := by
          apply pmfExp_le_pmfExp_of_forall_le
          intro history
          have hweightNonneg : 0 ≤ finiteAdaptiveProductWeight multiplier rounds history :=
            finiteAdaptiveProductWeight_nonneg multiplier hnonneg rounds history
          exact mul_le_of_le_one_right hweightNonneg (hconditional rounds history)
        _ ≤ 1 := ih

/-- Sum of history-dependent real scores along an adaptive finite trace. -/
def finiteAdaptiveScoreSum
    {Outcome : Type*}
    (score : ∀ round, (Fin round → Outcome) → Outcome → ℝ) :
    (rounds : ℕ) → (Fin rounds → Outcome) → ℝ
  | 0, _ => 0
  | rounds + 1, trace =>
      finiteAdaptiveScoreSum score rounds (Fin.init trace) +
        score rounds (Fin.init trace) (trace (Fin.last rounds))

/-- Appending an outcome adds exactly the new history-dependent score. -/
theorem finiteAdaptiveScoreSum_snoc
    {Outcome : Type*}
    (score : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    {rounds : ℕ} (history : Fin rounds → Outcome) (outcome : Outcome) :
    finiteAdaptiveScoreSum score (rounds + 1) (Fin.snoc history outcome) =
      finiteAdaptiveScoreSum score rounds history + score rounds history outcome := by
  simp [finiteAdaptiveScoreSum]

/-- Pointwise score perturbations accumulate at most linearly along a finite
adaptive trace.  This is a deterministic telescoping fact: no independence or
probabilistic assumption on the adaptive outcome law is involved. -/
theorem finiteAdaptiveScoreSum_sub_abs_le
    {Outcome : Type*}
    (left right : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    (error : ℝ)
    (hpoint : ∀ round history outcome,
      |left round history outcome - right round history outcome| ≤ error) :
    ∀ rounds (trace : Fin rounds → Outcome),
      |finiteAdaptiveScoreSum left rounds trace -
        finiteAdaptiveScoreSum right rounds trace| ≤ (rounds : ℝ) * error := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace
      simp [finiteAdaptiveScoreSum]
  | succ rounds ih =>
      intro trace
      cases trace using Fin.snocCases with
      | snoc history outcome =>
          rw [finiteAdaptiveScoreSum_snoc, finiteAdaptiveScoreSum_snoc]
          calc
            |(finiteAdaptiveScoreSum left rounds history + left rounds history outcome) -
                (finiteAdaptiveScoreSum right rounds history + right rounds history outcome)| =
                |(finiteAdaptiveScoreSum left rounds history -
                    finiteAdaptiveScoreSum right rounds history) +
                  (left rounds history outcome - right rounds history outcome)| := by
                    congr 1
                    ring
            _ ≤ |finiteAdaptiveScoreSum left rounds history -
                  finiteAdaptiveScoreSum right rounds history| +
                |left rounds history outcome - right rounds history outcome| := abs_add_le _ _
            _ ≤ (rounds : ℝ) * error + error :=
              add_le_add (ih history) (hpoint rounds history outcome)
            _ = ((rounds + 1 : ℕ) : ℝ) * error := by
              push_cast
              ring

/-- The exponential supermartingale weight for a conditionally centered and
uniformly bounded adaptive score. -/
noncomputable def finiteAdaptiveCenteredWeight
    {Outcome : Type*}
    (increment : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    (bound step : ℝ) (rounds : ℕ) (trace : Fin rounds → Outcome) : ℝ :=
  finiteAdaptiveProductWeight
    (fun round history outcome => Real.exp
      (step * increment round history outcome - bound ^ 2 * step ^ 2 / 2))
    rounds trace

/-- The product supermartingale is the exponential of the centered partial
sum minus its Hoeffding compensator. -/
theorem finiteAdaptiveCenteredWeight_eq_exp
    {Outcome : Type*}
    (increment : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    (bound step : ℝ) :
    ∀ rounds (trace : Fin rounds → Outcome),
      finiteAdaptiveCenteredWeight increment bound step rounds trace =
        Real.exp (step * finiteAdaptiveScoreSum increment rounds trace -
          (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace
      simp [finiteAdaptiveCenteredWeight, finiteAdaptiveProductWeight,
        finiteAdaptiveScoreSum]
  | succ rounds ih =>
      intro trace
      cases trace using Fin.snocCases with
      | snoc history outcome =>
          rw [finiteAdaptiveCenteredWeight, finiteAdaptiveProductWeight_snoc,
            finiteAdaptiveScoreSum_snoc]
          change finiteAdaptiveCenteredWeight increment bound step rounds history *
              Real.exp (step * increment rounds history outcome -
                bound ^ 2 * step ^ 2 / 2) = _
          rw [ih]
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

/-- Finite adaptive Hoeffding supermartingale.  The conditional mean-zero and
range hypotheses are imposed separately at every full history. -/
theorem pmfExp_finiteAdaptiveCenteredWeight_le_one
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (increment : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    (bound step : ℝ)
    (hbound : 0 ≤ bound)
    (hmean : ∀ round history,
      pmfExp (nextLaw round history) (increment round history) = 0)
    (hincrement : ∀ round history outcome,
      |increment round history outcome| ≤ bound) :
    ∀ rounds,
      pmfExp (finiteAdaptiveTraceLaw nextLaw rounds)
        (finiteAdaptiveCenteredWeight increment bound step rounds) ≤ 1 := by
  intro rounds
  apply pmfExp_finiteAdaptiveProductWeight_le_one nextLaw
    (fun round history outcome => Real.exp
      (step * increment round history outcome - bound ^ 2 * step ^ 2 / 2))
  · intro round history outcome
    exact (Real.exp_pos _).le
  · intro round history
    have hmgf := pmfExp_exp_mul_le_exp_half_bound_sq_mul_sq
      (nextLaw round history) (increment round history) bound step hbound
      (hmean round history) (hincrement round history)
    calc
      pmfExp (nextLaw round history) (fun outcome => Real.exp
          (step * increment round history outcome - bound ^ 2 * step ^ 2 / 2)) =
          pmfExp (nextLaw round history) (fun outcome =>
            Real.exp (-(bound ^ 2 * step ^ 2 / 2)) *
              Real.exp (step * increment round history outcome)) := by
              apply pmfExp_congr
              intro outcome
              rw [← Real.exp_add]
              congr 1
              ring
      _ =
          Real.exp (-(bound ^ 2 * step ^ 2 / 2)) *
            pmfExp (nextLaw round history)
              (fun outcome => Real.exp (step * increment round history outcome)) := by
              rw [pmfExp_const_mul]
      _ ≤ Real.exp (-(bound ^ 2 * step ^ 2 / 2)) *
          Real.exp (bound ^ 2 * step ^ 2 / 2) := by
            gcongr
      _ = 1 := by rw [← Real.exp_add]; simp

/-- Exponential upper tail for a conditionally centered bounded finite
adaptive score.  It is an adaptive (not independent-round) Hoeffding bound. -/
theorem pmfProb_finiteAdaptiveScoreSum_ge_le_exp
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (increment : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    (bound step threshold : ℝ) (rounds : ℕ)
    (hbound : 0 ≤ bound) (hstep : 0 ≤ step)
    (hmean : ∀ round history,
      pmfExp (nextLaw round history) (increment round history) = 0)
    (hincrement : ∀ round history outcome,
      |increment round history outcome| ≤ bound) :
    pmfProb (finiteAdaptiveTraceLaw nextLaw rounds)
        (fun trace => threshold ≤ finiteAdaptiveScoreSum increment rounds trace) ≤
      Real.exp (-step * threshold +
        (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) := by
  let weight := finiteAdaptiveCenteredWeight increment bound step rounds
  have hweight := pmfExp_finiteAdaptiveCenteredWeight_le_one nextLaw increment bound step
    hbound hmean hincrement rounds
  have hpoint : ∀ trace : Fin rounds → Outcome,
      (if threshold ≤ finiteAdaptiveScoreSum increment rounds trace then (1 : ℝ) else 0) ≤
        Real.exp (-step * threshold +
          (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) * weight trace := by
    intro trace
    by_cases hlarge : threshold ≤ finiteAdaptiveScoreSum increment rounds trace
    · rw [if_pos hlarge]
      change 1 ≤ Real.exp (-step * threshold +
          (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) *
        finiteAdaptiveCenteredWeight increment bound step rounds trace
      rw [finiteAdaptiveCenteredWeight_eq_exp]
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (-step * threshold +
            (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2) +
            (step * finiteAdaptiveScoreSum increment rounds trace -
              (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2))) := by
              apply Real.exp_le_exp.mpr
              nlinarith [mul_nonneg hstep (sub_nonneg.mpr hlarge)]
        _ = Real.exp (-step * threshold +
            (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) *
            Real.exp (step * finiteAdaptiveScoreSum increment rounds trace -
              (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) := by
              rw [Real.exp_add]
    · simp only [if_neg hlarge]
      exact mul_nonneg (Real.exp_pos _).le
        (finiteAdaptiveProductWeight_nonneg _
          (fun _ _ _ => (Real.exp_pos _).le) rounds trace)
  calc
    pmfProb (finiteAdaptiveTraceLaw nextLaw rounds)
        (fun trace => threshold ≤ finiteAdaptiveScoreSum increment rounds trace) =
        pmfExp (finiteAdaptiveTraceLaw nextLaw rounds)
          (fun trace => if threshold ≤ finiteAdaptiveScoreSum increment rounds trace
            then (1 : ℝ) else 0) := rfl
    _ ≤ pmfExp (finiteAdaptiveTraceLaw nextLaw rounds) (fun trace =>
        Real.exp (-step * threshold +
          (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) * weight trace) :=
      pmfExp_le_pmfExp_of_forall_le _ _ _ hpoint
    _ = Real.exp (-step * threshold +
          (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) *
        pmfExp (finiteAdaptiveTraceLaw nextLaw rounds) weight := by
        rw [pmfExp_const_mul]
    _ ≤ Real.exp (-step * threshold +
          (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) := by
        nlinarith [Real.exp_pos
          (-step * threshold + (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2))]

/-- Optimizing the exponential step gives the usual finite adaptive
Hoeffding tail.  The score increments need only be conditionally centered,
not independent. -/
theorem pmfProb_finiteAdaptiveScoreSum_ge_le_hoeffding
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (increment : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    (bound threshold : ℝ) (rounds : ℕ)
    (hboundPos : 0 < bound) (hthreshold : 0 ≤ threshold)
    (hrounds : 0 < rounds)
    (hmean : ∀ round history,
      pmfExp (nextLaw round history) (increment round history) = 0)
    (hincrement : ∀ round history outcome,
      |increment round history outcome| ≤ bound) :
    pmfProb (finiteAdaptiveTraceLaw nextLaw rounds)
        (fun trace => threshold ≤ finiteAdaptiveScoreSum increment rounds trace) ≤
      Real.exp (-threshold ^ 2 /
        (2 * (rounds : ℝ) * bound ^ 2)) := by
  let step := threshold / ((rounds : ℝ) * bound ^ 2)
  have hroundsReal : 0 < (rounds : ℝ) := by exact_mod_cast hrounds
  have hdenomPos : 0 < (rounds : ℝ) * bound ^ 2 :=
    mul_pos hroundsReal (sq_pos_of_pos hboundPos)
  have hstep : 0 ≤ step := div_nonneg hthreshold hdenomPos.le
  have htail := pmfProb_finiteAdaptiveScoreSum_ge_le_exp
    nextLaw increment bound step threshold rounds hboundPos.le hstep hmean hincrement
  convert htail using 1
  dsimp [step]
  field_simp [hdenomPos.ne']
  ring_nf

/-- The exponential supermartingale weight for a bounded adaptive score with
conditional mean at most a specified drift. -/
noncomputable def finiteAdaptiveDriftWeight
    {Outcome : Type*}
    (score : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    (drift bound step : ℝ) (rounds : ℕ) (trace : Fin rounds → Outcome) : ℝ :=
  finiteAdaptiveProductWeight
    (fun round history outcome => Real.exp
      (step * (score round history outcome - drift) - bound ^ 2 * step ^ 2 / 2))
    rounds trace

/-- The drifted supermartingale weight is the exponential of the score sum
above its cumulative drift, less the Hoeffding compensator. -/
theorem finiteAdaptiveDriftWeight_eq_exp
    {Outcome : Type*}
    (score : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    (drift bound step : ℝ) :
    ∀ rounds (trace : Fin rounds → Outcome),
      finiteAdaptiveDriftWeight score drift bound step rounds trace =
        Real.exp (step *
          (finiteAdaptiveScoreSum score rounds trace - (rounds : ℝ) * drift) -
          (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace
      simp [finiteAdaptiveDriftWeight, finiteAdaptiveProductWeight,
        finiteAdaptiveScoreSum]
  | succ rounds ih =>
      intro trace
      cases trace using Fin.snocCases with
      | snoc history outcome =>
          rw [finiteAdaptiveDriftWeight, finiteAdaptiveProductWeight_snoc,
            finiteAdaptiveScoreSum_snoc]
          change finiteAdaptiveDriftWeight score drift bound step rounds history *
              Real.exp (step * (score rounds history outcome - drift) -
                bound ^ 2 * step ^ 2 / 2) = _
          rw [ih]
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring

/-- A bounded adaptive score whose conditional means are at most `drift`
has a finite exponential supermartingale. -/
theorem pmfExp_finiteAdaptiveDriftWeight_le_one
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (score : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    (drift bound step : ℝ)
    (hbound : 0 ≤ bound) (hstep : 0 ≤ step)
    (hmean : ∀ round history,
      pmfExp (nextLaw round history) (score round history) ≤ drift)
    (hscore : ∀ round history outcome, |score round history outcome| ≤ bound)
    (rounds : ℕ) :
    pmfExp (finiteAdaptiveTraceLaw nextLaw rounds)
      (finiteAdaptiveDriftWeight score drift bound step rounds) ≤ 1 := by
  apply pmfExp_finiteAdaptiveProductWeight_le_one nextLaw
    (fun round history outcome => Real.exp
      (step * (score round history outcome - drift) - bound ^ 2 * step ^ 2 / 2))
  · intro round history outcome
    exact (Real.exp_pos _).le
  · intro round history
    let mean := pmfExp (nextLaw round history) (score round history)
    have hmgf := pmfExp_exp_mul_sub_pmfExp_le_exp_half_bound_sq_mul_sq
      (nextLaw round history) (score round history) bound step hbound
      (hscore round history)
    calc
      pmfExp (nextLaw round history) (fun outcome => Real.exp
          (step * (score round history outcome - drift) -
            bound ^ 2 * step ^ 2 / 2)) =
          Real.exp (step * (mean - drift) - bound ^ 2 * step ^ 2 / 2) *
            pmfExp (nextLaw round history) (fun outcome => Real.exp
              (step * (score round history outcome - mean))) := by
            rw [← pmfExp_const_mul]
            apply pmfExp_congr
            intro outcome
            rw [← Real.exp_add]
            dsimp [mean]
            congr 1
            ring
      _ ≤ Real.exp (step * (mean - drift) - bound ^ 2 * step ^ 2 / 2) *
          Real.exp (bound ^ 2 * step ^ 2 / 2) := by
          exact mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ = Real.exp (step * (mean - drift)) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ 1 := by
          rw [← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          exact mul_nonpos_of_nonneg_of_nonpos hstep
            (sub_nonpos.mpr (hmean round history))

/-- Exponential upper tail for a bounded finite adaptive score with a
conditional drift bound. -/
theorem pmfProb_finiteAdaptiveScoreSum_ge_drift_add_le_exp
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (score : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    (drift bound step threshold : ℝ) (rounds : ℕ)
    (hbound : 0 ≤ bound) (hstep : 0 ≤ step)
    (hmean : ∀ round history,
      pmfExp (nextLaw round history) (score round history) ≤ drift)
    (hscore : ∀ round history outcome, |score round history outcome| ≤ bound) :
    pmfProb (finiteAdaptiveTraceLaw nextLaw rounds)
        (fun trace => (rounds : ℝ) * drift + threshold ≤
          finiteAdaptiveScoreSum score rounds trace) ≤
      Real.exp (-step * threshold +
        (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) := by
  let weight := finiteAdaptiveDriftWeight score drift bound step rounds
  have hweight := pmfExp_finiteAdaptiveDriftWeight_le_one nextLaw score drift bound step
    hbound hstep hmean hscore rounds
  have hpoint : ∀ trace : Fin rounds → Outcome,
      (if (rounds : ℝ) * drift + threshold ≤
          finiteAdaptiveScoreSum score rounds trace then (1 : ℝ) else 0) ≤
        Real.exp (-step * threshold +
          (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) * weight trace := by
    intro trace
    by_cases hlarge : (rounds : ℝ) * drift + threshold ≤
        finiteAdaptiveScoreSum score rounds trace
    · rw [if_pos hlarge]
      change 1 ≤ Real.exp (-step * threshold +
          (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) *
        finiteAdaptiveDriftWeight score drift bound step rounds trace
      rw [finiteAdaptiveDriftWeight_eq_exp]
      calc
        (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (-step * threshold +
            (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2) +
            (step * (finiteAdaptiveScoreSum score rounds trace -
              (rounds : ℝ) * drift) -
              (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2))) := by
              apply Real.exp_le_exp.mpr
              nlinarith [mul_nonneg hstep (sub_nonneg.mpr hlarge)]
        _ = Real.exp (-step * threshold +
            (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) *
            Real.exp (step * (finiteAdaptiveScoreSum score rounds trace -
              (rounds : ℝ) * drift) -
              (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) := by
              rw [Real.exp_add]
    · simp only [if_neg hlarge]
      exact mul_nonneg (Real.exp_pos _).le
        (finiteAdaptiveProductWeight_nonneg _
          (fun _ _ _ => (Real.exp_pos _).le) rounds trace)
  calc
    pmfProb (finiteAdaptiveTraceLaw nextLaw rounds)
        (fun trace => (rounds : ℝ) * drift + threshold ≤
          finiteAdaptiveScoreSum score rounds trace) =
        pmfExp (finiteAdaptiveTraceLaw nextLaw rounds)
          (fun trace => if (rounds : ℝ) * drift + threshold ≤
              finiteAdaptiveScoreSum score rounds trace then (1 : ℝ) else 0) := rfl
    _ ≤ pmfExp (finiteAdaptiveTraceLaw nextLaw rounds) (fun trace =>
        Real.exp (-step * threshold +
          (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) * weight trace) :=
      pmfExp_le_pmfExp_of_forall_le _ _ _ hpoint
    _ = Real.exp (-step * threshold +
          (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) *
        pmfExp (finiteAdaptiveTraceLaw nextLaw rounds) weight := by
        rw [pmfExp_const_mul]
    _ ≤ Real.exp (-step * threshold +
          (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2)) := by
        nlinarith [Real.exp_pos
          (-step * threshold + (rounds : ℝ) * (bound ^ 2 * step ^ 2 / 2))]

/-- Optimizing the exponential step gives the finite adaptive Hoeffding tail
above a conditional drift bound. -/
theorem pmfProb_finiteAdaptiveScoreSum_ge_drift_add_le_hoeffding
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (nextLaw : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (score : ∀ round, (Fin round → Outcome) → Outcome → ℝ)
    (drift bound threshold : ℝ) (rounds : ℕ)
    (hboundPos : 0 < bound) (hthreshold : 0 ≤ threshold)
    (hrounds : 0 < rounds)
    (hmean : ∀ round history,
      pmfExp (nextLaw round history) (score round history) ≤ drift)
    (hscore : ∀ round history outcome, |score round history outcome| ≤ bound) :
    pmfProb (finiteAdaptiveTraceLaw nextLaw rounds)
        (fun trace => (rounds : ℝ) * drift + threshold ≤
          finiteAdaptiveScoreSum score rounds trace) ≤
      Real.exp (-threshold ^ 2 /
        (2 * (rounds : ℝ) * bound ^ 2)) := by
  let step := threshold / ((rounds : ℝ) * bound ^ 2)
  have hroundsReal : 0 < (rounds : ℝ) := by exact_mod_cast hrounds
  have hdenomPos : 0 < (rounds : ℝ) * bound ^ 2 :=
    mul_pos hroundsReal (sq_pos_of_pos hboundPos)
  have hstep : 0 ≤ step := div_nonneg hthreshold hdenomPos.le
  have htail := pmfProb_finiteAdaptiveScoreSum_ge_drift_add_le_exp
    nextLaw score drift bound step threshold rounds hboundPos.le hstep hmean hscore
  convert htail using 1
  dsimp [step]
  field_simp [hdenomPos.ne']
  ring_nf

end

end AppliedModelingLib
