import ZhouChenLi2014OptimalPACMultipleArm.QuartileBatch
import ZhouChenLi2014OptimalPACMultipleArm.QuartileTermination
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.AdaptiveQueryInvariants
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.PAC

/-!
# Fresh adaptive Quartile-Elimination rounds

This is the finite-PMF composition layer for QE.  A new round outcome is
drawn after the preceding active set is known.  Uniform historywise one-round
failure bounds therefore compose by the finite adaptive-query union bound,
without incorrectly assuming independence across random active sets.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The deterministic active-set update from one fresh QE round outcome. -/
noncomputable def quartileRoundAdvance {Arm Outcome : Type*} [Fintype Arm]
    (score : ℕ → Finset Arm → Outcome → Arm → ℝ)
    (round : ℕ) (active : Finset Arm) (outcome : Outcome) : Finset Arm :=
  quartileEliminationSurvivors active (score round active outcome)

/-- The current mean maximizer of a nonempty finite active set. -/
noncomputable def quartileRoundMeanMaximizer {Arm : Type*}
    (mean : Arm → ℝ) (active : Finset Arm) (hactive : active.Nonempty) : active := by
  classical
  letI : Nonempty active := by
    rcases hactive with ⟨arm, harm⟩
    exact ⟨⟨arm, harm⟩⟩
  exact finiteActiveMeanMaximizer mean active

theorem mean_le_quartileRoundMeanMaximizer {Arm : Type*}
    (mean : Arm → ℝ) (active : Finset Arm) (hactive : active.Nonempty) (arm : active) :
    mean arm.val ≤ mean (quartileRoundMeanMaximizer mean active hactive).val := by
  classical
  letI : Nonempty active := by
    rcases hactive with ⟨arm, harm⟩
    exact ⟨⟨arm, harm⟩⟩
  exact mean_le_finiteActiveMeanMaximizer mean active arm

/--
The bad event of one QE round: the next active set contains no arm within
twice the round error of the current active-set mean maximum.  An empty input
is assigned `False`; the all-success invariant below keeps active sets
nonempty from a nonempty initial set.
-/
noncomputable def quartileRoundBad {Arm Outcome : Type*} [Fintype Arm]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (score : ℕ → Finset Arm → Outcome → Arm → ℝ)
    (round : ℕ) (active : Finset Arm) (outcome : Outcome) : Prop := by
  classical
  by_cases hactive : active.Nonempty
  · exact ¬ ∃ survivor, survivor ∈ quartileRoundAdvance score round active outcome ∧
      mean (quartileRoundMeanMaximizer mean active hactive).val - 2 * error round ≤
        mean survivor
  · exact False

/-- The finite adaptive execution law of history-selected fresh QE rounds. -/
noncomputable def freshQuartileRoundsStateLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (score : ℕ → Finset Arm → Outcome → Arm → ℝ) (roundCount : ℕ) :
    PMF (Finset Arm × Bool) := by
  classical
  letI : ∀ round active outcome,
      Decidable (quartileRoundBad mean error score round active outcome) :=
    fun _ _ _ => Classical.propDecidable _
  exact adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw
    (quartileRoundAdvance score) (quartileRoundBad mean error score) roundCount

/-- A nonempty active set remains nonempty after any tie-broken QE update. -/
theorem quartileRoundAdvance_nonempty {Arm Outcome : Type*} [Fintype Arm]
    (score : ℕ → Finset Arm → Outcome → Arm → ℝ)
    (round : ℕ) (active : Finset Arm) (outcome : Outcome) (hactive : active.Nonempty) :
    (quartileRoundAdvance score round active outcome).Nonempty := by
  exact quartileEliminationSurvivors_nonempty active (score round active outcome) hactive

/--
If a nonempty round is not bad, its next active set contains an arm within
twice the current round error of the current mean maximum.
-/
theorem exists_quartileRoundAdvance_near_mean_maximum_of_not_bad
    {Arm Outcome : Type*} [Fintype Arm]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (score : ℕ → Finset Arm → Outcome → Arm → ℝ)
    (round : ℕ) (active : Finset Arm) (outcome : Outcome) (hactive : active.Nonempty)
    (hnotBad : ¬ quartileRoundBad mean error score round active outcome) :
    ∃ survivor, survivor ∈ quartileRoundAdvance score round active outcome ∧
      mean (quartileRoundMeanMaximizer mean active hactive).val - 2 * error round ≤
        mean survivor := by
  classical
  by_contra hnone
  apply hnotBad
  unfold quartileRoundBad
  rw [dif_pos hactive]
  exact hnone

/--
Below four active arms the tie-broken QE update changes no set, so its bad
event is impossible for every nonnegative round error.  This is the finite
stopping branch needed by the source schedule: no later batch need be drawn
after QE has reached its terminal small set.
-/
theorem not_quartileRoundBad_of_card_le_three
    {Arm Outcome : Type*} [Fintype Arm]
    (mean : Arm → ℝ) (error : ℕ → ℝ)
    (score : ℕ → Finset Arm → Outcome → Arm → ℝ)
    (round : ℕ) (active : Finset Arm) (outcome : Outcome)
    (hcard : active.card ≤ 3) (herror : 0 ≤ error round) :
    ¬ quartileRoundBad mean error score round active outcome := by
  classical
  by_cases hactive : active.Nonempty
  · have hadvance : quartileRoundAdvance score round active outcome = active := by
      apply Finset.eq_of_subset_of_card_le
      · exact quartileEliminationSurvivors_subset active (score round active outcome)
      · change active.card ≤
          (quartileEliminationSurvivors active (score round active outcome)).card
        rw [quartileEliminationSurvivors_card]
        unfold quartileSurvivorCount
        omega
    let reference : active := quartileRoundMeanMaximizer mean active hactive
    unfold quartileRoundBad
    rw [dif_pos hactive]
    intro hbad
    apply hbad
    refine ⟨reference.val, ?_, ?_⟩
    · rw [hadvance]
      exact reference.property
    · nlinarith
  · unfold quartileRoundBad
    rw [dif_neg hactive]
    simp

/--
The active-set cardinality at every positive-mass adaptive QE state is the
deterministic rounded recurrence, independently of all observed batch values
and of the accumulated failure flag.
-/
theorem freshQuartileRoundsStateLaw_support_card_eq_iter
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (mean : Arm → ℝ) (error : ℕ → ℝ) (initial : Finset Arm)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (score : ℕ → Finset Arm → Outcome → Arm → ℝ) (roundCount : ℕ)
    (stateFailure : Finset Arm × Bool)
    (hsupport : stateFailure ∈
      (freshQuartileRoundsStateLaw mean error initial outcomeLaw score roundCount).support) :
    stateFailure.1.card = quartileSurvivorCountIter roundCount initial.card := by
  classical
  let advance : AdaptiveStateUpdate (Finset Arm) Outcome := quartileRoundAdvance score
  let bad : ℕ → Finset Arm → Outcome → Prop := quartileRoundBad mean error score
  let invariant : ℕ → Finset Arm → Bool → Prop := fun completed active _ =>
    active.card = quartileSurvivorCountIter completed initial.card
  letI : ∀ round active outcome, Decidable (bad round active outcome) :=
    fun _ _ _ => Classical.propDecidable _
  have hinitial : ∀ active ∈ (PMF.pure initial).support, invariant 0 active false := by
    intro active hactive
    have hactiveEq : active = initial := by simpa using hactive
    subst active
    simp [invariant, quartileSurvivorCountIter]
  have hadvance : ∀ round active flag outcome,
      invariant round active flag →
      invariant (round + 1) (advance round active outcome)
        (flag || decide (bad round active outcome)) := by
    intro round active flag outcome hinvariant
    dsimp [invariant] at hinvariant ⊢
    change (quartileEliminationSurvivors active (score round active outcome)).card = _
    rw [quartileEliminationSurvivors_card, quartileSurvivorCountIter_succ_eq_update,
      hinvariant]
  have hinvariantSupport := adaptiveQueryStateLaw_support_invariant
    (PMF.pure initial) outcomeLaw advance bad invariant hinitial hadvance
  simpa [freshQuartileRoundsStateLaw, advance, bad, invariant] using
    (hinvariantSupport roundCount stateFailure hsupport)

/--
Fresh QE-round failures compose under arbitrary history-selected outcome laws.
On the all-success event, the final active set contains an arm within the sum
of the round losses of the initial active-set mean maximum.
-/
theorem freshQuartileRounds_near_initial_maximum_probability_ge_one_sub_sum
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (mean : Arm → ℝ) (error : ℕ → ℝ) (initial : Finset Arm)
    (hinitial : initial.Nonempty)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (score : ℕ → Finset Arm → Outcome → Arm → ℝ)
    (failureBudget : ℕ → ℝ) (roundCount : ℕ)
    (hfailure : ∀ round active,
      pmfProbClassical (outcomeLaw round active)
        (quartileRoundBad mean error score round active) ≤ failureBudget round) :
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      pmfProb (freshQuartileRoundsStateLaw mean error initial outcomeLaw score roundCount)
        (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean (quartileRoundMeanMaximizer mean initial hinitial).val -
            ∑ round ∈ Finset.range roundCount, 2 * error round ≤ mean survivor) := by
  classical
  let advance : AdaptiveStateUpdate (Finset Arm) Outcome := quartileRoundAdvance score
  let bad : ℕ → Finset Arm → Outcome → Prop := quartileRoundBad mean error score
  let initialMaximum : Arm := (quartileRoundMeanMaximizer mean initial hinitial).val
  let invariant : ℕ → Finset Arm → Bool → Prop := fun completed active flag =>
    flag = false → ∃ survivor, survivor ∈ active ∧
      mean initialMaximum - ∑ round ∈ Finset.range completed, 2 * error round ≤ mean survivor
  letI : ∀ round active outcome, Decidable (bad round active outcome) :=
    fun _ _ _ => Classical.propDecidable _
  have hinvariantInitial : ∀ active ∈ (PMF.pure initial).support, invariant 0 active false := by
    intro active hactive _
    have hactiveEq : active = initial := by simpa using hactive
    subst active
    refine ⟨initialMaximum, (quartileRoundMeanMaximizer mean initial hinitial).property, ?_⟩
    · simp [initialMaximum]
  have hinvariantAdvance : ∀ round active flag outcome,
      invariant round active flag →
      invariant (round + 1) (advance round active outcome)
        (flag || decide (bad round active outcome)) := by
    intro round active flag outcome hinvariant hnextFlag
    have hflag : flag = false := (Bool.or_eq_false_iff.mp hnextFlag).1
    have hbadFalse : decide (bad round active outcome) = false :=
      (Bool.or_eq_false_iff.mp hnextFlag).2
    have hnotBad : ¬ bad round active outcome := by simpa using hbadFalse
    rcases hinvariant hflag with ⟨previous, hpreviousMem, hpreviousNear⟩
    have hactive : active.Nonempty := ⟨previous, hpreviousMem⟩
    obtain ⟨survivor, hsurvivorMem, hsurvivorNear⟩ :=
      exists_quartileRoundAdvance_near_mean_maximum_of_not_bad
        mean error score round active outcome hactive hnotBad
    refine ⟨survivor, hsurvivorMem, ?_⟩
    have hpreviousLeMaximum : mean previous ≤
        mean (quartileRoundMeanMaximizer mean active hactive).val := by
      exact mean_le_quartileRoundMeanMaximizer mean active hactive ⟨previous, hpreviousMem⟩
    rw [Finset.sum_range_succ]
    nlinarith
  have hinvariantSupport := adaptiveQueryStateLaw_support_invariant
    (PMF.pure initial) outcomeLaw advance bad invariant hinvariantInitial hinvariantAdvance
  have hsuccess := adaptiveQuerySuccessProbability_ge_one_sub_sum
    (PMF.pure initial) outcomeLaw advance bad failureBudget (by
      intro round active
      simpa [pmfProbClassical, bad] using hfailure round active) roundCount
  have hstate : ∀ stateFailure ∈
      (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount).support,
      stateFailure.2 = false → ∃ survivor, survivor ∈ stateFailure.1 ∧
        mean initialMaximum - ∑ round ∈ Finset.range roundCount, 2 * error round ≤ mean survivor := by
    intro stateFailure hsupport hflag
    exact hinvariantSupport roundCount stateFailure hsupport hflag
  have hequal : pmfProb
      (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount)
      (fun stateFailure => stateFailure.2 = false) =
      pmfProb
        (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount)
        (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean initialMaximum - ∑ round ∈ Finset.range roundCount, 2 * error round ≤
            mean survivor) := by
    apply pmfProb_eq_of_support_iff
    intro stateFailure hsupport
    constructor
    · intro hflag
      exact ⟨hflag, hstate stateFailure hsupport hflag⟩
    · exact fun h => h.1
  simpa [freshQuartileRoundsStateLaw, advance, bad, initialMaximum] using hsuccess.trans_eq hequal

/--
The same QE composition theorem when round-tail estimates are known only on
positive-mass preceding states.  This is the natural premise for a
state-dependent finite schedule whose active-set cardinality is itself an
execution invariant.
-/
theorem freshQuartileRounds_near_initial_maximum_probability_ge_one_sub_sum_of_support
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (mean : Arm → ℝ) (error : ℕ → ℝ) (initial : Finset Arm)
    (hinitial : initial.Nonempty)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (score : ℕ → Finset Arm → Outcome → Arm → ℝ)
    (failureBudget : ℕ → ℝ) (roundCount : ℕ)
    (hfailure : ∀ round (stateFailure : Finset Arm × Bool),
      stateFailure ∈
        (freshQuartileRoundsStateLaw mean error initial outcomeLaw score round).support →
      pmfProbClassical (outcomeLaw round stateFailure.1)
        (quartileRoundBad mean error score round stateFailure.1) ≤ failureBudget round) :
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      pmfProb (freshQuartileRoundsStateLaw mean error initial outcomeLaw score roundCount)
        (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean (quartileRoundMeanMaximizer mean initial hinitial).val -
            ∑ round ∈ Finset.range roundCount, 2 * error round ≤ mean survivor) := by
  classical
  let advance : AdaptiveStateUpdate (Finset Arm) Outcome := quartileRoundAdvance score
  let bad : ℕ → Finset Arm → Outcome → Prop := quartileRoundBad mean error score
  let initialMaximum : Arm := (quartileRoundMeanMaximizer mean initial hinitial).val
  let invariant : ℕ → Finset Arm → Bool → Prop := fun completed active flag =>
    flag = false → ∃ survivor, survivor ∈ active ∧
      mean initialMaximum - ∑ round ∈ Finset.range completed, 2 * error round ≤ mean survivor
  letI : ∀ round active outcome, Decidable (bad round active outcome) :=
    fun _ _ _ => Classical.propDecidable _
  have hinvariantInitial : ∀ active ∈ (PMF.pure initial).support, invariant 0 active false := by
    intro active hactive _
    have hactiveEq : active = initial := by simpa using hactive
    subst active
    refine ⟨initialMaximum, (quartileRoundMeanMaximizer mean initial hinitial).property, ?_⟩
    · simp [initialMaximum]
  have hinvariantAdvance : ∀ round active flag outcome,
      invariant round active flag →
      invariant (round + 1) (advance round active outcome)
        (flag || decide (bad round active outcome)) := by
    intro round active flag outcome hinvariant hnextFlag
    have hflag : flag = false := (Bool.or_eq_false_iff.mp hnextFlag).1
    have hbadFalse : decide (bad round active outcome) = false :=
      (Bool.or_eq_false_iff.mp hnextFlag).2
    have hnotBad : ¬ bad round active outcome := by simpa using hbadFalse
    rcases hinvariant hflag with ⟨previous, hpreviousMem, hpreviousNear⟩
    have hactive : active.Nonempty := ⟨previous, hpreviousMem⟩
    obtain ⟨survivor, hsurvivorMem, hsurvivorNear⟩ :=
      exists_quartileRoundAdvance_near_mean_maximum_of_not_bad
        mean error score round active outcome hactive hnotBad
    refine ⟨survivor, hsurvivorMem, ?_⟩
    have hpreviousLeMaximum : mean previous ≤
        mean (quartileRoundMeanMaximizer mean active hactive).val := by
      exact mean_le_quartileRoundMeanMaximizer mean active hactive ⟨previous, hpreviousMem⟩
    rw [Finset.sum_range_succ]
    nlinarith
  have hinvariantSupport := adaptiveQueryStateLaw_support_invariant
    (PMF.pure initial) outcomeLaw advance bad invariant hinvariantInitial hinvariantAdvance
  have hsuccess := adaptiveQuerySuccessProbability_ge_one_sub_sum_of_support
    (PMF.pure initial) outcomeLaw advance bad failureBudget (by
      intro round stateFailure hsupport
      simpa [freshQuartileRoundsStateLaw, advance, bad, pmfProbClassical] using
        hfailure round stateFailure (by
          simpa [freshQuartileRoundsStateLaw, advance, bad] using hsupport)) roundCount
  have hstate : ∀ stateFailure ∈
      (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount).support,
      stateFailure.2 = false → ∃ survivor, survivor ∈ stateFailure.1 ∧
        mean initialMaximum - ∑ round ∈ Finset.range roundCount, 2 * error round ≤ mean survivor := by
    intro stateFailure hsupport hflag
    exact hinvariantSupport roundCount stateFailure hsupport hflag
  have hequal : pmfProb
      (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount)
      (fun stateFailure => stateFailure.2 = false) =
      pmfProb
        (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount)
        (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean initialMaximum - ∑ round ∈ Finset.range roundCount, 2 * error round ≤
            mean survivor) := by
    apply pmfProb_eq_of_support_iff
    intro stateFailure hsupport
    constructor
    · intro hflag
      exact ⟨hflag, hstate stateFailure hsupport hflag⟩
    · exact fun h => h.1
  simpa [freshQuartileRoundsStateLaw, advance, bad, initialMaximum] using hsuccess.trans_eq hequal

/--
A retained arm near the initial maximum, followed by an approximate best-arm
choice within that retained active set, is an approximate best arm globally.
This deterministic bridge is the endpoint needed to attach QE to any valid
final-stage policy without treating the random survivor set as fixed.
-/
theorem epsilonPACBestArm_of_near_initial_maximum_and_activePAC
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (initial active : Finset Arm) (hinitial : initial.Nonempty)
    (hinitialAll : ∀ arm, arm ∈ initial) (loss finalError : ℝ) (selected : active)
    (hnear : ∃ survivor, survivor ∈ active ∧
      mean (quartileRoundMeanMaximizer mean initial hinitial).val - loss ≤ mean survivor)
    (hfinal : EpsilonPACBestArm (fun arm : active => mean arm.val) finalError selected) :
    EpsilonPACBestArm mean (loss + finalError) selected.val := by
  intro competitor
  rcases hnear with ⟨survivor, hsurvivor, hnear⟩
  have hmaximum : mean competitor ≤
      mean (quartileRoundMeanMaximizer mean initial hinitial).val :=
    mean_le_quartileRoundMeanMaximizer mean initial hinitial ⟨competitor, hinitialAll competitor⟩
  have hfinalSurvivor := hfinal ⟨survivor, hsurvivor⟩
  dsimp at hfinalSurvivor
  linarith

end ZhouChenLi2014OptimalPACMultipleArm
