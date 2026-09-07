import FalahatgarEtAl2017MaxingRanking.FreshStoppedPruneTrace
import FalahatgarEtAl2017MaxingRanking.PruneSourceSchedule
import FalahatgarEtAl2017MaxingRanking.PruneRoundContraction
import FalahatgarEtAl2017MaxingRanking.FiniteSSTExistence

/-!
# Canonical Prune under Algorithm 2's integer source schedule

This file instantiates the stopped finite-PMF trace at the source algorithm's
integer round cap: its counter begins at one and therefore permits
`(Nat.log 2 n)^2 - 1` rounds under the guard `t < (log₂ n)^2`.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/--
Lemma 15's finite joint Prune event at any admissible early stopping horizon.

The supplement's proof first chooses a horizon by which the contracting
bad-arm population falls below the cutoff, and then separately sums the
bad- and good-arm comparison costs only through that horizon.  This theorem
is that finite-PMF bridge: callers provide the integral horizon, the
population cap used by the finite failure budget, and the geometric target.
It retains the actual stopped comparison
trace, rather than charging hypothetical rounds after the active set is
already of size at most `2 * cutoff`.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_and_max_success_probability_of_sourceLemma15_earlyStop
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor maximum : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hmaximum : maximum ∈ initial) (hgap : upper ≤ preferenceGap maximum anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcard : 2 ≤ Fintype.card Arm) (hroundCount : roundCount ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta)
    (htarget : delta ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff) :
    1 - delta ≤
      pmfProb
        (freshStoppedPruneTraceCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
          initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            roundCount anchor lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
          roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1.1 ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
            stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount,
              ((cutoff : ℝ) + delta ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta delta round.val) : ℝ)) := by
  have hcore := canonicalFreshStoppedPruneRounds_card_and_max_success_probability
    preferenceGap hprobability roundCount anchor maximum lower upper delta maxBatch cutoff hbudget
    initial hanchor hmaximum hgap hseparation hdelta
    (hdeltaHalf.trans (by norm_num)) hcard hroundCount hcutoff hdeltaLower htarget
  have htrace := freshStoppedPruneTraceCardAndMaxStateLaw_card_size_cost_and_max_probability_of_joint
    preferenceGap lower cutoff anchor maximum initial delta
    (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
      lower upper delta maxBatch hbudget)
    (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
    roundCount upper (1 - (1 / (Fintype.card Arm : ℝ) ^ 2 + delta / 2))
    hanchor hmaximum hdelta.le htarget hcore
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hcard
  have hcutoffPos : 0 < cutoff := by
    have hcutoffReal : 0 < (cutoff : ℝ) :=
      lt_of_le_of_lt (Real.sqrt_nonneg _) hcutoff
    exact_mod_cast hcutoffReal
  have hcutoffOne : 1 ≤ (cutoff : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr hcutoffPos
  have hcardTwo : (2 : ℝ) ≤ (Fintype.card Arm : ℝ) := by
    exact_mod_cast hcard
  have hdeltaTail : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤ delta / 2 := by
    have hscale : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
        (cutoff : ℝ) / (2 * (Fintype.card Arm : ℝ)) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * (Fintype.card Arm : ℝ))).mpr
      field_simp [ne_of_gt hcardPos]
      nlinarith [hcardTwo, hcutoffOne]
    calc
      1 / (Fintype.card Arm : ℝ) ^ 2 ≤
          (cutoff : ℝ) / (2 * (Fintype.card Arm : ℝ)) := hscale
      _ = ((cutoff : ℝ) / (Fintype.card Arm : ℝ)) / 2 := by ring
      _ ≤ delta / 2 := by gcongr
  calc
    1 - delta ≤ 1 - (1 / (Fintype.card Arm : ℝ) ^ 2 + delta / 2) := by
      linarith
    _ ≤ _ := htrace

/--
Lemma 15's size and exact stopped comparison envelope under Algorithm 2's
integer source round cap, for the nontrivial `n ≥ 3` branch.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_of_sourceLemma15_schedule
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < Nat.log 2 (Fintype.card Arm) - 1,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcard : 3 ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta) :
    1 - delta / 2 ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower delta cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            (Nat.log 2 (Fintype.card Arm) - 1) anchor lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (Nat.log 2 (Fintype.card Arm) - 1)
            lower upper delta maxBatch hbudget)
          (Nat.log 2 (Fintype.card Arm) - 1))
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount (Nat.log 2 (Fintype.card Arm) - 1)
            cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin (Nat.log 2 (Fintype.card Arm) - 1),
              ((cutoff : ℝ) + delta ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta delta round.val) : ℝ)) := by
  let roundCount := Nat.log 2 (Fintype.card Arm) - 1
  have htarget := sourceLemma15_log_two_pred_round_geometric_target
    preferenceGap lower anchor initial cutoff delta hcard hcutoff.le hdelta.le hdeltaHalf
  have hroundCount : roundCount ≤ Fintype.card Arm := by
    dsimp [roundCount]
    exact (Nat.sub_le _ _).trans (Nat.log_le_self _ _)
  have hcore := canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_ge_one_sub_card_inv_sq
    preferenceGap hprobability roundCount anchor lower upper delta maxBatch cutoff hbudget initial
    hanchor hseparation hdelta (hdeltaHalf.trans (by norm_num))
    (by omega : 2 ≤ Fintype.card Arm) hroundCount hcutoff hdeltaLower (by
      simpa [roundCount] using htarget)
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 3) hcard
  have hcutoffPos : 0 < cutoff := by
    exact lt_of_lt_of_le (by omega : 0 < 4)
      (four_le_cutoff_of_sourceLemma15_sqrt (Fintype.card Arm) cutoff hcard hcutoff.le)
  have hcutoffOne : 1 ≤ (cutoff : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hcutoffPos
  have hcardTwo : (2 : ℝ) ≤ (Fintype.card Arm : ℝ) := by
    exact_mod_cast (by omega : 2 ≤ Fintype.card Arm)
  have hdeltaTail : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤ delta / 2 := by
    have hscale : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
        (cutoff : ℝ) / (2 * (Fintype.card Arm : ℝ)) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * (Fintype.card Arm : ℝ))).mpr
      field_simp [ne_of_gt hcardPos]
      nlinarith [hcardTwo, hcutoffOne]
    calc
      1 / (Fintype.card Arm : ℝ) ^ 2 ≤
          (cutoff : ℝ) / (2 * (Fintype.card Arm : ℝ)) := hscale
      _ = ((cutoff : ℝ) / (Fintype.card Arm : ℝ)) / 2 := by ring
      _ ≤ delta / 2 := by gcongr
  calc
    1 - delta / 2 ≤ 1 - 1 / (Fintype.card Arm : ℝ) ^ 2 := by linarith
    _ ≤ _ := hcore

/--
Lemma 15's joint cardinality, maximum-retention, and literal stopped-cost
guarantee at Algorithm 2's integer source round cap, in the high-gap branch
used by Lemma 17.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_and_max_success_probability_of_sourceLemma15_schedule
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor maximum : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < Nat.log 2 (Fintype.card Arm) - 1,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hmaximum : maximum ∈ initial) (hgap : upper ≤ preferenceGap maximum anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcard : 3 ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta) :
    1 - delta ≤
      pmfProb
        (freshStoppedPruneTraceCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
          initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            (Nat.log 2 (Fintype.card Arm) - 1) anchor lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (Nat.log 2 (Fintype.card Arm) - 1)
            lower upper delta maxBatch hbudget)
          (Nat.log 2 (Fintype.card Arm) - 1))
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1.1 ∧
          (stoppedPruneTraceComparisonCount (Nat.log 2 (Fintype.card Arm) - 1)
            cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin (Nat.log 2 (Fintype.card Arm) - 1),
              ((cutoff : ℝ) + delta ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta delta round.val) : ℝ)) := by
  let roundCount := Nat.log 2 (Fintype.card Arm) - 1
  have htarget := sourceLemma15_log_two_pred_round_geometric_target
    preferenceGap lower anchor initial cutoff delta hcard hcutoff.le hdelta.le hdeltaHalf
  have hroundCount : roundCount ≤ Fintype.card Arm := by
    dsimp [roundCount]
    exact (Nat.sub_le _ _).trans (Nat.log_le_self _ _)
  simpa [roundCount] using
    (canonicalFreshStoppedPruneTrace_card_size_cost_and_max_success_probability_of_sourceLemma15_earlyStop
      preferenceGap hprobability roundCount anchor maximum lower upper delta maxBatch cutoff hbudget
      initial hanchor hmaximum hgap hseparation hdelta hdeltaHalf
      (by omega : 2 ≤ Fintype.card Arm) hroundCount hcutoff hdeltaLower (by
        simpa [roundCount] using htarget))

/--
At a zero-round Prune schedule, the stopped trace is deterministically within
the size and exact-cost envelope.  This provides the small-card boundary for
Algorithm 2's source cap.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_of_zero_round_schedule
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (roundCount : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (hroundCount : roundCount = 0)
    (initial : Finset Arm)
    (hdelta : 0 ≤ delta)
    (hsize : initial.card ≤ 2 * cutoff) :
    1 - delta / 2 ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower delta cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            roundCount anchor lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision roundCount
            lower upper delta maxBatch hbudget)
          roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount
            cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin roundCount,
              ((cutoff : ℝ) + delta ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta delta round.val) : ℝ)) := by
  subst roundCount
  calc
    1 - delta / 2 ≤ 1 := by linarith
    _ = pmfProb
      (freshStoppedPruneTraceStateLaw preferenceGap lower delta cutoff anchor initial
        (canonicalFreshPruneOutcomeLaw preferenceGap hprobability 0 anchor lower upper delta
          maxBatch hbudget)
        (canonicalFreshPruneDecision 0 lower upper delta maxBatch hbudget) 0)
      (fun stateFailure => stateFailure.2 = false ∧
        stateFailure.1.1.card ≤ 2 * cutoff ∧
        (stoppedPruneTraceComparisonCount 0 cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
          ∑ round : Fin 0,
            ((cutoff : ℝ) + delta ^ round.val *
              ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
              (fixedSampleBudget lower upper
                (adaptivePruneRoundDelta delta round.val) : ℝ)) := by
      symm
      exact freshStoppedPruneTrace_zero_round_success_probability preferenceGap lower upper delta
        cutoff anchor initial
        (canonicalFreshPruneOutcomeLaw preferenceGap hprobability 0 anchor lower upper delta
          maxBatch hbudget)
        (canonicalFreshPruneDecision 0 lower upper delta maxBatch hbudget) hsize

/--
The zero-round boundary for the joint trace: it retains any initial designated
maximum, has no comparison cost, and is deterministic once the input is small.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_and_max_success_probability_of_zero_round_schedule
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor maximum : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (roundCount : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (hroundCount : roundCount = 0)
    (initial : Finset Arm)
    (hsize : initial.card ≤ 2 * cutoff) (hmaximum : maximum ∈ initial) :
    pmfProb
      (freshStoppedPruneTraceCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
        initial
        (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
          roundCount anchor lower upper delta maxBatch hbudget)
        (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
        roundCount)
      (fun stateFailure => stateFailure.2 = false ∧
        stateFailure.1.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1.1 ∧
        (stoppedPruneTraceComparisonCount roundCount
          cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
          ∑ round : Fin roundCount,
            ((cutoff : ℝ) + delta ^ round.val *
              ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
              (fixedSampleBudget lower upper
                (adaptivePruneRoundDelta delta round.val) : ℝ)) = 1 := by
  subst roundCount
  exact freshStoppedPruneTraceCardAndMaxStateLaw_zero_round_success_probability
    preferenceGap lower upper delta cutoff anchor maximum initial
    (canonicalFreshPruneOutcomeLaw preferenceGap hprobability 0 anchor lower upper delta maxBatch hbudget)
    (canonicalFreshPruneDecision 0 lower upper delta maxBatch hbudget) hsize hmaximum

/--
Lemma 15's source-horizon joint trace event, including its zero-round
small-card boundary.  It joins cardinality, retained maximum, and stopped
comparison cost on one actual Algorithm-2 execution.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_and_max_success_probability_of_sourceLemma15
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor maximum : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < Nat.log 2 (Fintype.card Arm) - 1,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hmaximum : maximum ∈ initial) (hgap : upper ≤ preferenceGap maximum anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta) :
    1 - delta ≤
      pmfProb
        (freshStoppedPruneTraceCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
          initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            (Nat.log 2 (Fintype.card Arm) - 1) anchor lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (Nat.log 2 (Fintype.card Arm) - 1)
            lower upper delta maxBatch hbudget)
          (Nat.log 2 (Fintype.card Arm) - 1))
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1.1 ∧
          (stoppedPruneTraceComparisonCount (Nat.log 2 (Fintype.card Arm) - 1)
            cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin (Nat.log 2 (Fintype.card Arm) - 1),
              ((cutoff : ℝ) + delta ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta delta round.val) : ℝ)) := by
  by_cases hlarge : 3 ≤ Fintype.card Arm
  · exact canonicalFreshStoppedPruneTrace_card_size_cost_and_max_success_probability_of_sourceLemma15_schedule
      preferenceGap hprobability anchor maximum lower upper delta maxBatch cutoff hbudget initial
      hanchor hmaximum hgap hseparation hdelta hdeltaHalf hlarge hcutoff hdeltaLower
  · have hsmall : Fintype.card Arm ≤ 2 := by omega
    have hroundCount : Nat.log 2 (Fintype.card Arm) - 1 = 0 := by
      have hlog : Nat.log 2 (Fintype.card Arm) ≤ 1 := by
        calc
          Nat.log 2 (Fintype.card Arm) ≤ Nat.log 2 2 :=
            Nat.log_mono_right hsmall
          _ = 1 := by norm_num
      omega
    have hcutoffPos : 0 < cutoff := by
      have hcutoffReal : 0 < (cutoff : ℝ) :=
        lt_of_le_of_lt (Real.sqrt_nonneg _) hcutoff
      exact_mod_cast hcutoffReal
    have hinitialCard : initial.card ≤ Fintype.card Arm := by
      simpa using Finset.card_le_card (Finset.subset_univ initial)
    have hsize : initial.card ≤ 2 * cutoff := by omega
    have hzero := canonicalFreshStoppedPruneTrace_card_size_cost_and_max_success_probability_of_zero_round_schedule
      preferenceGap hprobability anchor maximum lower upper delta maxBatch cutoff
      (Nat.log 2 (Fintype.card Arm) - 1) hbudget hroundCount initial hsize hmaximum
    calc
      1 - delta ≤ 1 := by linarith
      _ = _ := hzero.symm

/--
Lemma 15's literal probability and stopped comparison envelope at Algorithm
2's integer source cap, including its deterministic small-card boundary.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_of_sourceLemma15
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < Nat.log 2 (Fintype.card Arm) - 1,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta) :
    1 - delta / 2 ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower delta cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            (Nat.log 2 (Fintype.card Arm) - 1) anchor lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (Nat.log 2 (Fintype.card Arm) - 1)
            lower upper delta maxBatch hbudget)
          (Nat.log 2 (Fintype.card Arm) - 1))
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount (Nat.log 2 (Fintype.card Arm) - 1)
            cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
            ∑ round : Fin (Nat.log 2 (Fintype.card Arm) - 1),
              ((cutoff : ℝ) + delta ^ round.val *
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ)) *
                (fixedSampleBudget lower upper
                  (adaptivePruneRoundDelta delta round.val) : ℝ)) := by
  by_cases hlarge : 3 ≤ Fintype.card Arm
  · exact canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_of_sourceLemma15_schedule
      preferenceGap hprobability anchor lower upper delta maxBatch cutoff hbudget initial hanchor hseparation
      hdelta hdeltaHalf hlarge hcutoff hdeltaLower
  · have hsmall : Fintype.card Arm ≤ 2 := by omega
    have hroundCount : Nat.log 2 (Fintype.card Arm) - 1 = 0 := by
      have hlog : Nat.log 2 (Fintype.card Arm) ≤ 1 := by
        calc
          Nat.log 2 (Fintype.card Arm) ≤ Nat.log 2 2 :=
            Nat.log_mono_right hsmall
          _ = 1 := by norm_num
      omega
    have hcutoffPos : 0 < cutoff := by
      have hcutoffReal : 0 < (cutoff : ℝ) :=
        lt_of_le_of_lt (Real.sqrt_nonneg _) hcutoff
      exact_mod_cast hcutoffReal
    have hinitialCard : initial.card ≤ Fintype.card Arm := by
      simpa using Finset.card_le_card (Finset.subset_univ initial)
    have hsize : initial.card ≤ 2 * cutoff := by omega
    exact canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_of_zero_round_schedule
      preferenceGap hprobability anchor lower upper delta maxBatch cutoff
      (Nat.log 2 (Fintype.card Arm) - 1) hbudget hroundCount initial hdelta.le hsize

/--
Lemma 15's source-horizon event carries the sharp finite comparison envelope.
The geometric bad-arm contribution is summed before the probability statement
is formed, so it does not acquire an artificial source-horizon factor.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_of_sourceLemma15_sharpEnvelope
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < Nat.log 2 (Fintype.card Arm) - 1,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta) :
    1 - delta / 2 ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower delta cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            (Nat.log 2 (Fintype.card Arm) - 1) anchor lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (Nat.log 2 (Fintype.card Arm) - 1)
            lower upper delta maxBatch hbudget)
          (Nat.log 2 (Fintype.card Arm) - 1))
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount (Nat.log 2 (Fintype.card Arm) - 1)
            cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
            (2 / (upper - lower) ^ 2) *
              ((cutoff : ℝ) * ((Nat.log 2 (Fintype.card Arm) - 1 : ℕ) : ℝ) *
                  (Real.log (2 / delta) +
                    (((Nat.log 2 (Fintype.card Arm) - 1 : ℕ) : ℝ) + 1) * Real.log 2) +
                ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) *
                  (2 * Real.log (2 / delta) + 6 * Real.log 2)) +
              (((Nat.log 2 (Fintype.card Arm) - 1 : ℕ) : ℝ) * (cutoff : ℝ) +
                2 * ((pruneBadArms preferenceGap lower anchor initial).card : ℝ))) := by
  have hsource := canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_of_sourceLemma15
    preferenceGap hprobability anchor lower upper delta maxBatch cutoff hbudget initial hanchor
      hseparation hdelta hdeltaHalf hcutoff hdeltaLower
  have hresource := pruneComparisonEnvelope_le_sharpGeometricSourceLogEnvelope
    (Nat.log 2 (Fintype.card Arm) - 1) cutoff
    ((pruneBadArms preferenceGap lower anchor initial).card) lower upper delta hdelta hdeltaHalf
  refine hsource.trans (pmfProb_le_of_imp _ _ _ ?_)
  intro stateFailure hsuccess
  exact ⟨hsuccess.1, hsuccess.2.1, hsuccess.2.2.trans hresource⟩

/--
Main Lemma 5 uses the printed confidence lower bound `1 / n ≤ δ`, not the
Supplement Lemma 15 allocation `n' / n ≤ δ`.  The stopped execution is
analyzed with the larger of the actual confidence and the cutoff ratio; this
factor is proof instrumentation only, while every comparison batch still uses
the source schedule generated from `δ`.
-/
noncomputable def sourceLemma5PruneContractionFactor
    (armCount cutoff : ℕ) (delta : ℝ) : ℝ :=
  max delta ((cutoff : ℝ) / (armCount : ℝ))

/--
Main Lemma 5's population-only, ceiling-corrected comparison-rate envelope.
The additive one beside the inverse-gap term is the unavoidable integral
ceiling correction to the source's real-valued `O(n gap⁻² log(1/δ))` display.
-/
noncomputable def sourceLemma5PruneComparisonRateBound
    (armCount : ℕ) (lower upper delta : ℝ) : ℝ :=
  16 * (armCount : ℝ) * (2 / (upper - lower) ^ 2 + 1) *
    (1 + Real.log (1 / delta))

/-- The executed-round geometric envelope implies Main Lemma 5's source rate. -/
theorem two_mul_geometric_pruneComparisonEnvelope_le_sourceLemma5_rateBound
    (roundCount badCount armCount : ℕ) (lower upper delta contraction : ℝ)
    (hbadCount : badCount ≤ armCount)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcontraction : 0 ≤ contraction) (hcontractionHalf : contraction ≤ 1 / 2) :
    ∑ round : Fin roundCount,
      (2 * contraction ^ round.val * (badCount : ℝ)) *
        (fixedSampleBudget lower upper
          (adaptivePruneRoundDelta delta round.val) : ℝ) ≤
      sourceLemma5PruneComparisonRateBound armCount lower upper delta := by
  let sourceFactor : ℝ := 2 / (upper - lower) ^ 2
  let confidenceLog : ℝ := Real.log (1 / delta)
  have hsourceFactorNonnegative : 0 ≤ sourceFactor := by
    dsimp [sourceFactor]
    positivity
  have hconfidenceNonnegative : 0 ≤ confidenceLog := by
    dsimp [confidenceLog]
    apply Real.log_nonneg
    exact (one_le_div₀ hdelta).2 (by linarith)
  have hlogTwoLeOne : Real.log (2 : ℝ) ≤ 1 := by
    apply (Real.exp_le_exp).mp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simpa [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hlogSplit : Real.log (2 / delta) = Real.log 2 + confidenceLog := by
    dsimp [confidenceLog]
    rw [show 2 / delta = 2 * (1 / delta) by field_simp [ne_of_gt hdelta]]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (one_div_ne_zero hdelta.ne')]
  have hsum := two_mul_geometric_pruneComparisonEnvelope_le roundCount badCount
    lower upper delta contraction hdelta hdeltaHalf hcontraction hcontractionHalf
  have hbadCountReal : (badCount : ℝ) ≤ (armCount : ℝ) := by exact_mod_cast hbadCount
  have hinnerNonnegative :
      0 ≤ sourceFactor * (2 * Real.log (2 / delta) + 6 * Real.log 2) + 2 := by
    have hlogGlobal : 0 ≤ Real.log (2 / delta) := by
      apply Real.log_nonneg
      exact (one_le_div₀ hdelta).2 (by linarith)
    positivity
  have hpopulation :
      2 * (badCount : ℝ) *
          (sourceFactor * (2 * Real.log (2 / delta) + 6 * Real.log 2) + 2) ≤
        2 * (armCount : ℝ) *
          (sourceFactor * (2 * Real.log (2 / delta) + 6 * Real.log 2) + 2) := by
    gcongr
  have hscalar :
      2 * (sourceFactor * (2 * Real.log (2 / delta) + 6 * Real.log 2) + 2) ≤
        16 * (sourceFactor + 1) * (1 + confidenceLog) := by
    rw [hlogSplit]
    nlinarith
  calc
    ∑ round : Fin roundCount,
        (2 * contraction ^ round.val * (badCount : ℝ)) *
          (fixedSampleBudget lower upper
            (adaptivePruneRoundDelta delta round.val) : ℝ) ≤
      2 * (badCount : ℝ) *
        (sourceFactor * (2 * Real.log (2 / delta) + 6 * Real.log 2) + 2) := by
          simpa [sourceFactor] using hsum
    _ ≤ 2 * (armCount : ℝ) *
        (sourceFactor * (2 * Real.log (2 / delta) + 6 * Real.log 2) + 2) := hpopulation
    _ = (armCount : ℝ) *
        (2 * (sourceFactor * (2 * Real.log (2 / delta) + 6 * Real.log 2) + 2)) := by
          ring
    _ ≤ (armCount : ℝ) *
        (16 * (sourceFactor + 1) * (1 + confidenceLog)) :=
          mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg _)
    _ = sourceLemma5PruneComparisonRateBound armCount lower upper delta := by
      simp only [sourceLemma5PruneComparisonRateBound, sourceFactor, confidenceLog]
      ring

/--
The raw cardinality-and-cost part of Main Lemma 5.  The comparison schedule
uses `delta`, while the proof-only contraction monitor uses the larger of that
confidence and the cutoff ratio.  Before converting the inverse-square
contraction tail to a confidence budget, the exact failure term is `n⁻²`.

This separation is useful to callers that compose several source phases: they
can charge the inverse-square term only once, against the global confidence
budget, instead of strengthening the confidence passed to Prune.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_ge_one_sub_card_inv_sq_of_sourceLemma5_sharpEnvelope
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcutoffPos : 0 < cutoff)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) ≤ (cutoff : ℝ)) :
    1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower
          (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff delta)
          cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
            lower upper delta maxBatch hbudget)
          (sourcePruneRoundCount (Fintype.card Arm)))
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount (sourcePruneRoundCount (Fintype.card Arm))
            cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
            sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta) := by
  let roundCount := sourcePruneRoundCount (Fintype.card Arm)
  let contraction := sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff delta
  let badCount := (pruneBadArms preferenceGap lower anchor initial).card
  let resourceBound : ℝ :=
    sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta
  have hcardPosNat : 0 < Fintype.card Arm := Fintype.card_pos_iff.mpr ⟨anchor⟩
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcardPosNat
  have hroundCount : roundCount ≤ Fintype.card Arm := by
    simpa [roundCount] using sourcePruneRoundCount_le_card (Fintype.card Arm)
  have hdeltaLeOne : delta ≤ 1 := hdeltaHalf.trans (by norm_num)
  have hlogDelta : 0 ≤ Real.log (1 / delta) := by
    apply Real.log_nonneg
    exact (one_le_div₀ hdelta).2 hdeltaLeOne
  have hresource : 0 ≤ resourceBound := by
    dsimp [resourceBound, sourceLemma5PruneComparisonRateBound]
    positivity
  have hdeterministic (hsize : initial.card ≤ 2 * cutoff) :
      1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
        pmfProb
          (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
              lower upper delta maxBatch hbudget)
            (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
            roundCount)
          (fun stateFailure => stateFailure.2 = false ∧
            stateFailure.1.1.card ≤ 2 * cutoff ∧
            (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
              stateFailure.1.2 : ℝ) ≤ resourceBound) := by
    have hone := freshStoppedPruneTrace_initial_small_success_probability
      preferenceGap lower delta contraction cutoff anchor initial
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
        lower upper delta maxBatch hbudget)
      (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
      roundCount upper resourceBound hsize hresource
    calc
      1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤ 1 := by
        have hinvNonnegative : 0 ≤ 1 / (Fintype.card Arm : ℝ) ^ 2 := by
          positivity
        linarith
      _ = _ := hone.symm
  by_cases hsize : initial.card ≤ 2 * cutoff
  · have hresult := hdeterministic hsize
    simpa [roundCount, contraction, resourceBound, badCount] using hresult
  · have hinitial : initial.card ≤ Fintype.card Arm := by
      simpa using Finset.card_le_card (Finset.subset_univ initial)
    have hcard : 3 ≤ Fintype.card Arm := by omega
    have hratioNonnegative : 0 ≤
        (cutoff : ℝ) / (Fintype.card Arm : ℝ) := by positivity
    have hdeltaLeContraction : delta ≤ contraction := by
      exact le_max_left _ _
    have hratioLeContraction :
        (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ contraction := by
      exact le_max_right _ _
    have hcontraction : 0 < contraction := hdelta.trans_le hdeltaLeContraction
    have hratioHalf : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ 1 / 2 := by
      by_contra hnot
      have hratioGt : 1 / 2 <
          (cutoff : ℝ) / (Fintype.card Arm : ℝ) := lt_of_not_ge hnot
      have hhalfCardLt : (1 / 2 : ℝ) * (Fintype.card Arm : ℝ) < cutoff :=
        (lt_div_iff₀ hcardPos).mp hratioGt
      have hcardLt : (Fintype.card Arm : ℝ) < 2 * (cutoff : ℝ) := by
        nlinarith
      have hcardLeNat : Fintype.card Arm ≤ 2 * cutoff := by
        exact_mod_cast hcardLt.le
      exact hsize (hinitial.trans hcardLeNat)
    have hcontractionHalf : contraction ≤ 1 / 2 :=
      max_le hdeltaHalf hratioHalf
    have htarget := sourceLemma15_source_round_geometric_target
      preferenceGap lower anchor initial cutoff contraction hcard hcutoff hcontraction.le
        hcontractionHalf
    have hcore :=
      canonicalFreshStoppedPruneTrace_card_size_rate_cost_success_probability_ge_one_sub_card_inv_sq_of_schedule_le
        preferenceGap hprobability roundCount anchor lower upper delta contraction maxBatch cutoff
        hbudget initial hanchor hseparation hdelta hdeltaLeOne hcontraction
        hdeltaLeContraction (by omega : 2 ≤ Fintype.card Arm) hroundCount hcutoff
        hratioLeContraction (by simpa [roundCount] using htarget)
    have hbadCount : badCount ≤ Fintype.card Arm := by
      dsimp [badCount, pruneBadArms]
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
        (by simpa using Finset.card_le_card (Finset.subset_univ initial))
    have hgeometricResource :=
      two_mul_geometric_pruneComparisonEnvelope_le_sourceLemma5_rateBound
        roundCount badCount (Fintype.card Arm) lower upper delta contraction hbadCount hdelta
          hdeltaHalf hcontraction.le hcontractionHalf
    have hbounded : 1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
        pmfProb
          (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
              lower upper delta maxBatch hbudget)
            (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
            roundCount)
          (fun stateFailure => stateFailure.2 = false ∧
            stateFailure.1.1.card ≤ 2 * cutoff ∧
            (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
              stateFailure.1.2 : ℝ) ≤ resourceBound) := by
      refine hcore.trans (pmfProb_le_of_imp _ _ _ ?_)
      intro stateFailure hsuccess
      exact ⟨hsuccess.1, hsuccess.2.1, hsuccess.2.2.trans (by
        simpa [resourceBound, badCount] using hgeometricResource)⟩
    simpa [roundCount, contraction, resourceBound, badCount] using hbounded

/--
Main Lemma 5's cardinality and comparison guarantee under its exact displayed
premises.  If the cutoff ratio exceeds one half, the input is already below
the stopping threshold.  Otherwise the maximum of `δ` and `n' / n` gives a
valid at-most-half contraction factor, whose inverse-cubic round tails sum to
at most `n⁻² ≤ δ / 2`.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_of_sourceLemma5_sharpEnvelope
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) ≤ (cutoff : ℝ))
    (hdeltaLower : 1 / (Fintype.card Arm : ℝ) ≤ delta) :
    1 - delta / 2 ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower
          (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff delta)
          cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
            lower upper delta maxBatch hbudget)
          (sourcePruneRoundCount (Fintype.card Arm)))
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount (sourcePruneRoundCount (Fintype.card Arm))
            cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
            sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta) := by
  let roundCount := sourcePruneRoundCount (Fintype.card Arm)
  let contraction := sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff delta
  let badCount := (pruneBadArms preferenceGap lower anchor initial).card
  let resourceBound : ℝ :=
    sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta
  have hcardPosNat : 0 < Fintype.card Arm := Fintype.card_pos_iff.mpr ⟨anchor⟩
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcardPosNat
  have hcard : 2 ≤ Fintype.card Arm := by
    by_contra hnot
    have hcardOne : Fintype.card Arm = 1 := by omega
    have hlower : (1 : ℝ) ≤ delta := by simpa [hcardOne] using hdeltaLower
    linarith
  have hroundCount : roundCount ≤ Fintype.card Arm := by
    simpa [roundCount] using sourcePruneRoundCount_le_card (Fintype.card Arm)
  have hdeltaLeOne : delta ≤ 1 := hdeltaHalf.trans (by norm_num)
  have hlogDelta : 0 ≤ Real.log (1 / delta) := by
    apply Real.log_nonneg
    exact (one_le_div₀ hdelta).2 hdeltaLeOne
  have hresource : 0 ≤ resourceBound := by
    dsimp [resourceBound, sourceLemma5PruneComparisonRateBound]
    positivity
  have hdeterministic (hsize : initial.card ≤ 2 * cutoff) :
      1 - delta / 2 ≤
        pmfProb
          (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
              lower upper delta maxBatch hbudget)
            (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
            roundCount)
          (fun stateFailure => stateFailure.2 = false ∧
            stateFailure.1.1.card ≤ 2 * cutoff ∧
            (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
              stateFailure.1.2 : ℝ) ≤ resourceBound) := by
    have hone := freshStoppedPruneTrace_initial_small_success_probability
      preferenceGap lower delta contraction cutoff anchor initial
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
        lower upper delta maxBatch hbudget)
      (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
      roundCount upper resourceBound hsize hresource
    calc
      1 - delta / 2 ≤ 1 := by linarith
      _ = _ := hone.symm
  by_cases hlarge : 3 ≤ Fintype.card Arm
  · have hratioNonnegative : 0 ≤
        (cutoff : ℝ) / (Fintype.card Arm : ℝ) := by positivity
    have hdeltaLeContraction : delta ≤ contraction := by
      exact le_max_left _ _
    have hratioLeContraction :
        (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ contraction := by
      exact le_max_right _ _
    have hcontraction : 0 < contraction := hdelta.trans_le hdeltaLeContraction
    by_cases hratioHalf : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ 1 / 2
    · have hcontractionHalf : contraction ≤ 1 / 2 :=
        max_le hdeltaHalf hratioHalf
      have htarget := sourceLemma15_source_round_geometric_target
        preferenceGap lower anchor initial cutoff contraction hlarge hcutoff hcontraction.le
          hcontractionHalf
      have hcore :=
        canonicalFreshStoppedPruneTrace_card_size_rate_cost_success_probability_ge_one_sub_card_inv_sq_of_schedule_le
          preferenceGap hprobability roundCount anchor lower upper delta contraction maxBatch cutoff
          hbudget initial hanchor hseparation hdelta hdeltaLeOne hcontraction
          hdeltaLeContraction hcard hroundCount hcutoff hratioLeContraction (by
            simpa [roundCount] using htarget)
      have htail : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤ delta / 2 := by
        have hcardTwo : (2 : ℝ) ≤ (Fintype.card Arm : ℝ) := by exact_mod_cast hcard
        have hinv : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
            (1 / (Fintype.card Arm : ℝ)) / 2 := by
          field_simp [ne_of_gt hcardPos]
          nlinarith
        exact hinv.trans (div_le_div_of_nonneg_right hdeltaLower (by norm_num))
      have hbadCount : badCount ≤ Fintype.card Arm := by
        dsimp [badCount, pruneBadArms]
        exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
          (by simpa using Finset.card_le_card (Finset.subset_univ initial))
      have hgeometricResource :=
        two_mul_geometric_pruneComparisonEnvelope_le_sourceLemma5_rateBound
          roundCount badCount (Fintype.card Arm) lower upper delta contraction hbadCount hdelta
            hdeltaHalf hcontraction.le hcontractionHalf
      have hbounded : 1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
          pmfProb
            (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
              (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
                lower upper delta maxBatch hbudget)
              (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
              roundCount)
            (fun stateFailure => stateFailure.2 = false ∧
              stateFailure.1.1.card ≤ 2 * cutoff ∧
              (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
                stateFailure.1.2 : ℝ) ≤ resourceBound) := by
        refine hcore.trans (pmfProb_le_of_imp _ _ _ ?_)
        intro stateFailure hsuccess
        exact ⟨hsuccess.1, hsuccess.2.1, hsuccess.2.2.trans (by
          simpa [resourceBound, badCount] using hgeometricResource)⟩
      have hresult : 1 - delta / 2 ≤
          pmfProb
            (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
              (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
                lower upper delta maxBatch hbudget)
              (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
              roundCount)
            (fun stateFailure => stateFailure.2 = false ∧
              stateFailure.1.1.card ≤ 2 * cutoff ∧
              (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
                stateFailure.1.2 : ℝ) ≤ resourceBound) := by
        exact (by linarith : 1 - delta / 2 ≤
          1 - 1 / (Fintype.card Arm : ℝ) ^ 2).trans hbounded
      simpa [roundCount, contraction, resourceBound, badCount] using hresult
    · have hratioGt : 1 / 2 <
          (cutoff : ℝ) / (Fintype.card Arm : ℝ) := lt_of_not_ge hratioHalf
      have hhalfCardLt : (1 / 2 : ℝ) * (Fintype.card Arm : ℝ) < cutoff :=
        (lt_div_iff₀ hcardPos).mp hratioGt
      have hcardLt : (Fintype.card Arm : ℝ) < 2 * (cutoff : ℝ) := by nlinarith
      have hcardLeNat : Fintype.card Arm ≤ 2 * cutoff := by exact_mod_cast hcardLt.le
      have hinitial : initial.card ≤ Fintype.card Arm := by
        simpa using Finset.card_le_card (Finset.subset_univ initial)
      have hresult := hdeterministic (hinitial.trans hcardLeNat)
      simpa [roundCount, contraction, resourceBound, badCount] using hresult
  · have hsmall : Fintype.card Arm ≤ 2 := by omega
    have hinsidePositive : 0 <
        6 * (Fintype.card Arm : ℝ) * Real.log (Fintype.card Arm : ℝ) := by
      exact mul_pos (mul_pos (by norm_num) hcardPos)
        (Real.log_pos (by exact_mod_cast hcard))
    have hcutoffPosReal : 0 < (cutoff : ℝ) :=
      (Real.sqrt_pos.2 hinsidePositive).trans_le hcutoff
    have hcutoffPos : 0 < cutoff := by exact_mod_cast hcutoffPosReal
    have hinitial : initial.card ≤ Fintype.card Arm := by
      simpa using Finset.card_le_card (Finset.subset_univ initial)
    have hsize : initial.card ≤ 2 * cutoff := by omega
    have hresult := hdeterministic hsize
    simpa [roundCount, contraction, resourceBound, badCount] using hresult

/--
Main Lemma 5 on the actual source trace.  The finite batch-storage witness and
the contraction monitor are constructed internally and erased from the
published event.
-/
theorem canonicalFreshStoppedPruneTrace_sourceLemma5_size_cost_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor : Arm) (lower upper delta : ℝ) (cutoff : ℕ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) ≤ (cutoff : ℝ))
    (hdeltaLower : 1 / (Fintype.card Arm : ℝ) ≤ delta) :
    1 - delta / 2 ≤
      pmfProb
        (freshStoppedPruneTraceLaw cutoff (Finset.univ : Finset Arm)
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper delta
            (sourcePruneMaxBatch (Arm := Arm) lower upper delta)
            (fixedSampleBudget_le_sourcePruneMaxBatch_of_source_round lower upper delta))
          (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
            lower upper delta (sourcePruneMaxBatch (Arm := Arm) lower upper delta)
            (fixedSampleBudget_le_sourcePruneMaxBatch_of_source_round lower upper delta))
          (sourcePruneRoundCount (Fintype.card Arm)))
        (fun state => state.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount (sourcePruneRoundCount (Fintype.card Arm))
            cutoff lower upper delta state.2 : ℝ) ≤
            sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta) := by
  let roundCount := sourcePruneRoundCount (Fintype.card Arm)
  let maxBatch := sourcePruneMaxBatch (Arm := Arm) lower upper delta
  let hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch :=
    fixedSampleBudget_le_sourcePruneMaxBatch_of_source_round lower upper delta
  let contraction := sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff delta
  let outcomeLaw := canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
    lower upper delta maxBatch hbudget
  let decision := canonicalFreshPruneDecision (Arm := Arm) roundCount lower upper delta maxBatch
    hbudget
  let sourceEvent : stoppedPruneTraceState Arm roundCount → Prop := fun state =>
    state.1.card ≤ 2 * cutoff ∧
      (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta state.2 : ℝ) ≤
        sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta
  have hflagged :=
    canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_of_sourceLemma5_sharpEnvelope
      preferenceGap hprobability anchor lower upper delta maxBatch cutoff hbudget Finset.univ
      hanchor hseparation hdelta hdeltaHalf hcutoff hdeltaLower
  calc
    1 - delta / 2 ≤
        pmfProb
          (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor Finset.univ
            outcomeLaw decision roundCount)
          (fun stateFailure => stateFailure.2 = false ∧ sourceEvent stateFailure.1) := by
            simpa [roundCount, maxBatch, hbudget, contraction, outcomeLaw, decision, sourceEvent]
              using hflagged
    _ ≤ pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor Finset.univ
          outcomeLaw decision roundCount)
        (fun stateFailure => sourceEvent stateFailure.1) := by
          apply pmfProb_le_of_imp
          intro stateFailure hsuccess
          exact hsuccess.2
    _ = pmfProb
        ((freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor Finset.univ
          outcomeLaw decision roundCount).map Prod.fst) sourceEvent := by
          symm
          exact pmfProb_map _ _ _
    _ = pmfProb (freshStoppedPruneTraceLaw cutoff Finset.univ outcomeLaw decision roundCount)
        sourceEvent := by
          rw [freshStoppedPruneTraceStateLaw_map_traceLaw]
    _ = _ := by
      rfl

/--
Maximum retention for the actual stopped Prune execution under an arbitrary
finite source schedule.  This theorem deliberately mentions neither the
proof-only contraction monitor nor a cardinality event: retention depends only
on the comparisons actually sampled by the algorithm.
-/
theorem canonicalFreshStoppedPruneActive_maximum_probability_of_schedule
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor maximum : Arm) (lower upper delta : ℝ)
    (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm) (hmaximum : maximum ∈ initial)
    (hgap : upper ≤ preferenceGap maximum anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    1 - delta / 2 ≤
      pmfProb
        (freshStoppedPruneActiveLaw initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper delta maxBatch hbudget)
          cutoff
          (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
          roundCount)
        (fun active => maximum ∈ active) := by
  let outcomeLaw := canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
    lower upper delta maxBatch hbudget
  let decision := canonicalFreshPruneDecision (Arm := Arm) roundCount lower upper delta maxBatch
    hbudget
  let failureBudget : ℕ → ℝ := fun round =>
    if round < roundCount then adaptivePruneRoundDelta delta round else 1
  have hfailure : ∀ round active,
      pmfProb (outcomeLaw round active) (fun outcome =>
        ¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
          decision round active outcome maximum ≠ .upper) ≤ failureBudget round := by
    intro round active
    by_cases hround : round < roundCount
    · have hretention :=
        canonicalFreshPruneRound_upper_failure_probability preferenceGap hprobability roundCount
          anchor lower upper delta maxBatch hbudget round hround active maximum hgap hseparation
          hdelta hdeltaLeOne
      calc
        pmfProb (outcomeLaw round active) (fun outcome =>
            ¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
              decision round active outcome maximum ≠ .upper) ≤
            pmfProb (outcomeLaw round active) (fun outcome =>
              decision round active outcome maximum ≠ .upper) := by
                apply pmfProb_le_of_imp
                intro outcome hbad
                exact hbad.2.2
        _ ≤ adaptivePruneRoundDelta delta round := by
          simpa [outcomeLaw, decision] using hretention
        _ = failureBudget round := by simp [failureBudget, hround]
    · simpa [failureBudget, hround] using pmfProb_le_one (outcomeLaw round active)
        (fun outcome =>
          ¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
            decision round active outcome maximum ≠ .upper)
  have hretention := freshStoppedPruneActive_maximum_probability_ge_one_sub_sum cutoff maximum
    initial outcomeLaw decision failureBudget roundCount hmaximum hfailure
  have hsum : ∑ round ∈ Finset.range roundCount, failureBudget round ≤ delta / 2 := by
    simpa only [failureBudget, Finset.sum_congr rfl (fun round hround =>
      if_pos (Finset.mem_range.mp hround))] using
      adaptivePruneRoundDelta_sum_le_half delta hdelta.le roundCount
  calc
    1 - delta / 2 ≤ 1 - ∑ round ∈ Finset.range roundCount, failureBudget round := by
      linarith
    _ ≤ pmfProb (freshStoppedPruneActiveLaw initial outcomeLaw cutoff decision roundCount)
        (fun active => maximum ∈ active) := hretention
    _ = _ := by rfl

/--
The raw joint Prune event needed by Algorithm 3.  The inverse-square
contraction tail and the comparison-schedule retention tail are kept as
separate terms until the caller allocates the global confidence budget.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_and_max_probability_ge_raw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor maximum : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hmaximum : maximum ∈ initial) (hgap : upper ≤ preferenceGap maximum anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcutoffPos : 0 < cutoff)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) ≤ (cutoff : ℝ)) :
    1 - (1 / (Fintype.card Arm : ℝ) ^ 2 + delta / 2) ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower
          (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff delta)
          cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
            lower upper delta maxBatch hbudget)
          (sourcePruneRoundCount (Fintype.card Arm)))
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount (sourcePruneRoundCount (Fintype.card Arm))
            cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
            sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta ∧
          maximum ∈ stateFailure.1.1) := by
  let roundCount := sourcePruneRoundCount (Fintype.card Arm)
  let contraction := sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff delta
  let outcomeLaw := canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
    lower upper delta maxBatch hbudget
  let decision := canonicalFreshPruneDecision (Arm := Arm) roundCount lower upper delta maxBatch
    hbudget
  let traceLaw := freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor
    initial outcomeLaw decision roundCount
  let sizeCostEvent : stoppedPruneTraceState Arm roundCount × Bool → Prop := fun stateFailure =>
    stateFailure.2 = false ∧ stateFailure.1.1.card ≤ 2 * cutoff ∧
      (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
        stateFailure.1.2 : ℝ) ≤
        sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta
  let maximumEvent : stoppedPruneTraceState Arm roundCount × Bool → Prop := fun stateFailure =>
    maximum ∈ stateFailure.1.1
  have hsizeCost : 1 - 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
      pmfProb traceLaw sizeCostEvent := by
    simpa [roundCount, contraction, outcomeLaw, decision, traceLaw, sizeCostEvent] using
      (canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_ge_one_sub_card_inv_sq_of_sourceLemma5_sharpEnvelope
        preferenceGap hprobability anchor lower upper delta maxBatch cutoff hbudget initial
        hanchor hseparation hdelta hdeltaHalf hcutoffPos hcutoff)
  have hretention : 1 - delta / 2 ≤ pmfProb traceLaw maximumEvent := by
    have hactive := canonicalFreshStoppedPruneActive_maximum_probability_of_schedule
      preferenceGap hprobability roundCount anchor maximum lower upper delta maxBatch cutoff
      hbudget initial hmaximum hgap hseparation hdelta (hdeltaHalf.trans (by norm_num))
    calc
      1 - delta / 2 ≤
          pmfProb (freshStoppedPruneActiveLaw initial outcomeLaw cutoff decision roundCount)
            (fun active => maximum ∈ active) := by
              simpa [outcomeLaw, decision] using hactive
      _ = pmfProb (traceLaw.map (fun stateFailure => stateFailure.1.1))
          (fun active => maximum ∈ active) := by
            rw [freshStoppedPruneTraceStateLaw_map_activeLaw preferenceGap lower contraction
              cutoff anchor initial outcomeLaw decision roundCount]
      _ = pmfProb traceLaw maximumEvent := by
            rw [pmfProb_map]
  have hintersection := pmfProb_inter_ge_one_sub_add traceLaw sizeCostEvent maximumEvent
    hsizeCost hretention
  calc
    1 - (1 / (Fintype.card Arm : ℝ) ^ 2 + delta / 2) =
        1 - 1 / (Fintype.card Arm : ℝ) ^ 2 - delta / 2 := by ring
    _ ≤ pmfProb traceLaw (fun stateFailure =>
        sizeCostEvent stateFailure ∧ maximumEvent stateFailure) := hintersection
    _ ≤ pmfProb traceLaw (fun stateFailure => stateFailure.2 = false ∧
        stateFailure.1.1.card ≤ 2 * cutoff ∧
        (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
          stateFailure.1.2 : ℝ) ≤
          sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta ∧
        maximum ∈ stateFailure.1.1) := by
          apply pmfProb_le_of_imp
          intro stateFailure hsuccess
          exact ⟨hsuccess.1.1, hsuccess.1.2.1, hsuccess.1.2.2, hsuccess.2⟩
    _ = _ := by rfl

/--
When Prune's input already satisfies the stopping threshold, the joint
size/resource/retention event is deterministic.  This is the zero-failure
branch used by callers that keep the contraction tail explicit.
-/
theorem canonicalFreshStoppedPruneTrace_card_size_cost_and_max_probability_eq_one_of_initial_small
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor maximum : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hsize : initial.card ≤ 2 * cutoff) (hmaximum : maximum ∈ initial) :
    pmfProb
      (freshStoppedPruneTraceStateLaw preferenceGap lower
        (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff delta)
        cutoff anchor initial
        (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
          (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper delta maxBatch hbudget)
        (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
          lower upper delta maxBatch hbudget)
        (sourcePruneRoundCount (Fintype.card Arm)))
      (fun stateFailure => stateFailure.2 = false ∧
        stateFailure.1.1.card ≤ 2 * cutoff ∧
        (stoppedPruneTraceComparisonCount (sourcePruneRoundCount (Fintype.card Arm))
          cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
          sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta ∧
        maximum ∈ stateFailure.1.1) = 1 := by
  let roundCount := sourcePruneRoundCount (Fintype.card Arm)
  let contraction := sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff delta
  let outcomeLaw := canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
    lower upper delta maxBatch hbudget
  let decision := canonicalFreshPruneDecision (Arm := Arm) roundCount lower upper delta maxBatch
    hbudget
  let resourceBound := sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta
  have hresource : 0 ≤ resourceBound := by
    have hlog : 0 ≤ Real.log (1 / delta) := by
      exact Real.log_nonneg ((one_le_div₀ hdelta).2 hdeltaLeOne)
    dsimp [resourceBound, sourceLemma5PruneComparisonRateBound]
    positivity
  have hstrong := freshStoppedPruneTrace_initial_small_state_success_probability
    preferenceGap lower delta contraction cutoff anchor initial outcomeLaw decision roundCount upper
    resourceBound hsize hresource
  apply le_antisymm (pmfProb_le_one _ _)
  calc
    1 = pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
          outcomeLaw decision roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1 = initial ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
            stateFailure.1.2 : ℝ) ≤ resourceBound) := hstrong.symm
    _ ≤ pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower contraction cutoff anchor initial
          outcomeLaw decision roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta
            stateFailure.1.2 : ℝ) ≤ resourceBound ∧
          maximum ∈ stateFailure.1.1) := by
      apply pmfProb_le_of_imp
      intro stateFailure hsuccess
      exact ⟨hsuccess.1, hsuccess.2.2.1, hsuccess.2.2.2,
        hsuccess.2.1.symm ▸ hmaximum⟩
    _ = _ := by rfl

/-- Main Lemma 5's retention clause on the actual canonical Prune output law. -/
theorem canonicalFreshStoppedPruneActive_sourceLemma5_maximum_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor : Arm) (lower upper delta : ℝ) (cutoff : ℕ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hupperNonnegative : 0 ≤ upper)
    (hanchorNotMaximum : ¬ EpsilonMaximum preferenceGap upper anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    1 - delta / 2 ≤
      pmfProbClassical
        (freshStoppedPruneActiveLaw (Finset.univ : Finset Arm)
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper delta
            (sourcePruneMaxBatch (Arm := Arm) lower upper delta)
            (fixedSampleBudget_le_sourcePruneMaxBatch_of_source_round lower upper delta))
          cutoff
          (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
            lower upper delta (sourcePruneMaxBatch (Arm := Arm) lower upper delta)
            (fixedSampleBudget_le_sourcePruneMaxBatch_of_source_round lower upper delta))
          (sourcePruneRoundCount (Fintype.card Arm)))
        (fun active => ∃ maximum, AbsoluteMaximum preferenceGap maximum ∧ maximum ∈ active) := by
  classical
  let roundCount := sourcePruneRoundCount (Fintype.card Arm)
  let maxBatch := sourcePruneMaxBatch (Arm := Arm) lower upper delta
  let hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch :=
    fixedSampleBudget_le_sourcePruneMaxBatch_of_source_round lower upper delta
  let outcomeLaw := canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
    lower upper delta maxBatch hbudget
  let decision := canonicalFreshPruneDecision (Arm := Arm) roundCount lower upper delta maxBatch
    hbudget
  let failureBudget : ℕ → ℝ := fun round =>
    if round < roundCount then adaptivePruneRoundDelta delta round else 1
  letI : Nonempty Arm := ⟨anchor⟩
  let hcomplete := preferenceComplete_of_antisymmetric preferenceGap hantisymmetric
  rcases exists_absoluteMaximum_of_preferenceComplete_sst preferenceGap hcomplete hsst with
    ⟨maximum, hmaximum⟩
  have hgap : upper ≤ preferenceGap maximum anchor :=
    (absoluteMaximum_gap_gt_of_not_epsilonMaximum preferenceGap upper hantisymmetric hsst
      hupperNonnegative maximum anchor hmaximum hanchorNotMaximum).le
  have hfailure : ∀ round active,
      pmfProb (outcomeLaw round active) (fun outcome =>
        ¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
          decision round active outcome maximum ≠ .upper) ≤ failureBudget round := by
    intro round active
    by_cases hround : round < roundCount
    · have hretention :=
        canonicalFreshPruneRound_upper_failure_probability preferenceGap hprobability roundCount
          anchor lower upper delta maxBatch hbudget round hround active maximum hgap hseparation
          hdelta hdeltaLeOne
      calc
        pmfProb (outcomeLaw round active) (fun outcome =>
            ¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
              decision round active outcome maximum ≠ .upper) ≤
            pmfProb (outcomeLaw round active) (fun outcome =>
              decision round active outcome maximum ≠ .upper) := by
                apply pmfProb_le_of_imp
                intro outcome hbad
                exact hbad.2.2
        _ ≤ adaptivePruneRoundDelta delta round := by
          simpa [outcomeLaw, decision] using hretention
        _ = failureBudget round := by simp [failureBudget, hround]
    · simpa [failureBudget, hround] using pmfProb_le_one (outcomeLaw round active)
        (fun outcome =>
          ¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
            decision round active outcome maximum ≠ .upper)
  have hretention := freshStoppedPruneActive_maximum_probability_ge_one_sub_sum cutoff maximum
    (Finset.univ : Finset Arm) outcomeLaw decision failureBudget roundCount (by simp) hfailure
  have hsum : ∑ round ∈ Finset.range roundCount, failureBudget round ≤ delta / 2 := by
    simpa only [failureBudget, Finset.sum_congr rfl (fun round hround =>
      if_pos (Finset.mem_range.mp hround))] using
      adaptivePruneRoundDelta_sum_le_half delta hdelta.le roundCount
  have hmaximumEvent :
      pmfProb (freshStoppedPruneActiveLaw (Finset.univ : Finset Arm) outcomeLaw cutoff decision
          roundCount) (fun active => maximum ∈ active) ≤
        pmfProbClassical (freshStoppedPruneActiveLaw (Finset.univ : Finset Arm) outcomeLaw cutoff decision
          roundCount) (fun active => ∃ selected, AbsoluteMaximum preferenceGap selected ∧
            selected ∈ active) := by
    rw [pmfProbClassical_eq_pmfProb]
    apply pmfProb_le_of_imp
    intro active hmem
    exact ⟨maximum, hmaximum, hmem⟩
  calc
    1 - delta / 2 ≤ 1 - ∑ round ∈ Finset.range roundCount, failureBudget round := by linarith
    _ ≤ pmfProb (freshStoppedPruneActiveLaw (Finset.univ : Finset Arm) outcomeLaw cutoff decision
        roundCount) (fun active => maximum ∈ active) := hretention
    _ ≤ pmfProbClassical (freshStoppedPruneActiveLaw (Finset.univ : Finset Arm) outcomeLaw cutoff decision
        roundCount) (fun active => ∃ selected, AbsoluteMaximum preferenceGap selected ∧
          selected ∈ active) := hmaximumEvent
    _ = _ := by rfl

end FalahatgarEtAl2017MaxingRanking
