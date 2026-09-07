import ZhouChenLi2014OptimalPACMultipleArm.CoreDefinitions
import AppliedModelingLib.Foundations.Probability.IndependentProduct

/-!
# Fixed finite Bernoulli policies

A static product batch can be replayed as a finite adaptive Bernoulli policy
whose next pull ignores its reward history.  This file proves the exact PMF
identity, rather than assuming that a batch and a sequential experiment have
the same law.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib
open scoped BigOperators

/-- A finite policy whose pull at each round is fixed in advance. -/
noncomputable def fixedBernoulliProcedure {Arm : Type*} {pullBudget : ℕ}
    (schedule : Fin pullBudget → Arm) (output : (Fin pullBudget → Bool) → Arm) :
    FiniteAdaptiveBernoulliBestArmProcedure Arm pullBudget where
  pull := fun round _history => schedule round
  output := output

/-- Restrict a fixed schedule to an earlier finite prefix. -/
def fixedSchedulePrefix {Arm : Type*} {pullBudget roundCount : ℕ}
    (schedule : Fin pullBudget → Arm) (hroundCount : roundCount ≤ pullBudget) :
    Fin roundCount → Arm := fun round =>
  schedule ⟨round.val, Nat.lt_of_lt_of_le round.isLt hroundCount⟩

@[simp]
theorem fixedSchedulePrefix_castSucc {Arm : Type*} {pullBudget roundCount : ℕ}
    (schedule : Fin pullBudget → Arm) (hroundCount : roundCount + 1 ≤ pullBudget)
    (round : Fin roundCount) :
    fixedSchedulePrefix schedule hroundCount round.castSucc =
      fixedSchedulePrefix schedule (Nat.le_of_succ_le hroundCount) round := rfl

@[simp]
theorem fixedSchedulePrefix_last {Arm : Type*} {pullBudget roundCount : ℕ}
    (schedule : Fin pullBudget → Arm) (hroundCount : roundCount + 1 ≤ pullBudget) :
    fixedSchedulePrefix schedule hroundCount (Fin.last roundCount) =
      schedule ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩ := rfl

/-- Appending a binary response to a fixed history has a unique preimage. -/
private lemma pmfMapSnoc_apply
    {roundCount : ℕ} (response : PMF Bool)
    (history target : Fin roundCount → Bool) (outcome : Bool) :
    PMF.map (fun responseOutcome => Fin.snoc history responseOutcome) response
      (@Fin.snoc roundCount (fun _ => Bool) target outcome) =
        if target = history then response outcome else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  simp only [Fin.snoc_inj]
  by_cases htarget : target = history
  · subst target
    cases outcome <;> simp
  · simp [htarget]

/-- The product of conditional response masses along a fixed finite schedule. -/
noncomputable def fixedBernoulliRewardPrefixMass
    {Arm : Type*} {pullBudget : ℕ} (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (schedule : Fin pullBudget → Arm) :
    (roundCount : ℕ) → (hroundCount : roundCount ≤ pullBudget) →
      (Fin roundCount → Bool) → ENNReal
  | 0, _, _ => 1
  | roundCount + 1, hroundCount, rewards =>
      fixedBernoulliRewardPrefixMass mean hmean schedule roundCount
        (Nat.le_of_succ_le hroundCount) (Fin.init rewards) *
        (bernoulliRewardLaw mean hmean
          (schedule ⟨roundCount, Nat.lt_of_succ_le hroundCount⟩))
          (rewards (Fin.last roundCount))

/-- The atom mass of a fixed policy's prefix trace is its sequential product. -/
theorem adaptiveFixedBernoulliRewardPrefixLaw_apply
    {Arm : Type*} {pullBudget : ℕ} (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (schedule : Fin pullBudget → Arm) (output : (Fin pullBudget → Bool) → Arm) :
    ∀ (roundCount : ℕ) (hroundCount : roundCount ≤ pullBudget)
      (rewards : Fin roundCount → Bool),
      adaptiveBernoulliRewardPrefixLaw mean hmean
        (fixedBernoulliProcedure schedule output) roundCount hroundCount rewards =
        fixedBernoulliRewardPrefixMass mean hmean schedule roundCount hroundCount rewards := by
  intro roundCount
  induction roundCount with
  | zero =>
      intro _ rewards
      have hrewards : rewards = Fin.elim0 := Subsingleton.elim _ _
      subst rewards
      simp [adaptiveBernoulliRewardPrefixLaw, fixedBernoulliRewardPrefixMass]
  | succ roundCount ih =>
      intro hroundCount rewards
      cases rewards using Fin.snocCases with
      | snoc history outcome =>
          rw [adaptiveBernoulliRewardPrefixLaw, PMF.bind_apply, tsum_fintype]
          simp_rw [pmfMapSnoc_apply]
          rw [Finset.sum_eq_single history]
          · rw [ih (Nat.le_of_succ_le hroundCount) history]
            simp [fixedBernoulliRewardPrefixMass, fixedBernoulliProcedure]
          · intro other _ hother
            simp [hother.symm]
          · simp

/-- The sequential mass of a fixed schedule is its finite independent product mass. -/
theorem fixedBernoulliRewardPrefixMass_eq_pmfPi
    {Arm : Type*} {pullBudget : ℕ} (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (schedule : Fin pullBudget → Arm) :
    ∀ (roundCount : ℕ) (hroundCount : roundCount ≤ pullBudget)
      (rewards : Fin roundCount → Bool),
      fixedBernoulliRewardPrefixMass mean hmean schedule roundCount hroundCount rewards =
        pmfPi (fun round : Fin roundCount =>
          bernoulliRewardLaw mean hmean (fixedSchedulePrefix schedule hroundCount round)) rewards := by
  intro roundCount
  induction roundCount with
  | zero =>
      intro _ rewards
      have hrewards : rewards = Fin.elim0 := Subsingleton.elim _ _
      subst rewards
      simp [fixedBernoulliRewardPrefixMass, pmfPi_apply]
  | succ roundCount ih =>
      intro hroundCount rewards
      cases rewards using Fin.snocCases with
      | snoc history outcome =>
          rw [fixedBernoulliRewardPrefixMass, pmfPi_apply, Fin.prod_univ_castSucc]
          simp only [Fin.init_snoc, Fin.snoc_castSucc, Fin.snoc_last]
          rw [ih (Nat.le_of_succ_le hroundCount) history]
          simp only [pmfPi_apply, fixedSchedulePrefix_castSucc, fixedSchedulePrefix_last]

/-- Every finite prefix of a fixed Bernoulli schedule has the corresponding
independent coordinate-product law. -/
theorem adaptiveFixedBernoulliRewardPrefixLaw_eq_pmfPi
    {Arm : Type*} {pullBudget roundCount : ℕ}
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (schedule : Fin pullBudget → Arm) (output : (Fin pullBudget → Bool) → Arm)
    (hroundCount : roundCount ≤ pullBudget) :
    adaptiveBernoulliRewardPrefixLaw mean hmean
      (fixedBernoulliProcedure schedule output) roundCount hroundCount =
      pmfPi (fun round : Fin roundCount =>
        bernoulliRewardLaw mean hmean (fixedSchedulePrefix schedule hroundCount round)) := by
  apply PMF.ext
  intro rewards
  rw [adaptiveFixedBernoulliRewardPrefixLaw_apply]
  exact fixedBernoulliRewardPrefixMass_eq_pmfPi mean hmean schedule roundCount hroundCount rewards

/--
The complete trace law of a fixed pull schedule is exactly the product PMF of
the scheduled Bernoulli coordinate laws.
-/
theorem adaptiveFixedBernoulliRewardLaw_eq_pmfPi
    {Arm : Type*} {pullBudget : ℕ} (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (schedule : Fin pullBudget → Arm) (output : (Fin pullBudget → Bool) → Arm) :
    adaptiveBernoulliRewardLaw mean hmean (fixedBernoulliProcedure schedule output) =
      pmfPi (fun round : Fin pullBudget => bernoulliRewardLaw mean hmean (schedule round)) := by
  apply PMF.ext
  intro rewards
  rw [adaptiveBernoulliRewardLaw]
  rw [adaptiveFixedBernoulliRewardPrefixLaw_apply]
  simpa [fixedSchedulePrefix] using
    (fixedBernoulliRewardPrefixMass_eq_pmfPi mean hmean schedule pullBudget (le_refl _)
      rewards)

end ZhouChenLi2014OptimalPACMultipleArm
