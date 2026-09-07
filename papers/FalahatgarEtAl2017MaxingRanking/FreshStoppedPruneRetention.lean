import FalahatgarEtAl2017MaxingRanking.FreshStoppedPruneRounds

/-!
# Joint retention and contraction for stopped fresh Prune

The source's Lemma 17 needs one execution of Algorithm 2 on which both the
geometric bad-arm contraction and preservation of a high-gap maximum hold.
This module puts those two historywise bad events in one Boolean flag, so the
final cardinality and retention facts are genuinely statements about the same
finite adaptive PMF.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- Finite-PMF union bound for two decidable event predicates. -/
theorem pmfProb_or_le {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (first second : Outcome → Prop)
    [DecidablePred first] [DecidablePred second] :
    pmfProb law (fun outcome => first outcome ∨ second outcome) ≤
      pmfProb law first + pmfProb law second := by
  calc
    pmfProb law (fun outcome => first outcome ∨ second outcome) =
        pmfExp law (fun outcome =>
          if first outcome ∨ second outcome then (1 : ℝ) else 0) := rfl
    _ ≤ pmfExp law (fun outcome =>
        (if first outcome then (1 : ℝ) else 0) +
          (if second outcome then (1 : ℝ) else 0)) := by
            apply pmfExp_le_pmfExp_of_forall_le
            intro outcome
            by_cases hfirst : first outcome <;> by_cases hsecond : second outcome <;>
              simp [hfirst, hsecond]
    _ = pmfProb law first + pmfProb law second := by
          rw [pmfExp_add]
          rfl

/-- The state marginal of a finite adaptive query execution, with no failure flag. -/
noncomputable def adaptiveQueryActiveLaw
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) : ℕ → PMF State
  | 0 => initialStateLaw
  | queryCount + 1 =>
      (adaptiveQueryActiveLaw initialStateLaw outcomeLaw advance queryCount).bind
        fun state => (outcomeLaw queryCount state).map fun outcome =>
          advance queryCount state outcome

/--
The active-state marginal is independent of which historywise event is stored
in the Boolean failure flag.  This permits a single actual Prune state law to
reuse the separate contraction and retention analyses without treating them as
different executions.
-/
theorem adaptiveQueryStateLaw_map_fst_eq_activeLaw
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)] :
    ∀ queryCount,
      (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).map Prod.fst =
        adaptiveQueryActiveLaw initialStateLaw outcomeLaw advance queryCount := by
  intro queryCount
  induction queryCount with
  | zero =>
      rw [adaptiveQueryStateLaw, adaptiveQueryActiveLaw]
      simp_rw [PMF.map_comp]
      have hid : Prod.fst ∘ (fun state : State => (state, false)) = id := by
        funext state
        rfl
      rw [hid]
      exact PMF.map_id initialStateLaw
  | succ queryCount ih =>
      rw [adaptiveQueryStateLaw, adaptiveQueryActiveLaw, PMF.map_bind]
      simp_rw [PMF.map_comp]
      change
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).bind
          (fun stateFailure =>
            (outcomeLaw queryCount stateFailure.1).map fun outcome =>
              advance queryCount stateFailure.1 outcome) =
          (adaptiveQueryActiveLaw initialStateLaw outcomeLaw advance queryCount).bind
            (fun state =>
              (outcomeLaw queryCount state).map fun outcome => advance queryCount state outcome)
      let step : State → PMF State := fun state =>
        (outcomeLaw queryCount state).map fun outcome => advance queryCount state outcome
      have hkernel : (fun stateFailure : State × Bool =>
          (outcomeLaw queryCount stateFailure.1).map fun outcome =>
            advance queryCount stateFailure.1 outcome) = step ∘ Prod.fst := by
        rfl
      rw [hkernel, ← PMF.bind_map, ih]

/-- The actual active-set law of stopped Prune, with bookkeeping flags erased. -/
noncomputable def freshStoppedPruneActiveLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (cutoff : ℕ) (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (roundCount : ℕ) : PMF (Finset Arm) :=
  adaptiveQueryActiveLaw (PMF.pure initial) outcomeLaw (stoppedPruneAdvance cutoff decision) roundCount

/--
Maximum retention on the actual stopped-Prune active-set law.  The Boolean
failure process is proof-only and is erased from the conclusion.
-/
theorem freshStoppedPruneActive_maximum_probability_ge_one_sub_sum
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (cutoff : ℕ) (maximum : Arm) (initial : Finset Arm)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (failureBudget : ℕ → ℝ) (roundCount : ℕ)
    (hmaximum : maximum ∈ initial)
    (hfailure : ∀ round active,
      pmfProb (outcomeLaw round active) (fun outcome =>
        ¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
          decision round active outcome maximum ≠ .upper) ≤ failureBudget round) :
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      pmfProb (freshStoppedPruneActiveLaw initial outcomeLaw cutoff decision roundCount)
        (fun active => maximum ∈ active) := by
  classical
  let advance : AdaptiveStateUpdate (Finset Arm) Outcome := stoppedPruneAdvance cutoff decision
  let bad : ℕ → Finset Arm → Outcome → Prop := fun round active outcome =>
    ¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
      decision round active outcome maximum ≠ .upper
  let invariant : ℕ → Finset Arm → Bool → Prop := fun _ active flag =>
    flag = false → maximum ∈ active
  have hinitial : ∀ active ∈ (PMF.pure initial).support, invariant 0 active false := by
    intro active hactive _
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hactive
    subst active
    exact hmaximum
  have hadvance : ∀ round active flag outcome,
      invariant round active flag →
      invariant (round + 1) (advance round active outcome)
        (flag || decide (bad round active outcome)) := by
    intro round active flag outcome hinvariant hnextFlag
    have hflag : flag = false := (Bool.or_eq_false_iff.mp hnextFlag).1
    have hbadFalse : decide (bad round active outcome) = false :=
      (Bool.or_eq_false_iff.mp hnextFlag).2
    have hnotBad : ¬ bad round active outcome := by simpa using hbadFalse
    have hmax : maximum ∈ active := hinvariant hflag
    by_cases hstopped : active.card ≤ 2 * cutoff
    · simpa [advance, stoppedPruneAdvance, hstopped] using hmax
    · have hupper : decision round active outcome maximum = .upper := by
        by_contra hnotUpper
        exact hnotBad ⟨hstopped, hmax, hnotUpper⟩
      simpa [advance, stoppedPruneAdvance, hstopped] using
        mem_pruneRound_of_upper active (decision round active outcome) maximum hmax hupper
  have hinvariantSupport := adaptiveQueryStateLaw_support_invariant
    (PMF.pure initial) outcomeLaw advance bad invariant hinitial hadvance
  have hsuccess := adaptiveQuerySuccessProbability_ge_one_sub_sum
    (PMF.pure initial) outcomeLaw advance bad failureBudget (by
      intro round active
      simpa [bad] using hfailure round active) roundCount
  have hequal :
      pmfProb (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount)
          (fun stateFailure => stateFailure.2 = false) =
        pmfProb (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount)
          (fun stateFailure => stateFailure.2 = false ∧ maximum ∈ stateFailure.1) := by
    apply pmfProb_eq_of_support_iff
    intro stateFailure hsupport
    constructor
    · intro hflag
      exact ⟨hflag, hinvariantSupport roundCount stateFailure hsupport hflag⟩
    · exact fun h => h.1
  calc
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
        pmfProb (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount)
          (fun stateFailure => stateFailure.2 = false) := hsuccess
    _ = pmfProb (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount)
          (fun stateFailure => stateFailure.2 = false ∧ maximum ∈ stateFailure.1) := hequal
    _ ≤ pmfProb (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount)
          (fun stateFailure => maximum ∈ stateFailure.1) := by
            apply pmfProb_le_of_imp
            intro stateFailure hstate
            exact hstate.2
    _ = pmfProb
          ((adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount).map Prod.fst)
          (fun active => maximum ∈ active) := by
            rw [pmfProb_map]
    _ = pmfProb (freshStoppedPruneActiveLaw initial outcomeLaw cutoff decision roundCount)
          (fun active => maximum ∈ active) := by
            rw [show
              (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount).map
                  Prod.fst =
                freshStoppedPruneActiveLaw initial outcomeLaw cutoff decision roundCount by
              simpa only [advance, bad, freshStoppedPruneActiveLaw] using
                (adaptiveQueryStateLaw_map_fst_eq_activeLaw (PMF.pure initial) outcomeLaw advance
                  bad roundCount)]

/--
The stopped fresh Prune law whose flag records either a contraction failure or
the removal of the designated retained arm on an actually executed round.
-/
noncomputable def freshStoppedPruneRoundsCardAndMaxStateLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower delta : ℝ) (cutoff : ℕ) (anchor maximum : Arm)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) (roundCount : ℕ) :
    PMF (Finset Arm × Bool) := by
  classical
  exact adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw
    (stoppedPruneAdvance cutoff decision)
    (fun round active outcome =>
      (¬ active.card ≤ 2 * cutoff ∧
        cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
        delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
          ((pruneBadArms preferenceGap lower anchor
            (stoppedPruneAdvance cutoff decision round active outcome)).card : ℝ)) ∨
      (¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
          decision round active outcome maximum ≠ .upper))
    roundCount

/-- Erasing the contraction flag yields the actual stopped-Prune active law. -/
theorem freshStoppedPruneRoundsStateLaw_map_fst_eq_activeLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower delta : ℝ) (cutoff : ℕ) (anchor : Arm)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) (roundCount : ℕ) :
    (freshStoppedPruneRoundsStateLaw preferenceGap lower delta cutoff anchor initial outcomeLaw
      decision roundCount).map Prod.fst =
      freshStoppedPruneActiveLaw initial outcomeLaw cutoff decision roundCount := by
  simpa only [freshStoppedPruneRoundsStateLaw, freshStoppedPruneActiveLaw] using
    (adaptiveQueryStateLaw_map_fst_eq_activeLaw (PMF.pure initial) outcomeLaw
      (stoppedPruneAdvance cutoff decision)
      (fun round active outcome =>
        ¬ active.card ≤ 2 * cutoff ∧
          cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (stoppedPruneAdvance cutoff decision round active outcome)).card : ℝ))
      roundCount)

/-- Erasing the joint flag yields that same actual stopped-Prune active law. -/
theorem freshStoppedPruneRoundsCardAndMaxStateLaw_map_fst_eq_activeLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower delta : ℝ) (cutoff : ℕ) (anchor maximum : Arm)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) (roundCount : ℕ) :
    (freshStoppedPruneRoundsCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
      initial outcomeLaw decision roundCount).map Prod.fst =
      freshStoppedPruneActiveLaw initial outcomeLaw cutoff decision roundCount := by
  simpa only [freshStoppedPruneRoundsCardAndMaxStateLaw, freshStoppedPruneActiveLaw] using
    (adaptiveQueryStateLaw_map_fst_eq_activeLaw (PMF.pure initial) outcomeLaw
      (stoppedPruneAdvance cutoff decision)
      (fun round active outcome =>
        (¬ active.card ≤ 2 * cutoff ∧
          cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (stoppedPruneAdvance cutoff decision round active outcome)).card : ℝ)) ∨
        (¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
          decision round active outcome maximum ≠ .upper))
      roundCount)

/--
On one finite stopped fresh execution, no joint failure entails both the
Lemma-15 cardinality endpoint and retention of the designated arm.  A caller
supplies a uniform bound for the union of the two one-round failure events.
-/
theorem freshStoppedPruneRounds_card_and_max_success_probability_ge_one_sub_sum
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor maximum : Arm)
    (initial : Finset Arm) (delta : ℝ)
    (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision)
    (failureBudget : ℕ → ℝ) (roundCount : ℕ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hmaximum : maximum ∈ initial) (hdelta : 0 ≤ delta)
    (hfailure : ∀ round active,
      pmfProb (outcomeLaw round active) (fun outcome =>
        (¬ active.card ≤ 2 * cutoff ∧
          cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
          delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
            ((pruneBadArms preferenceGap lower anchor
              (stoppedPruneAdvance cutoff decision round active outcome)).card : ℝ)) ∨
        (¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
          decision round active outcome maximum ≠ .upper)) ≤ failureBudget round)
    (htarget : delta ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff) :
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      pmfProb
        (freshStoppedPruneRoundsCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
          initial outcomeLaw decision roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1) := by
  classical
  let badCount : Finset Arm → ℝ := fun active =>
    ((pruneBadArms preferenceGap lower anchor active).card : ℝ)
  let advance : AdaptiveStateUpdate (Finset Arm) Outcome := stoppedPruneAdvance cutoff decision
  let contractionBad : ℕ → Finset Arm → Outcome → Prop := fun round active outcome =>
    ¬ active.card ≤ 2 * cutoff ∧ cutoff < badCount active ∧
      delta * badCount active < badCount (advance round active outcome)
  let retentionBad : ℕ → Finset Arm → Outcome → Prop := fun round active outcome =>
    ¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
      decision round active outcome maximum ≠ .upper
  let bad : ℕ → Finset Arm → Outcome → Prop := fun round active outcome =>
    contractionBad round active outcome ∨ retentionBad round active outcome
  let invariant : ℕ → Finset Arm → Bool → Prop := fun round active flag =>
    flag = false →
      (active.card ≤ 2 * cutoff ∨ badCount active ≤ cutoff ∨
        badCount active ≤ delta ^ round * badCount initial) ∧ maximum ∈ active
  have hinitial : ∀ active ∈ (PMF.pure initial).support, invariant 0 active false := by
    intro active hactive _
    simp [badCount] at hactive ⊢
    subst active
    exact ⟨Or.inr (Or.inr (by simp)), hmaximum⟩
  have hbadMonotone : ∀ round active outcome,
      badCount (advance round active outcome) ≤ badCount active := by
    intro round active outcome
    dsimp [badCount, advance]
    exact_mod_cast Finset.card_le_card
      (pruneBadArms_subset_of_subset preferenceGap lower anchor
        (stoppedPruneAdvance_subset cutoff decision round active outcome))
  have hadvance : ∀ round active flag outcome,
      invariant round active flag →
      invariant (round + 1) (advance round active outcome)
        (flag || decide (bad round active outcome)) := by
    intro round active flag outcome hinvariant hnextFlag
    have hflag : flag = false := (Bool.or_eq_false_iff.mp hnextFlag).1
    have hbadFalse : decide (bad round active outcome) = false :=
      (Bool.or_eq_false_iff.mp hnextFlag).2
    have hnotBad : ¬ bad round active outcome := by simpa using hbadFalse
    have hnotContraction : ¬ contractionBad round active outcome := fun hbad =>
      hnotBad (Or.inl hbad)
    have hnotRetention : ¬ retentionBad round active outcome := fun hbad =>
      hnotBad (Or.inr hbad)
    rcases hinvariant hflag with ⟨hsize, hmax⟩
    constructor
    · rcases hsize with hstopped | hsmall | hgeometric
      · left
        simp [advance, stoppedPruneAdvance, hstopped]
      · right; left
        exact (hbadMonotone round active outcome).trans hsmall
      · by_cases hsmall : badCount active ≤ cutoff
        · right; left
          exact (hbadMonotone round active outcome).trans hsmall
        · by_cases hstopped : active.card ≤ 2 * cutoff
          · left
            simp [advance, stoppedPruneAdvance, hstopped]
          · right; right
            have hcontract : badCount (advance round active outcome) ≤
                delta * badCount active := by
                  apply le_of_not_gt
                  intro htooMany
                  exact hnotContraction ⟨hstopped, lt_of_not_ge hsmall, htooMany⟩
            calc
              badCount (advance round active outcome) ≤ delta * badCount active := hcontract
              _ ≤ delta * (delta ^ round * badCount initial) :=
                mul_le_mul_of_nonneg_left hgeometric hdelta
              _ = delta ^ (round + 1) * badCount initial := by
                rw [pow_succ]
                ring
    · by_cases hstopped : active.card ≤ 2 * cutoff
      · simpa [advance, stoppedPruneAdvance, hstopped] using hmax
      · have hadvance : advance round active outcome =
            pruneRound active (decision round active outcome) := by
              simp [advance, stoppedPruneAdvance, hstopped]
        rw [hadvance]
        apply mem_pruneRound_of_upper active (decision round active outcome) maximum hmax
        by_contra hnotUpper
        exact hnotRetention ⟨hstopped, hmax, hnotUpper⟩
  have hinvariantSupport := adaptiveQueryStateLaw_support_invariant
    (PMF.pure initial) outcomeLaw advance bad invariant hinitial hadvance
  have hsuccess := adaptiveQuerySuccessProbability_ge_one_sub_sum
    (PMF.pure initial) outcomeLaw advance bad failureBudget (by
      intro round active
      simpa [bad, contractionBad, retentionBad, badCount, advance] using hfailure round active)
    roundCount
  have hresult : ∀ stateFailure ∈
      (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount).support,
      stateFailure.2 = false →
        stateFailure.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1 := by
    intro stateFailure hsupport hflag
    rcases hinvariantSupport roundCount stateFailure hsupport hflag with ⟨hsize, hmax⟩
    constructor
    · rcases hsize with hstopped | hsmall | hgeometric
      · exact hstopped
      · apply pruneActive_card_le_two_mul_of_goodAnchor_and_badArms
          preferenceGap lower cutoff anchor stateFailure.1 hanchor
        exact (Nat.cast_le (α := ℝ)).mp (by simpa [badCount] using hsmall)
      · apply pruneActive_card_le_two_mul_of_goodAnchor_and_badArms
          preferenceGap lower cutoff anchor stateFailure.1 hanchor
        exact (Nat.cast_le (α := ℝ)).mp (by
          calc
            ((pruneBadArms preferenceGap lower anchor stateFailure.1).card : ℝ) =
                badCount stateFailure.1 := rfl
            _ ≤ delta ^ roundCount * badCount initial := hgeometric
            _ ≤ cutoff := by simpa [badCount] using htarget)
    · exact hmax
  have hequal : pmfProb
      (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount)
      (fun stateFailure => stateFailure.2 = false) =
      pmfProb
        (adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw advance bad roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1) := by
    apply pmfProb_eq_of_support_iff
    intro stateFailure hsupport
    constructor
    · intro hflag
      exact ⟨hflag, (hresult stateFailure hsupport hflag).1,
        (hresult stateFailure hsupport hflag).2⟩
    · exact fun h => h.1
  simpa only [freshStoppedPruneRoundsCardAndMaxStateLaw, advance, bad, contractionBad,
    retentionBad, badCount] using hsuccess.trans_eq hequal

/--
Transfer a joint flagged stopped-Prune success event to the unique active-set
marginal that the surrounding OPT-Maximize algorithm consumes.
-/
theorem freshStoppedPruneActive_card_and_max_probability_of_joint
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (preferenceGap : Arm → Arm → ℝ) (lower delta : ℝ) (cutoff : ℕ) (anchor maximum : Arm)
    (initial : Finset Arm) (outcomeLaw : AdaptiveOutcomeKernel (Finset Arm) Outcome)
    (decision : ℕ → Finset Arm → Outcome → Arm → CompareDecision) (roundCount : ℕ)
    (successBound : ℝ)
    (hjoint : successBound ≤
      pmfProb
        (freshStoppedPruneRoundsCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
          initial outcomeLaw decision roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1)) :
    successBound ≤
      pmfProb (freshStoppedPruneActiveLaw initial outcomeLaw cutoff decision roundCount)
        (fun active => active.card ≤ 2 * cutoff ∧ maximum ∈ active) := by
  calc
    successBound ≤
        pmfProb
          (freshStoppedPruneRoundsCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
            initial outcomeLaw decision roundCount)
          (fun stateFailure => stateFailure.2 = false ∧
            stateFailure.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1) := hjoint
    _ ≤ pmfProb
          (freshStoppedPruneRoundsCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
            initial outcomeLaw decision roundCount)
          (fun stateFailure => stateFailure.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1) := by
            apply pmfProb_le_of_imp
            intro stateFailure hsuccess
            exact ⟨hsuccess.2.1, hsuccess.2.2⟩
    _ = pmfProb
          ((freshStoppedPruneRoundsCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
            initial outcomeLaw decision roundCount).map Prod.fst)
          (fun active => active.card ≤ 2 * cutoff ∧ maximum ∈ active) := by
            rw [pmfProb_map]
    _ = pmfProb (freshStoppedPruneActiveLaw initial outcomeLaw cutoff decision roundCount)
          (fun active => active.card ≤ 2 * cutoff ∧ maximum ∈ active) := by
            rw [freshStoppedPruneRoundsCardAndMaxStateLaw_map_fst_eq_activeLaw]

/--
The source Lemma-15 cardinality conclusion stated on stopped Prune's actual
active-set marginal, rather than its contraction-proof flag.
-/
theorem canonicalFreshStoppedPruneActive_card_success_probability_of_sourceLemma15
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcard : 2 ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta) :
    1 - delta / 2 ≤
      pmfProb
        (freshStoppedPruneActiveLaw initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
            lower upper delta maxBatch hbudget)
          cutoff
          (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
          (Fintype.card Arm))
        (fun active => active.card ≤ 2 * cutoff) := by
  have hflagged := canonicalFreshStoppedPruneRounds_card_success_probability_ge_one_sub_delta_half_of_sourceLemma15
    preferenceGap hprobability anchor lower upper delta maxBatch cutoff hbudget initial hanchor
    hseparation hdelta hdeltaHalf hcard hcutoff hdeltaLower
  calc
    1 - delta / 2 ≤
        pmfProb
          (freshStoppedPruneRoundsStateLaw preferenceGap lower delta cutoff anchor initial
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
              lower upper delta maxBatch hbudget)
            (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
            (Fintype.card Arm))
          (fun stateFailure => stateFailure.2 = false ∧
            stateFailure.1.card ≤ 2 * cutoff) := hflagged
    _ ≤ pmfProb
          (freshStoppedPruneRoundsStateLaw preferenceGap lower delta cutoff anchor initial
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
              lower upper delta maxBatch hbudget)
            (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
            (Fintype.card Arm))
          (fun stateFailure => stateFailure.1.card ≤ 2 * cutoff) := by
            apply pmfProb_le_of_imp
            intro stateFailure hsuccess
            exact hsuccess.2
    _ = pmfProb
          ((freshStoppedPruneRoundsStateLaw preferenceGap lower delta cutoff anchor initial
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
              lower upper delta maxBatch hbudget)
            (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
            (Fintype.card Arm)).map Prod.fst)
          (fun active => active.card ≤ 2 * cutoff) := by
            rw [pmfProb_map]
    _ = pmfProb
          (freshStoppedPruneActiveLaw initial
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
              lower upper delta maxBatch hbudget)
            cutoff
            (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
            (Fintype.card Arm))
          (fun active => active.card ≤ 2 * cutoff) := by
            rw [freshStoppedPruneRoundsStateLaw_map_fst_eq_activeLaw]

/--
Concrete joint Prune guarantee on the canonical tagged source law.  The
`n⁻²` contraction total and the `delta / 2` retention total are charged on
the same stopped execution, rather than being separate existential runs.
-/
theorem canonicalFreshStoppedPruneRounds_card_and_max_success_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (roundCount : ℕ) (anchor maximum : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < roundCount,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hmaximum : maximum ∈ initial) (hgap : upper ≤ preferenceGap maximum anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hcard : 2 ≤ Fintype.card Arm) (hroundCount : roundCount ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta)
    (htarget : delta ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff) :
    1 - (1 / (Fintype.card Arm : ℝ) ^ 2 + delta / 2) ≤
      pmfProb
        (freshStoppedPruneRoundsCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
          initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
          roundCount)
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1) := by
  let contractionBudget : ℝ := 1 / (Fintype.card Arm : ℝ) ^ 3
  let retentionBudget : ℕ → ℝ := adaptivePruneRoundDelta delta
  let failureBudget : ℕ → ℝ := fun round =>
    if round < roundCount then contractionBudget + retentionBudget round else 1
  have hfailure : ∀ round active,
      pmfProb
        (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
          lower upper delta maxBatch hbudget round active)
        (fun outcome =>
          (¬ active.card ≤ 2 * cutoff ∧
            cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
            delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
              ((pruneBadArms preferenceGap lower anchor
                (stoppedPruneAdvance cutoff
                  (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
                  round active outcome)).card : ℝ)) ∨
          (¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
            canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget
              round active outcome maximum ≠ .upper)) ≤ failureBudget round := by
    intro round active
    by_cases hround : round < roundCount
    · have hcontraction := canonicalFreshStoppedPruneRound_contraction_failure_le_card_inv_cube
        preferenceGap hprobability roundCount anchor lower upper delta maxBatch cutoff hbudget
        round hround active hseparation hdelta hdeltaLeOne hcard hcutoff hdeltaLower
      have hretention :
          pmfProb
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
              lower upper delta maxBatch hbudget round active)
            (fun outcome =>
              ¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
                canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget
                  round active outcome maximum ≠ .upper) ≤ retentionBudget round := by
            apply (pmfProb_le_of_imp _ _ _ ?_).trans
              (canonicalFreshPruneRound_upper_failure_probability preferenceGap hprobability
                roundCount anchor lower upper delta maxBatch hbudget round hround active maximum
                hgap hseparation hdelta hdeltaLeOne)
            intro outcome hbad
            exact hbad.2.2
      have hunion :
          pmfProb
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
              lower upper delta maxBatch hbudget round active)
            (fun outcome =>
              (¬ active.card ≤ 2 * cutoff ∧
                cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
                delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
                  ((pruneBadArms preferenceGap lower anchor
                    (stoppedPruneAdvance cutoff
                      (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
                      round active outcome)).card : ℝ)) ∨
              (¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
                canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget
                  round active outcome maximum ≠ .upper)) ≤
            pmfProb
              (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
                lower upper delta maxBatch hbudget round active)
              (fun outcome =>
                ¬ active.card ≤ 2 * cutoff ∧
                  cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
                  delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
                    ((pruneBadArms preferenceGap lower anchor
                      (stoppedPruneAdvance cutoff
                        (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
                        round active outcome)).card : ℝ)) +
            pmfProb
              (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
                lower upper delta maxBatch hbudget round active)
              (fun outcome =>
                ¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
                  canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget
                    round active outcome maximum ≠ .upper) := by
              exact pmfProb_or_le _ _ _
      calc
        pmfProb
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
              lower upper delta maxBatch hbudget round active)
            (fun outcome =>
              (¬ active.card ≤ 2 * cutoff ∧
                cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
                delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
                  ((pruneBadArms preferenceGap lower anchor
                    (stoppedPruneAdvance cutoff
                      (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
                      round active outcome)).card : ℝ)) ∨
              (¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
                canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget
                  round active outcome maximum ≠ .upper)) ≤
            contractionBudget + retentionBudget round :=
              hunion.trans (add_le_add hcontraction hretention)
        _ = failureBudget round := by simp [failureBudget, hround]
    · simpa [failureBudget, hround] using
        (pmfProb_le_one
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
            lower upper delta maxBatch hbudget round active)
          (fun outcome =>
            (¬ active.card ≤ 2 * cutoff ∧
              cutoff < ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ∧
              delta * ((pruneBadArms preferenceGap lower anchor active).card : ℝ) <
                ((pruneBadArms preferenceGap lower anchor
                  (stoppedPruneAdvance cutoff
                    (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
                    round active outcome)).card : ℝ)) ∨
            (¬ active.card ≤ 2 * cutoff ∧ maximum ∈ active ∧
              canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget
                round active outcome maximum ≠ .upper)))
  have hfresh := freshStoppedPruneRounds_card_and_max_success_probability_ge_one_sub_sum
    preferenceGap lower cutoff anchor maximum initial delta
    (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
      lower upper delta maxBatch hbudget)
    (canonicalFreshPruneDecision roundCount lower upper delta maxBatch hbudget)
    failureBudget roundCount hanchor hmaximum hdelta.le hfailure htarget
  have hsum : (∑ round ∈ Finset.range roundCount, failureBudget round) =
      (roundCount : ℝ) * contractionBudget +
        ∑ round ∈ Finset.range roundCount, retentionBudget round := by
    calc
      (∑ round ∈ Finset.range roundCount, failureBudget round) =
          ∑ round ∈ Finset.range roundCount, (contractionBudget + retentionBudget round) := by
            apply Finset.sum_congr rfl
            intro round hround
            simp [failureBudget, Finset.mem_range.mp hround]
      _ = (roundCount : ℝ) * contractionBudget +
          ∑ round ∈ Finset.range roundCount, retentionBudget round := by
            rw [Finset.sum_add_distrib]
            simp
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hcard
  have hcontractNonneg : 0 ≤ contractionBudget := by
    dsimp [contractionBudget]
    positivity
  have hcontractSum : (roundCount : ℝ) * contractionBudget ≤
      1 / (Fintype.card Arm : ℝ) ^ 2 := by
    dsimp [contractionBudget]
    calc
      (roundCount : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) ≤
          (Fintype.card Arm : ℝ) * (1 / (Fintype.card Arm : ℝ) ^ 3) := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hroundCount
            · exact hcontractNonneg
      _ = 1 / (Fintype.card Arm : ℝ) ^ 2 := by
            field_simp [ne_of_gt hcardPos]
  have hretentionSum : ∑ round ∈ Finset.range roundCount, retentionBudget round ≤ delta / 2 := by
    simpa [retentionBudget] using
      adaptivePruneRoundDelta_sum_le_half delta hdelta.le roundCount
  have hsumLe : ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      1 / (Fintype.card Arm : ℝ) ^ 2 + delta / 2 := by
    rw [hsum]
    exact add_le_add hcontractSum hretentionSum
  calc
    1 - (1 / (Fintype.card Arm : ℝ) ^ 2 + delta / 2) ≤
        1 - ∑ round ∈ Finset.range roundCount, failureBudget round := by
          linarith
    _ ≤ _ := hfresh

/--
The source-normalized Lemma-15 form of the joint stopped-Prune theorem.  Its
cutoff lower bound converts the accumulated `n⁻²` contraction probability to
the remaining `delta / 2`, so the combined size-and-retention event has the
literal `1 - delta` probability required by Lemma 17.
-/
theorem canonicalFreshStoppedPruneRounds_card_and_max_success_probability_of_sourceLemma15
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor maximum : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hmaximum : maximum ∈ initial) (hgap : upper ≤ preferenceGap maximum anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcard : 2 ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta) :
    1 - delta ≤
      pmfProb
        (freshStoppedPruneRoundsCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
          initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
            lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
          (Fintype.card Arm))
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1) := by
  have hcutoffPosReal : 0 < (cutoff : ℝ) :=
    lt_of_le_of_lt (Real.sqrt_nonneg _) hcutoff
  have hcutoffPos : 0 < cutoff := by exact_mod_cast hcutoffPosReal
  have htarget := sourceLemma15_card_round_geometric_target preferenceGap lower anchor initial
    cutoff delta hcutoffPos hdelta.le hdeltaHalf
  have hcore := canonicalFreshStoppedPruneRounds_card_and_max_success_probability
    preferenceGap hprobability (Fintype.card Arm) anchor maximum lower upper delta maxBatch cutoff
    hbudget initial hanchor hmaximum hgap hseparation hdelta
    (hdeltaHalf.trans (by norm_num)) hcard (le_refl _) hcutoff hdeltaLower htarget
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hcard
  have hcutoffOne : 1 ≤ (cutoff : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr hcutoffPos
  have hcardTwo : (2 : ℝ) ≤ (Fintype.card Arm : ℝ) := by exact_mod_cast hcard
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
    _ ≤ _ := hcore

/--
Lemma 17's high-gap branch: if the Pick-Anchor result is not already an
`upper`-maximum, SST makes the absolute maximum satisfy Prune's upper
comparison threshold.  The concrete stopped source PMF then retains it while
also delivering the cardinality endpoint.
-/
theorem canonicalFreshStoppedPruneRounds_card_and_max_success_probability_of_not_epsilonMaximum
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor maximum : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hanchorNotMaximum : ¬ EpsilonMaximum preferenceGap upper anchor)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hmaximum : maximum ∈ initial)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcard : 2 ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta) :
    1 - delta ≤
      pmfProb
        (freshStoppedPruneRoundsCardAndMaxStateLaw preferenceGap lower delta cutoff anchor maximum
          initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
            lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
          (Fintype.card Arm))
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.card ≤ 2 * cutoff ∧ maximum ∈ stateFailure.1) := by
  apply canonicalFreshStoppedPruneRounds_card_and_max_success_probability_of_sourceLemma15
    preferenceGap hprobability anchor maximum lower upper delta maxBatch cutoff hbudget initial
    hanchor hmaximum
  · exact le_of_lt (absoluteMaximum_gap_gt_of_not_epsilonMaximum preferenceGap upper
      hantisymmetric hsst hupperNonnegative maximum anchor hmaximumAbsolute hanchorNotMaximum)
  · exact hseparation
  · exact hdelta
  · exact hdeltaHalf
  · exact hcard
  · exact hcutoff
  · exact hdeltaLower

/--
The Lemma-17 high-gap result stated directly on stopped Prune's active-set
marginal, the law consumed by the later OPT-Maximize phases.
-/
theorem canonicalFreshStoppedPruneActive_card_and_max_success_probability_of_not_epsilonMaximum
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor maximum : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hanchorNotMaximum : ¬ EpsilonMaximum preferenceGap upper anchor)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hmaximum : maximum ∈ initial)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcard : 2 ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta) :
    1 - delta ≤
      pmfProb
        (freshStoppedPruneActiveLaw initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
            lower upper delta maxBatch hbudget)
          cutoff
          (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
          (Fintype.card Arm))
        (fun active => active.card ≤ 2 * cutoff ∧ maximum ∈ active) := by
  apply freshStoppedPruneActive_card_and_max_probability_of_joint
    preferenceGap lower delta cutoff anchor maximum initial
    (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
      lower upper delta maxBatch hbudget)
    (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
    (Fintype.card Arm) (1 - delta)
  exact canonicalFreshStoppedPruneRounds_card_and_max_success_probability_of_not_epsilonMaximum
    preferenceGap hprobability anchor maximum lower upper delta maxBatch cutoff hbudget initial
    hantisymmetric hsst hupperNonnegative hmaximumAbsolute hanchorNotMaximum hanchor hmaximum
    hseparation hdelta hdeltaHalf hcard hcutoff hdeltaLower

end FalahatgarEtAl2017MaxingRanking
