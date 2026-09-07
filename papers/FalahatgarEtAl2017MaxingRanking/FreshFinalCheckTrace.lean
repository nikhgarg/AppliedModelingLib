import FalahatgarEtAl2017MaxingRanking.OptMaximizeResource

/-!
# Early-stopping traces for OPT-Maximize's final check

Algorithm 3 returns to Seq-Eliminate at the first upper comparison result in
its final loop.  The finite state below records precisely the queried prefix;
outcomes sampled after that return point are ignored by the state transition.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The queried-prefix record and no-upper flag of the final comparison loop. -/
abbrev finalCheckTraceState {Arm : Type*} [DecidableEq Arm] (candidates : Finset Arm) :=
  (Fin candidates.card → Option Bool) × Bool

/-- Initially no retained candidate has been queried and no upper result occurred. -/
noncomputable def initialFinalCheckTraceState {Arm : Type*} [DecidableEq Arm]
    (candidates : Finset Arm) : finalCheckTraceState candidates :=
  (fun _ => none, true)

/--
The source final-loop transition.  A `some true` trace entry is the upper
result that calls the fallback; entries after it remain `none` because the
source loop has already returned.
-/
noncomputable def canonicalFreshFinalCheckTraceAdvance
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (candidates : Finset Arm) (lower upper eta : ℝ) :
    AdaptiveStateUpdate (finalCheckTraceState candidates)
      (Fin (fixedSampleBudget lower upper eta) → Bool) :=
  fun queryIndex state outcome =>
    if hqueryIndex : queryIndex < candidates.card then
      if hnoUpper : state.2 then
        let isUpper := decide (adaptiveCompare
          (canonicalComparisonBatchObservation (fixedSampleBudget lower upper eta))
          (fixedSampleBudget lower upper eta) lower upper eta outcome = .upper)
        (Function.update state.1 ⟨queryIndex, hqueryIndex⟩ (some isUpper), !isUpper)
      else state
    else state

/-- The number of fresh final-loop comparisons actually reached before return. -/
noncomputable def finalCheckTraceComparisonCount {Arm : Type*} [DecidableEq Arm]
    (candidates : Finset Arm) (lower upper eta : ℝ)
    (trace : Fin candidates.card → Option Bool) : ℕ :=
  (Finset.univ.filter fun queryIndex => (trace queryIndex).isSome).card *
    fixedSampleBudget lower upper eta

/-- The source cap remains a valid bound for every early-stopping final trace. -/
theorem finalCheckTraceComparisonCount_le_cap {Arm : Type*} [DecidableEq Arm]
    (candidates : Finset Arm) (lower upper eta : ℝ)
    (trace : Fin candidates.card → Option Bool) :
    finalCheckTraceComparisonCount candidates lower upper eta trace ≤
      optMaximizeFinalCheckComparisonCap candidates lower upper eta := by
  unfold finalCheckTraceComparisonCount optMaximizeFinalCheckComparisonCap
  apply Nat.mul_le_mul_right
  have hsubset : (Finset.univ.filter fun queryIndex : Fin candidates.card =>
      (trace queryIndex).isSome) ⊆ Finset.univ := Finset.filter_subset _ _
  simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hsubset

/--
The finite PMF of the source final loop together with its early-stopping
prefix trace.  The batch kernel is available at every index, but the advance
function ignores it once a prior upper decision has returned.
-/
noncomputable def canonicalFreshFinalCheckTraceLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchor : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (lower upper eta : ℝ) : PMF (finalCheckTraceState candidates) := by
  classical
  exact adaptiveQueryActiveLaw (PMF.pure (initialFinalCheckTraceState candidates))
    (fun queryIndex state => canonicalFreshFinalCheckOutcomeLaw anchor candidates preferenceGap
      hprobability lower upper eta queryIndex state.2)
    (canonicalFreshFinalCheckTraceAdvance candidates lower upper eta)
    candidates.card

/-- The output selected by the early-stopping trace. -/
noncomputable def canonicalFreshFinalCheckTraceOutputLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchor fallback : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (lower upper eta : ℝ) : PMF Arm :=
  (canonicalFreshFinalCheckTraceLaw anchor candidates preferenceGap hprobability lower upper eta).map
    fun traceState => if traceState.2 then anchor else fallback

/-- The no-upper projection of one trace transition is the original final-loop transition. -/
theorem canonicalFreshFinalCheckTraceAdvance_snd
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (candidates : Finset Arm) (lower upper eta : ℝ)
    (queryIndex : ℕ) (state : finalCheckTraceState candidates)
    (outcome : Fin (fixedSampleBudget lower upper eta) → Bool) :
    (canonicalFreshFinalCheckTraceAdvance candidates lower upper eta queryIndex state outcome).2 =
      canonicalFreshFinalCheckAdvance candidates lower upper eta queryIndex state.2 outcome := by
  unfold canonicalFreshFinalCheckTraceAdvance canonicalFreshFinalCheckAdvance
  split
  · split <;> simp_all
  · rfl

/--
Erasing the queried-prefix record recovers the existing source final-loop PMF.
The equality makes the early-stop trace a conservative refinement, not a new
independent final-check execution.
-/
theorem canonicalFreshFinalCheckTraceLaw_map_noUpper_eq
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchor : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (lower upper eta : ℝ) :
    (canonicalFreshFinalCheckTraceLaw anchor candidates preferenceGap hprobability lower upper eta).map
      Prod.snd =
      canonicalFreshFinalCheckNoUpperLaw anchor candidates preferenceGap hprobability lower upper eta := by
  classical
  let traceInitial : PMF (finalCheckTraceState candidates) :=
    PMF.pure (initialFinalCheckTraceState candidates)
  let traceOutcomeLaw : AdaptiveOutcomeKernel (finalCheckTraceState candidates)
      (Fin (fixedSampleBudget lower upper eta) → Bool) :=
    fun queryIndex state => canonicalFreshFinalCheckOutcomeLaw anchor candidates preferenceGap hprobability
      lower upper eta queryIndex state.2
  let traceAdvance : AdaptiveStateUpdate (finalCheckTraceState candidates)
      (Fin (fixedSampleBudget lower upper eta) → Bool) :=
    canonicalFreshFinalCheckTraceAdvance candidates lower upper eta
  let outcomeLaw := canonicalFreshFinalCheckOutcomeLaw anchor candidates preferenceGap hprobability
    lower upper eta
  let advance := canonicalFreshFinalCheckAdvance candidates lower upper eta
  have hmap : ∀ queryCount,
      (adaptiveQueryActiveLaw traceInitial traceOutcomeLaw traceAdvance queryCount).map Prod.snd =
        adaptiveQueryActiveLaw (PMF.pure true) outcomeLaw advance queryCount := by
    intro queryCount
    induction queryCount with
    | zero =>
        change (PMF.pure (initialFinalCheckTraceState candidates)).map Prod.snd = PMF.pure true
        rw [PMF.pure_map]
        rfl
    | succ queryCount ih =>
        rw [adaptiveQueryActiveLaw, adaptiveQueryActiveLaw, PMF.map_bind]
        simp_rw [PMF.map_comp]
        have hkernel : (fun state : finalCheckTraceState candidates =>
            (traceOutcomeLaw queryCount state).map
              (Prod.snd ∘ fun outcome => traceAdvance queryCount state outcome)) =
            (fun noUpper => (outcomeLaw queryCount noUpper).map
              fun outcome => advance queryCount noUpper outcome) ∘ Prod.snd := by
          funext state
          dsimp only [traceOutcomeLaw, outcomeLaw, traceAdvance, advance]
          congr 1
          funext outcome
          exact canonicalFreshFinalCheckTraceAdvance_snd candidates lower upper eta queryCount state
            outcome
        rw [hkernel, ← PMF.bind_map, ih]
  change
    (adaptiveQueryActiveLaw traceInitial traceOutcomeLaw traceAdvance candidates.card).map Prod.snd =
      adaptiveQueryActiveLaw (PMF.pure true) outcomeLaw advance candidates.card
  exact hmap candidates.card

/-- The returned-arm marginal of the early-stopping trace is the existing final-check output law. -/
theorem canonicalFreshFinalCheckTraceOutputLaw_eq
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchor fallback : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (lower upper eta : ℝ) :
    canonicalFreshFinalCheckTraceOutputLaw anchor fallback candidates preferenceGap hprobability lower upper eta =
      canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap hprobability lower upper eta := by
  unfold canonicalFreshFinalCheckTraceOutputLaw canonicalFreshFinalCheckOutputLaw
  rw [← canonicalFreshFinalCheckTraceLaw_map_noUpper_eq anchor candidates preferenceGap hprobability]
  rw [PMF.map_comp]
  rfl

end FalahatgarEtAl2017MaxingRanking
