import FalahatgarEtAl2017MaxingRanking.FiniteBatchFreshSeqEliminate

/-!
# Fresh Seq-Eliminate on a possibly empty finite candidate set

OPT-Maximize invokes Seq-Eliminate after randomized Prune.  The algorithm is
specified on the high-probability branch where that candidate set contains an
absolute maximum and is therefore nonempty.  This file totalizes the finite
program off that branch by returning a supplied fallback arm on the empty set;
the source execution is unchanged whenever the candidate set is nonempty.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The initial incumbent for Seq-Eliminate on a finite candidate set. -/
noncomputable def finsetSeqEliminateInitial {Arm : Type*} [DecidableEq Arm]
    (emptyFallback : Arm) (candidates : Finset Arm) : Arm :=
  candidates.toList.headD emptyFallback

/-- The candidates after the initial incumbent, in the finite-set enumeration order. -/
noncomputable def finsetSeqEliminateChallengers {Arm : Type*} [DecidableEq Arm]
    (candidates : Finset Arm) : List Arm :=
  candidates.toList.tail

/-- A nonempty finite candidate set is its initial incumbent followed by its challengers. -/
theorem finsetSeqEliminate_toList_eq_initial_cons_challengers
    {Arm : Type*} [DecidableEq Arm] (emptyFallback : Arm) (candidates : Finset Arm)
    (hnonempty : candidates.Nonempty) :
    candidates.toList = finsetSeqEliminateInitial emptyFallback candidates ::
      finsetSeqEliminateChallengers candidates := by
  have hlist : candidates.toList ≠ [] := hnonempty.toList_ne_nil
  cases htoList : candidates.toList with
  | nil => exact (hlist htoList).elim
  | cons initial challengers =>
      simp only [finsetSeqEliminateInitial, finsetSeqEliminateChallengers, htoList,
        List.headD_cons, List.tail_cons]

/-- On a nonempty finite candidate set, the challenger count is one less than its cardinality. -/
theorem finsetSeqEliminateChallengers_length
    {Arm : Type*} [DecidableEq Arm] (candidates : Finset Arm)
    (hnonempty : candidates.Nonempty) :
    (finsetSeqEliminateChallengers candidates).length = candidates.card - 1 := by
  have hlist : candidates.toList ≠ [] := hnonempty.toList_ne_nil
  cases htoList : candidates.toList with
  | nil => exact (hlist htoList).elim
  | cons initial challengers =>
      have hcard : candidates.card = (initial :: challengers).length := by
        rw [← Finset.length_toList candidates, htoList]
      have hcard' : candidates.card = challengers.length + 1 := by
        simpa using hcard
      simp only [finsetSeqEliminateChallengers, htoList, List.tail_cons]
      omega

/-- An arm retained in the finite candidate set occurs in its Seq-Eliminate list. -/
theorem finsetSeqEliminate_maximum_appears
    {Arm : Type*} [DecidableEq Arm] (emptyFallback maximum : Arm) (candidates : Finset Arm)
    (hmaximum : maximum ∈ candidates) :
    finsetSeqEliminateInitial emptyFallback candidates = maximum ∨
      maximum ∈ finsetSeqEliminateChallengers candidates := by
  have hnonempty : candidates.Nonempty := ⟨maximum, hmaximum⟩
  have hlist := finsetSeqEliminate_toList_eq_initial_cons_challengers
    emptyFallback candidates hnonempty
  have hmem : maximum ∈ candidates.toList := Finset.mem_toList.mpr hmaximum
  rw [hlist] at hmem
  rcases (List.mem_cons.mp hmem) with hhead | htail
  · exact Or.inl hhead.symm
  · exact Or.inr htail

/-- The totalized deterministic Seq-Eliminate output on a finite candidate set. -/
noncomputable def finsetSeqEliminateOutput {Arm : Type*} [DecidableEq Arm]
    (emptyFallback : Arm) (step : Arm → Arm → Arm) (candidates : Finset Arm) : Arm :=
  sequentialEliminate step
    (finsetSeqEliminateInitial emptyFallback candidates)
    (finsetSeqEliminateChallengers candidates)

/--
Seq-Eliminate succeeds on every retained absolute maximum; the empty-set
fallback is irrelevant because membership of the maximum makes the set
nonempty.
-/
theorem finsetSeqEliminateOutput_epsilonMaximum_of_valid
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (step : Arm → Arm → Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap) (hepsilon : 0 ≤ epsilon)
    (hvalid : SequentialEliminationStepValid preferenceGap epsilon step)
    (emptyFallback maximum : Arm) (candidates : Finset Arm)
    (hmaximum : AbsoluteMaximum preferenceGap maximum) (hmaximumMem : maximum ∈ candidates) :
    EpsilonMaximum preferenceGap epsilon
      (finsetSeqEliminateOutput emptyFallback step candidates) := by
  unfold finsetSeqEliminateOutput
  apply sequentialEliminate_epsilonMaximum_of_maximumAppears preferenceGap epsilon step
    hantisymmetric hsst hepsilon hvalid maximum
  · exact hmaximum
  · exact finsetSeqEliminate_maximum_appears emptyFallback maximum candidates hmaximumMem

/-- The canonical fresh-call Seq-Eliminate output law on a totalized finite candidate set. -/
noncomputable def canonicalFreshFinsetSeqEliminateOutputLaw
    {Arm : Type*} [Fintype Arm]
    (emptyFallback : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap) (epsilon eta : ℝ) :
    PMF Arm := by
  classical
  exact (freshAdaptiveCompareSeqEliminateStateLaw
    (finsetSeqEliminateInitial emptyFallback candidates)
    (finsetSeqEliminateChallengers candidates)
    (canonicalFreshAdaptiveCompareOutcomeLaw
      (finsetSeqEliminateInitial emptyFallback candidates)
      (finsetSeqEliminateChallengers candidates) preferenceGap hprobability epsilon eta)
    (canonicalFreshAdaptiveCompareObservation epsilon eta)
    preferenceGap epsilon eta).map Prod.fst

/-- The `ε`-maximum probability of the totalized finite-set output law. -/
noncomputable def canonicalFreshFinsetSeqEliminateEpsilonMaximumProbability
    {Arm : Type*} [Fintype Arm]
    (emptyFallback : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap) (epsilon eta : ℝ) : ℝ := by
  classical
  exact pmfProbClassical
    (canonicalFreshFinsetSeqEliminateOutputLaw emptyFallback candidates preferenceGap
      hprobability epsilon eta)
    (EpsilonMaximum preferenceGap epsilon)

/--
The concrete finite Bernoulli source model makes totalized Seq-Eliminate an
`ε`-maximum whenever the candidate set contains the absolute maximum.  Its
failure allocation is charged only to the candidate set's actual tail.
-/
theorem canonicalFreshFinsetSeqEliminate_epsilonMaximum_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (emptyFallback : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap) (epsilon eta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1)
    (maximum : Arm) (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hmaximumMem : maximum ∈ candidates) :
    1 - ((finsetSeqEliminateChallengers candidates).length : ℝ) * eta ≤
      canonicalFreshFinsetSeqEliminateEpsilonMaximumProbability emptyFallback candidates
        preferenceGap hprobability epsilon eta := by
  classical
  letI : DecidableEq Arm := Classical.decEq Arm
  have hsource := canonicalFreshAdaptiveCompareSeqEliminate_epsilonMaximum_probability
    (finsetSeqEliminateInitial emptyFallback candidates)
    (finsetSeqEliminateChallengers candidates) preferenceGap hprobability epsilon eta
    hantisymmetric hself hsst hepsilon heta hetaLeOne maximum hmaximum
    (finsetSeqEliminate_maximum_appears emptyFallback maximum candidates hmaximumMem)
  unfold freshAdaptiveCompareSeqEliminateEpsilonMaximumProbability at hsource
  rw [pmfProbClassical_eq_pmfProb] at hsource
  unfold canonicalFreshFinsetSeqEliminateEpsilonMaximumProbability
  rw [pmfProbClassical_eq_pmfProb]
  unfold canonicalFreshFinsetSeqEliminateOutputLaw
  rw [pmfProb_map]
  exact hsource

/--
Seq-Eliminate on a retained finite candidate set receives its source failure
budget by dividing it over the set's actual cardinality, not the full arm
universe.  Since it makes only `|S'|-1` calls, this yields the literal
`1-δ` success bound.
-/
theorem canonicalFreshFinsetSeqEliminate_epsilonMaximum_probability_of_sourceSchedule
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (emptyFallback : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap) (epsilon delta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (maximum : Arm) (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hmaximumMem : maximum ∈ candidates) :
    1 - delta ≤ canonicalFreshFinsetSeqEliminateEpsilonMaximumProbability
      emptyFallback candidates preferenceGap hprobability epsilon
        (delta / (candidates.card : ℝ)) := by
  have hnonempty : candidates.Nonempty := ⟨maximum, hmaximumMem⟩
  have hcardNat : 0 < candidates.card := Finset.card_pos.mpr hnonempty
  have hcardReal : 0 < (candidates.card : ℝ) := by exact_mod_cast hcardNat
  have hcardGeOne : 1 ≤ (candidates.card : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr hcardNat
  have heta : 0 < delta / (candidates.card : ℝ) := div_pos hdelta hcardReal
  have hetaLeOne : delta / (candidates.card : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hcardReal).mpr
    nlinarith
  have hbase := canonicalFreshFinsetSeqEliminate_epsilonMaximum_probability
    emptyFallback candidates preferenceGap hprobability epsilon
    (delta / (candidates.card : ℝ)) hantisymmetric hself hsst hepsilon heta hetaLeOne
    maximum hmaximum hmaximumMem
  have hlength : ((finsetSeqEliminateChallengers candidates).length : ℝ) ≤
      (candidates.card : ℝ) := by
    rw [finsetSeqEliminateChallengers_length candidates hnonempty]
    exact_mod_cast Nat.sub_le candidates.card 1
  have hspent : ((finsetSeqEliminateChallengers candidates).length : ℝ) *
      (delta / (candidates.card : ℝ)) ≤ delta := by
    calc
      ((finsetSeqEliminateChallengers candidates).length : ℝ) *
          (delta / (candidates.card : ℝ)) ≤
          (candidates.card : ℝ) * (delta / (candidates.card : ℝ)) :=
        mul_le_mul_of_nonneg_right hlength (le_of_lt heta)
      _ = delta := by
        rw [← mul_div_assoc]
        exact mul_div_cancel_left₀ delta (ne_of_gt hcardReal)
  linarith

end FalahatgarEtAl2017MaxingRanking
