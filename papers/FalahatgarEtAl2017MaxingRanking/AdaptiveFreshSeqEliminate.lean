import AppliedModelingLib.Learning.ReinforcementLearning.Preference.AdaptiveQueries
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.PAC
import FalahatgarEtAl2017MaxingRanking.AdaptiveSeqEliminate
import FalahatgarEtAl2017MaxingRanking.AdaptiveSeqEliminateProbability
import FalahatgarEtAl2017MaxingRanking.SubsetSequentialElimination

/-!
# Fresh-call adaptive Seq-Eliminate

Appendix A.3 calls `Compare` on a pair selected from the preceding history,
but the observations for that call are fresh. This file represents that
source execution with a finite adaptive-query process.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The classical event wrapper agrees with any supplied finite-PMF decider. -/
theorem pmfProbClassical_eq_pmfProb
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (event : Outcome → Prop) [DecidablePred event] :
    pmfProbClassical law event = pmfProb law event := by
  classical
  unfold pmfProbClassical pmfProb
  apply pmfExp_congr
  intro outcome
  by_cases hevent : event outcome <;> simp [hevent]

/--
An invariant holds at every positive-mass adaptive-query state if it holds
initially and is preserved by each state update.  The failure flag is part of
the invariant because it records exactly the historywise event controlled by
`adaptiveQueryFailureProbability_le_sum`.
-/
theorem adaptiveQueryStateLaw_support_invariant
    {State Outcome : Type*} [Fintype State] [DecidableEq State]
    [Fintype Outcome] [DecidableEq Outcome]
    (initialStateLaw : PMF State) (outcomeLaw : AdaptiveOutcomeKernel State Outcome)
    (advance : AdaptiveStateUpdate State Outcome) (bad : ℕ → State → Outcome → Prop)
    [∀ queryIndex state outcome, Decidable (bad queryIndex state outcome)]
    (invariant : ℕ → State → Bool → Prop)
    (hinitial : ∀ state ∈ initialStateLaw.support, invariant 0 state false)
    (hadvance : ∀ queryIndex state flag outcome,
      invariant queryIndex state flag →
      invariant (queryIndex + 1) (advance queryIndex state outcome)
        (flag || decide (bad queryIndex state outcome))) :
    ∀ queryCount stateFailure,
      stateFailure ∈
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).support →
      invariant queryCount stateFailure.1 stateFailure.2 := by
  intro queryCount
  induction queryCount with
  | zero =>
      intro stateFailure hsupport
      change stateFailure ∈
        (initialStateLaw.map fun state => (state, false)).support at hsupport
      rcases (PMF.mem_support_map_iff (fun state => (state, false)) initialStateLaw
        stateFailure).mp hsupport with ⟨state, hstate, rfl⟩
      exact hinitial state hstate
  | succ queryCount ih =>
      intro stateFailure hsupport
      change stateFailure ∈
        ((adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount).bind
          fun stateFailure => (outcomeLaw queryCount stateFailure.1).map fun outcome =>
            (advance queryCount stateFailure.1 outcome,
              stateFailure.2 || decide (bad queryCount stateFailure.1 outcome))).support at hsupport
      rcases (PMF.mem_support_bind_iff
        (adaptiveQueryStateLaw initialStateLaw outcomeLaw advance bad queryCount)
        (fun stateFailure => (outcomeLaw queryCount stateFailure.1).map fun outcome =>
          (advance queryCount stateFailure.1 outcome,
            stateFailure.2 || decide (bad queryCount stateFailure.1 outcome)))
        stateFailure).mp hsupport with ⟨previous, hprevious, hnext⟩
      rcases (PMF.mem_support_map_iff
        (fun outcome =>
          (advance queryCount previous.1 outcome,
            previous.2 || decide (bad queryCount previous.1 outcome)))
        (outcomeLaw queryCount previous.1) stateFailure).mp hnext with
        ⟨outcome, _houtcome, hresult⟩
      rw [← hresult]
      exact hadvance queryCount previous.1 previous.2 outcome
        (ih previous hprevious)

/--
If an arm first appears in the `(index + 1)`-prefix of a list, it is precisely
the challenger at that index.  The in-range hypothesis makes the default in
`List.getD` irrelevant.
-/
theorem eq_listGetD_of_mem_take_succ_not_mem_take
    {Arm : Type*} (challengers : List Arm) (default maximum : Arm) (index : ℕ)
    (hindex : index < challengers.length)
    (hmem : maximum ∈ challengers.take (index + 1))
    (hnotMem : maximum ∉ challengers.take index) :
    maximum = challengers.getD index default := by
  rcases (List.mem_take_iff_getElem.mp hmem) with ⟨position, hposition, hvalue⟩
  have hpositionLe : position ≤ index := by
    exact Nat.le_of_lt_succ
      (lt_of_lt_of_le hposition (min_le_left _ _))
  have hpositionLength : position < challengers.length :=
    lt_of_lt_of_le hposition (min_le_right _ _)
  have hnotLt : ¬ position < index := by
    intro hpositionLt
    apply hnotMem
    apply List.mem_take_iff_getElem.mpr
    exact ⟨position, lt_min hpositionLt hpositionLength, hvalue⟩
  have hindexLe : index ≤ position := Nat.le_of_not_gt hnotLt
  have hpositionEq : position = index := Nat.le_antisymm hpositionLe hindexLe
  subst position
  rw [List.getD_eq_getElem challengers default hindex]
  exact hvalue.symm

/--
The finite law of a Seq-Eliminate execution whose call outcome is drawn only
after its current incumbent has been determined.  `outcomeLaw` may therefore
depend on both the call position and the preceding incumbent.
-/
noncomputable def freshSeqEliminateStateLaw
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (initial : Arm) (challengers : List Arm)
    (outcomeLaw : AdaptiveOutcomeKernel Arm Outcome)
    (step : ℕ → Arm → Arm → Outcome → Arm)
    (bad : ℕ → Arm → Outcome → Prop)
    [∀ queryIndex incumbent outcome, Decidable (bad queryIndex incumbent outcome)] :
    PMF (Arm × Bool) :=
  adaptiveQueryStateLaw (PMF.pure initial) outcomeLaw
    (fun queryIndex incumbent outcome =>
      step queryIndex incumbent (challengers.getD queryIndex initial) outcome)
    bad challengers.length

/--
The fresh-call Seq-Eliminate union bound first establishes that the output is
`ε`-preferable to an appearing maximum. This is the form applicable to a
maximum local to a sampled input list.
-/
theorem freshSeqEliminate_epsilonPreferableToAppearingMaximum_probability_of_historywiseCallBounds
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (initial : Arm) (challengers : List Arm)
    (outcomeLaw : AdaptiveOutcomeKernel Arm Outcome)
    (step : ℕ → Arm → Arm → Outcome → Arm)
    (bad : ℕ → Arm → Outcome → Prop)
    [∀ queryIndex incumbent outcome, Decidable (bad queryIndex incumbent outcome)]
    (preferenceGap : Arm → Arm → ℝ) (epsilon failureBudget : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum : Arm) (hmaximumSelf : 0 ≤ preferenceGap maximum maximum)
    (happears : initial = maximum ∨ maximum ∈ challengers)
    (hvalid : ∀ queryIndex < challengers.length, ∀ incumbent outcome,
      ¬ bad queryIndex incumbent outcome →
        0 ≤ preferenceGap
          (step queryIndex incumbent (challengers.getD queryIndex initial) outcome) incumbent ∧
        -epsilon ≤ preferenceGap
          (step queryIndex incumbent (challengers.getD queryIndex initial) outcome)
          (challengers.getD queryIndex initial))
    (hfailure : ∀ queryIndex incumbent,
      pmfProb (outcomeLaw queryIndex incumbent) (bad queryIndex incumbent) ≤ failureBudget) :
    1 - (challengers.length : ℝ) * failureBudget ≤
      pmfProbClassical
        (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
        (fun stateFailure => -epsilon ≤ preferenceGap stateFailure.1 maximum) := by
  classical
  let invariant : ℕ → Arm → Bool → Prop := fun queryIndex incumbent failed =>
    queryIndex ≤ challengers.length → failed = false →
      (maximum = initial ∨ maximum ∈ challengers.take queryIndex) →
        -epsilon ≤ preferenceGap incumbent maximum
  have hinitial : ∀ incumbent ∈ (PMF.pure initial).support,
      invariant 0 incumbent false := by
    intro incumbent hincumbent
    have hincumbentEq : incumbent = initial :=
      (PMF.mem_support_pure_iff initial incumbent).mp hincumbent
    subst incumbent
    dsimp [invariant]
    intro _ _ hseen
    have hmaximumInitial : maximum = initial := by
      simpa using hseen
    subst maximum
    exact (neg_nonpos.mpr hepsilon).trans hmaximumSelf
  have hadvance : ∀ queryIndex incumbent failed outcome,
      invariant queryIndex incumbent failed →
      invariant (queryIndex + 1)
        (step queryIndex incumbent (challengers.getD queryIndex initial) outcome)
        (failed || decide (bad queryIndex incumbent outcome)) := by
    intro queryIndex incumbent failed outcome hinvariant
    dsimp [invariant] at hinvariant ⊢
    intro hnextIndex hfailed hseen
    have hindex : queryIndex < challengers.length :=
      Nat.lt_of_succ_le hnextIndex
    have hfailedParts : failed = false ∧ decide (bad queryIndex incumbent outcome) = false :=
      Bool.or_eq_false_iff.mp hfailed
    have hbad : ¬ bad queryIndex incumbent outcome :=
      of_decide_eq_false hfailedParts.2
    have hcall := hvalid queryIndex hindex incumbent outcome hbad
    by_cases hseenBefore : maximum = initial ∨ maximum ∈ challengers.take queryIndex
    · exact epsilonPreferableToAbsoluteMaximum_of_validStep preferenceGap epsilon
        hantisymmetric hsst hepsilon maximum incumbent
        (step queryIndex incumbent (challengers.getD queryIndex initial) outcome)
        (hinvariant (Nat.le_of_lt hindex) hfailedParts.1 hseenBefore) hcall.1
    · have hnotMem : maximum ∉ challengers.take queryIndex :=
        fun hmem => hseenBefore (Or.inr hmem)
      rcases hseen with hmaximumInitial | hmaximumMem
      · exact (hseenBefore (Or.inl hmaximumInitial)).elim
      · have hchallenger : maximum = challengers.getD queryIndex initial :=
          eq_listGetD_of_mem_take_succ_not_mem_take challengers initial maximum queryIndex
            hindex hmaximumMem hnotMem
        rw [hchallenger]
        exact hcall.2
  have hsupport : ∀ stateFailure ∈
      (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad).support,
      invariant challengers.length stateFailure.1 stateFailure.2 := by
    simpa only [freshSeqEliminateStateLaw] using
      (adaptiveQueryStateLaw_support_invariant (PMF.pure initial) outcomeLaw
        (fun queryIndex incumbent outcome =>
          step queryIndex incumbent (challengers.getD queryIndex initial) outcome)
        bad invariant hinitial hadvance challengers.length)
  have hsuccess :
      1 - (challengers.length : ℝ) * failureBudget ≤
        pmfProb (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
          (fun stateFailure => stateFailure.2 = false) := by
    simpa only [freshSeqEliminateStateLaw, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] using
      (adaptiveQuerySuccessProbability_ge_one_sub_sum (PMF.pure initial) outcomeLaw
        (fun queryIndex incumbent outcome =>
          step queryIndex incumbent (challengers.getD queryIndex initial) outcome)
        bad (fun _ => failureBudget) hfailure challengers.length)
  have hsuccessLePreferable :
      pmfProb (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
          (fun stateFailure => stateFailure.2 = false) ≤
        pmfProbClassical (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
          (fun stateFailure => -epsilon ≤ preferenceGap stateFailure.1 maximum) := by
    change pmfProb (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
        (fun stateFailure => stateFailure.2 = false) ≤
      pmfProb (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
        (fun stateFailure => -epsilon ≤ preferenceGap stateFailure.1 maximum)
    unfold pmfProb pmfExp
    apply Finset.sum_le_sum
    intro stateFailure _
    by_cases hsuccessFlag : stateFailure.2 = false
    · by_cases hcorrect : -epsilon ≤ preferenceGap stateFailure.1 maximum
      · simp [hsuccessFlag, hcorrect]
      · have hnotSupport : stateFailure ∉
          (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad).support := by
          intro hstateFailure
          apply hcorrect
          apply hsupport stateFailure hstateFailure
          · exact Nat.le_refl _
          · exact hsuccessFlag
          · rcases happears with hmaximumInitial | hmaximumMem
            · exact Or.inl hmaximumInitial.symm
            · exact Or.inr (by simpa only [List.take_length] using hmaximumMem)
        have hzero :
            ((freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
              stateFailure).toReal = 0 := by
          rw [(PMF.apply_eq_zero_iff
            (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
            stateFailure).mpr hnotSupport]
          rfl
        simp [hsuccessFlag, hcorrect, hzero]
    · by_cases hcorrect : -epsilon ≤ preferenceGap stateFailure.1 maximum
      · simp [hsuccessFlag, hcorrect, ENNReal.toReal_nonneg]
      · simp [hsuccessFlag, hcorrect]
  exact hsuccess.trans hsuccessLePreferable

/--
Theorem 2's global-maximum form follows by the SST transfer from being
`ε`-preferable to the absolute maximum.
-/
theorem freshSeqEliminate_epsilonMaximum_probability_of_historywiseCallBounds
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (initial : Arm) (challengers : List Arm)
    (outcomeLaw : AdaptiveOutcomeKernel Arm Outcome)
    (step : ℕ → Arm → Arm → Outcome → Arm)
    (bad : ℕ → Arm → Outcome → Prop)
    [∀ queryIndex incumbent outcome, Decidable (bad queryIndex incumbent outcome)]
    (preferenceGap : Arm → Arm → ℝ) (epsilon failureBudget : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum : Arm) (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (happears : initial = maximum ∨ maximum ∈ challengers)
    (hvalid : ∀ queryIndex < challengers.length, ∀ incumbent outcome,
      ¬ bad queryIndex incumbent outcome →
        0 ≤ preferenceGap
          (step queryIndex incumbent (challengers.getD queryIndex initial) outcome) incumbent ∧
        -epsilon ≤ preferenceGap
          (step queryIndex incumbent (challengers.getD queryIndex initial) outcome)
          (challengers.getD queryIndex initial))
    (hfailure : ∀ queryIndex incumbent,
      pmfProb (outcomeLaw queryIndex incumbent) (bad queryIndex incumbent) ≤ failureBudget) :
    1 - (challengers.length : ℝ) * failureBudget ≤
      pmfProbClassical
        (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
        (fun stateFailure => EpsilonMaximum preferenceGap epsilon stateFailure.1) := by
  calc
    1 - (challengers.length : ℝ) * failureBudget ≤
        pmfProbClassical (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
          (fun stateFailure => -epsilon ≤ preferenceGap stateFailure.1 maximum) :=
      freshSeqEliminate_epsilonPreferableToAppearingMaximum_probability_of_historywiseCallBounds
        initial challengers outcomeLaw step bad preferenceGap epsilon failureBudget
        hantisymmetric hsst hepsilon maximum (hmaximum maximum) happears hvalid hfailure
    _ ≤ pmfProbClassical (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
        (fun stateFailure => EpsilonMaximum preferenceGap epsilon stateFailure.1) := by
          apply pmfProbClassical_le_of_imp
          intro stateFailure hpreferable
          exact epsilonMaximum_of_epsilonPreferableTo_absoluteMaximum preferenceGap epsilon
            hantisymmetric hsst hepsilon maximum stateFailure.1 hmaximum hpreferable

/--
The same fresh-call probability argument on a list-local maximum. This is the
Seq-Eliminate result needed when Pick-Anchor operates only on its sample `Q`.
-/
theorem freshSeqEliminate_listEpsilonMaximum_probability_of_historywiseCallBounds
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (initial : Arm) (challengers : List Arm)
    (outcomeLaw : AdaptiveOutcomeKernel Arm Outcome)
    (step : ℕ → Arm → Arm → Outcome → Arm)
    (bad : ℕ → Arm → Outcome → Prop)
    [∀ queryIndex incumbent outcome, Decidable (bad queryIndex incumbent outcome)]
    (preferenceGap : Arm → Arm → ℝ) (epsilon failureBudget : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum : Arm) (hmaximum : ListAbsoluteMaximum preferenceGap maximum initial challengers)
    (hvalid : ∀ queryIndex < challengers.length, ∀ incumbent outcome,
      ¬ bad queryIndex incumbent outcome →
        0 ≤ preferenceGap
          (step queryIndex incumbent (challengers.getD queryIndex initial) outcome) incumbent ∧
        -epsilon ≤ preferenceGap
          (step queryIndex incumbent (challengers.getD queryIndex initial) outcome)
          (challengers.getD queryIndex initial))
    (hfailure : ∀ queryIndex incumbent,
      pmfProb (outcomeLaw queryIndex incumbent) (bad queryIndex incumbent) ≤ failureBudget) :
    1 - (challengers.length : ℝ) * failureBudget ≤
      pmfProbClassical
        (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
        (fun stateFailure =>
          ListEpsilonMaximum preferenceGap epsilon initial challengers stateFailure.1) := by
  have happears : initial = maximum ∨ maximum ∈ challengers := by
    rcases hmaximum.1 with hmaximumInitial | hmaximumMem
    · exact Or.inl hmaximumInitial.symm
    · exact Or.inr hmaximumMem
  calc
    1 - (challengers.length : ℝ) * failureBudget ≤
        pmfProbClassical (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
          (fun stateFailure => -epsilon ≤ preferenceGap stateFailure.1 maximum) :=
      freshSeqEliminate_epsilonPreferableToAppearingMaximum_probability_of_historywiseCallBounds
        initial challengers outcomeLaw step bad preferenceGap epsilon failureBudget
        hantisymmetric hsst hepsilon maximum (hmaximum.2 maximum hmaximum.1)
        happears hvalid hfailure
    _ ≤ pmfProbClassical (freshSeqEliminateStateLaw initial challengers outcomeLaw step bad)
        (fun stateFailure =>
          ListEpsilonMaximum preferenceGap epsilon initial challengers stateFailure.1) := by
          apply pmfProbClassical_le_of_imp
          intro stateFailure hpreferable
          exact listEpsilonMaximum_of_epsilonPreferableTo_listAbsoluteMaximum
            preferenceGap epsilon hantisymmetric hsst hepsilon maximum stateFailure.1
            initial challengers hmaximum hpreferable

/--
One fresh adaptive `Compare` call has its Lemma-11/12 failure probability
under a finite PMF outcome law.  This is the finite-law bridge used for the
history-dependent calls in Seq-Eliminate.
-/
theorem adaptiveCompareStepCallInvalid_pmf_probability_of_ceilingBudget
    {Arm Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    (law : PMF Outcome) (observation : Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ)
    (incumbent challenger : Arm)
    (hindependent : iIndepFun (observation challenger incumbent) law.toMeasure)
    (hmeasurable : ∀ sampleIndex,
      Measurable (observation challenger incumbent sampleIndex))
    (hbounded : ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
      ∀ᵐ outcome ∂law.toMeasure,
        observation challenger incumbent sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
      law.toMeasure[observation challenger incumbent sampleIndex] =
        1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    pmfProbClassical law (fun outcome =>
      ¬ AdaptiveCompareStepCallValid observation (fixedSampleBudget 0 epsilon eta)
        preferenceGap epsilon eta outcome incumbent challenger) ≤ eta := by
  classical
  by_cases hsmall : preferenceGap challenger incumbent ≤ 0
  · calc
      pmfProbClassical law (fun outcome =>
          ¬ AdaptiveCompareStepCallValid observation (fixedSampleBudget 0 epsilon eta)
            preferenceGap epsilon eta outcome incumbent challenger) ≤
          pmfProbClassical law (fun outcome => adaptiveCompare
            (observation challenger incumbent) (fixedSampleBudget 0 epsilon eta)
            0 epsilon eta outcome ≠ .lower) := by
              apply pmfProbClassical_le_of_imp
              intro outcome hinvalid
              by_contra hdecision
              have hdecision' : adaptiveCompare (observation challenger incumbent)
                  (fixedSampleBudget 0 epsilon eta) 0 epsilon eta outcome = .lower := hdecision
              apply hinvalid
              unfold AdaptiveCompareStepCallValid
              simp only [adaptiveCompareStep, hdecision']
              constructor
              · rw [hself]
              · rw [hantisymmetric challenger incumbent]
                linarith
      _ = law.toMeasure.real {outcome | adaptiveCompare
          (observation challenger incumbent) (fixedSampleBudget 0 epsilon eta)
          0 epsilon eta outcome ≠ .lower} := by
        rw [pmfProbClassical_eq_pmfProb]
        exact AppliedModelingLib.pmfProb_eq_toMeasure_real law _
      _ ≤ eta := by
        apply adaptiveCompare_lower_failure_probability_of_ceilingBudget law.toMeasure
          (observation challenger incumbent) 0 epsilon
          (preferenceGap challenger incumbent) eta
        · exact hindependent
        · exact hmeasurable
        · exact hbounded
        · exact hmean
        · exact hsmall
        · exact hepsilon
        · exact heta
        · exact hetaLeOne
  · have hpositive : 0 ≤ preferenceGap challenger incumbent :=
      le_of_lt (lt_of_not_ge hsmall)
    by_cases hlarge : epsilon ≤ preferenceGap challenger incumbent
    · calc
        pmfProbClassical law (fun outcome =>
            ¬ AdaptiveCompareStepCallValid observation (fixedSampleBudget 0 epsilon eta)
              preferenceGap epsilon eta outcome incumbent challenger) ≤
            pmfProbClassical law (fun outcome => adaptiveCompare
              (observation challenger incumbent) (fixedSampleBudget 0 epsilon eta)
              0 epsilon eta outcome ≠ .upper) := by
                apply pmfProbClassical_le_of_imp
                intro outcome hinvalid
                by_contra hdecision
                have hdecision' : adaptiveCompare (observation challenger incumbent)
                    (fixedSampleBudget 0 epsilon eta) 0 epsilon eta outcome = .upper := hdecision
                apply hinvalid
                unfold AdaptiveCompareStepCallValid
                simp only [adaptiveCompareStep, hdecision']
                constructor
                · exact hpositive
                · rw [hself]
                  linarith
        _ = law.toMeasure.real {outcome | adaptiveCompare
            (observation challenger incumbent) (fixedSampleBudget 0 epsilon eta)
            0 epsilon eta outcome ≠ .upper} := by
          rw [pmfProbClassical_eq_pmfProb]
          exact AppliedModelingLib.pmfProb_eq_toMeasure_real law _
        _ ≤ eta := by
          apply adaptiveCompare_upper_failure_probability_of_ceilingBudget law.toMeasure
            (observation challenger incumbent) 0 epsilon
            (preferenceGap challenger incumbent) eta
          · exact hindependent
          · exact hmeasurable
          · exact hbounded
          · exact hmean
          · exact hlarge
          · exact hepsilon
          · exact heta
          · exact hetaLeOne
    · have hmiddle : preferenceGap challenger incumbent ≤ epsilon := le_of_not_ge hlarge
      have hallValid : ∀ outcome,
          AdaptiveCompareStepCallValid observation (fixedSampleBudget 0 epsilon eta)
            preferenceGap epsilon eta outcome incumbent challenger := by
        intro outcome
        exact adaptiveCompareStepCallValid_of_middleGap observation
          (fixedSampleBudget 0 epsilon eta) preferenceGap epsilon eta outcome
          hantisymmetric hself incumbent challenger hpositive hmiddle
      have hzero : pmfProbClassical law (fun outcome =>
          ¬ AdaptiveCompareStepCallValid observation (fixedSampleBudget 0 epsilon eta)
            preferenceGap epsilon eta outcome incumbent challenger) = 0 := by
        rw [pmfProbClassical_eq_pmfProb]
        apply pmfProb_eq_zero_of_no_mass
        intro outcome hinvalid
        exact (hinvalid (hallValid outcome)).elim
      rw [hzero]
      exact le_of_lt heta

/--
The outcome law for a source Seq-Eliminate run in which every call receives a
fresh adaptive Compare batch after its current incumbent is selected.
-/
noncomputable def freshAdaptiveCompareSeqEliminateStateLaw
    {Arm Outcome : Type*} [Fintype Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (initial : Arm) (challengers : List Arm)
    (outcomeLaw : AdaptiveOutcomeKernel Arm Outcome)
    (observation : ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ) :
    PMF (Arm × Bool) := by
  classical
  exact freshSeqEliminateStateLaw initial challengers outcomeLaw
    (fun queryIndex incumbent challenger outcome =>
      adaptiveCompareStep (observation queryIndex)
        (fixedSampleBudget 0 epsilon eta) epsilon eta outcome incumbent challenger)
    (fun queryIndex incumbent outcome =>
      if _ : queryIndex < challengers.length then
        ¬ AdaptiveCompareStepCallValid (observation queryIndex)
          (fixedSampleBudget 0 epsilon eta) preferenceGap epsilon eta outcome incumbent
            (challengers.getD queryIndex initial)
      else False)

/--
The finite probability that a fresh-call adaptive Seq-Eliminate run returns
an `ε`-maximum. The noncomputable wrapper keeps finite-state decidability
internal to the execution model rather than the paper-facing theorem.
-/
noncomputable def freshAdaptiveCompareSeqEliminateEpsilonMaximumProbability
    {Arm Outcome : Type*} [Fintype Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (initial : Arm) (challengers : List Arm)
    (outcomeLaw : AdaptiveOutcomeKernel Arm Outcome)
    (observation : ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ) : ℝ := by
  classical
  exact pmfProbClassical
    (freshAdaptiveCompareSeqEliminateStateLaw initial challengers outcomeLaw
      observation preferenceGap epsilon eta)
    (fun stateFailure => EpsilonMaximum preferenceGap epsilon stateFailure.1)

/--
Theorem 2 with the source's concrete adaptive Compare batches.  Fresh
comparison randomness may depend on the incumbent produced by the preceding
history, while the iid concentration hypotheses hold for every resulting
historywise call law.
-/
theorem freshAdaptiveCompareSeqEliminate_epsilonMaximum_probability
    {Arm Outcome : Type*} [Fintype Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    (initial : Arm) (challengers : List Arm)
    (outcomeLaw : AdaptiveOutcomeKernel Arm Outcome)
    (observation : ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ)
    (hindependent : ∀ queryIndex < challengers.length, ∀ incumbent,
      iIndepFun (observation queryIndex (challengers.getD queryIndex initial) incumbent)
        (outcomeLaw queryIndex incumbent).toMeasure)
    (hmeasurable : ∀ queryIndex < challengers.length, ∀ incumbent sampleIndex,
      Measurable (observation queryIndex (challengers.getD queryIndex initial) incumbent sampleIndex))
    (hbounded : ∀ queryIndex < challengers.length, ∀ incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
        ∀ᵐ outcome ∂(outcomeLaw queryIndex incumbent).toMeasure,
          observation queryIndex (challengers.getD queryIndex initial) incumbent sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ queryIndex < challengers.length, ∀ incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
        (outcomeLaw queryIndex incumbent).toMeasure[
          observation queryIndex (challengers.getD queryIndex initial) incumbent sampleIndex] =
            1 / 2 + preferenceGap (challengers.getD queryIndex initial) incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1)
    (maximum : Arm) (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (happears : initial = maximum ∨ maximum ∈ challengers) :
    1 - (challengers.length : ℝ) * eta ≤
      freshAdaptiveCompareSeqEliminateEpsilonMaximumProbability initial challengers
        outcomeLaw observation preferenceGap epsilon eta := by
  classical
  unfold freshAdaptiveCompareSeqEliminateEpsilonMaximumProbability
  unfold freshAdaptiveCompareSeqEliminateStateLaw
  apply freshSeqEliminate_epsilonMaximum_probability_of_historywiseCallBounds
    initial challengers outcomeLaw
    (fun queryIndex incumbent challenger outcome =>
      adaptiveCompareStep (observation queryIndex)
        (fixedSampleBudget 0 epsilon eta) epsilon eta outcome incumbent challenger)
    (fun queryIndex incumbent outcome =>
      if _ : queryIndex < challengers.length then
        ¬ AdaptiveCompareStepCallValid (observation queryIndex)
          (fixedSampleBudget 0 epsilon eta) preferenceGap epsilon eta outcome incumbent
            (challengers.getD queryIndex initial)
      else False)
    preferenceGap epsilon eta hantisymmetric hsst (le_of_lt hepsilon)
    maximum hmaximum happears
  · intro queryIndex hqueryIndex incumbent outcome hnotBad
    simp only [dif_pos hqueryIndex] at hnotBad
    exact Classical.not_not.mp hnotBad
  · intro queryIndex incumbent
    by_cases hqueryIndex : queryIndex < challengers.length
    · simp only [dif_pos hqueryIndex]
      rw [← pmfProbClassical_eq_pmfProb]
      refine adaptiveCompareStepCallInvalid_pmf_probability_of_ceilingBudget
        (outcomeLaw queryIndex incumbent) (observation queryIndex) preferenceGap epsilon eta
        incumbent (challengers.getD queryIndex initial) ?_ ?_ ?_ ?_ hantisymmetric hself
        hepsilon heta hetaLeOne
      · exact hindependent queryIndex hqueryIndex incumbent
      · exact hmeasurable queryIndex hqueryIndex incumbent
      · exact hbounded queryIndex hqueryIndex incumbent
      · exact hmean queryIndex hqueryIndex incumbent
    · simp only [dif_neg hqueryIndex, pmfProb_false]
      exact le_of_lt heta

/-- The finite probability that a fresh-call run is an `ε`-maximum of its input list. -/
noncomputable def freshAdaptiveCompareSeqEliminateListEpsilonMaximumProbability
    {Arm Outcome : Type*} [Fintype Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (initial : Arm) (challengers : List Arm)
    (outcomeLaw : AdaptiveOutcomeKernel Arm Outcome)
    (observation : ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ) : ℝ := by
  classical
  exact pmfProbClassical
    (freshAdaptiveCompareSeqEliminateStateLaw initial challengers outcomeLaw
      observation preferenceGap epsilon eta)
    (fun stateFailure =>
      ListEpsilonMaximum preferenceGap epsilon initial challengers stateFailure.1)

/--
Fresh adaptive Compare batches make Seq-Eliminate return an `ε`-maximum of
one finite input list. This is the source-local form used by Pick-Anchor.
-/
theorem freshAdaptiveCompareSeqEliminate_listEpsilonMaximum_probability
    {Arm Outcome : Type*} [Fintype Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    (initial : Arm) (challengers : List Arm)
    (outcomeLaw : AdaptiveOutcomeKernel Arm Outcome)
    (observation : ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ)
    (hindependent : ∀ queryIndex < challengers.length, ∀ incumbent,
      iIndepFun (observation queryIndex (challengers.getD queryIndex initial) incumbent)
        (outcomeLaw queryIndex incumbent).toMeasure)
    (hmeasurable : ∀ queryIndex < challengers.length, ∀ incumbent sampleIndex,
      Measurable (observation queryIndex (challengers.getD queryIndex initial) incumbent sampleIndex))
    (hbounded : ∀ queryIndex < challengers.length, ∀ incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
        ∀ᵐ outcome ∂(outcomeLaw queryIndex incumbent).toMeasure,
          observation queryIndex (challengers.getD queryIndex initial) incumbent sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ queryIndex < challengers.length, ∀ incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
        (outcomeLaw queryIndex incumbent).toMeasure[
          observation queryIndex (challengers.getD queryIndex initial) incumbent sampleIndex] =
            1 / 2 + preferenceGap (challengers.getD queryIndex initial) incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1)
    (maximum : Arm) (hmaximum : ListAbsoluteMaximum preferenceGap maximum initial challengers) :
    1 - (challengers.length : ℝ) * eta ≤
      freshAdaptiveCompareSeqEliminateListEpsilonMaximumProbability initial challengers
        outcomeLaw observation preferenceGap epsilon eta := by
  classical
  unfold freshAdaptiveCompareSeqEliminateListEpsilonMaximumProbability
  unfold freshAdaptiveCompareSeqEliminateStateLaw
  apply freshSeqEliminate_listEpsilonMaximum_probability_of_historywiseCallBounds
    initial challengers outcomeLaw
    (fun queryIndex incumbent challenger outcome =>
      adaptiveCompareStep (observation queryIndex)
        (fixedSampleBudget 0 epsilon eta) epsilon eta outcome incumbent challenger)
    (fun queryIndex incumbent outcome =>
      if _ : queryIndex < challengers.length then
        ¬ AdaptiveCompareStepCallValid (observation queryIndex)
          (fixedSampleBudget 0 epsilon eta) preferenceGap epsilon eta outcome incumbent
            (challengers.getD queryIndex initial)
      else False)
    preferenceGap epsilon eta hantisymmetric hsst (le_of_lt hepsilon)
    maximum hmaximum
  · intro queryIndex hqueryIndex incumbent outcome hnotBad
    simp only [dif_pos hqueryIndex] at hnotBad
    exact Classical.not_not.mp hnotBad
  · intro queryIndex incumbent
    by_cases hqueryIndex : queryIndex < challengers.length
    · simp only [dif_pos hqueryIndex]
      rw [← pmfProbClassical_eq_pmfProb]
      refine adaptiveCompareStepCallInvalid_pmf_probability_of_ceilingBudget
        (outcomeLaw queryIndex incumbent) (observation queryIndex) preferenceGap epsilon eta
        incumbent (challengers.getD queryIndex initial) ?_ ?_ ?_ ?_ hantisymmetric hself
        hepsilon heta hetaLeOne
      · exact hindependent queryIndex hqueryIndex incumbent
      · exact hmeasurable queryIndex hqueryIndex incumbent
      · exact hbounded queryIndex hqueryIndex incumbent
      · exact hmean queryIndex hqueryIndex incumbent
    · simp only [dif_neg hqueryIndex, pmfProb_false]
      exact le_of_lt heta

end FalahatgarEtAl2017MaxingRanking
