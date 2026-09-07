import FalahatgarEtAl2017MaxingRanking.AdaptiveSeqEliminate

/-!
# High-probability adaptive Seq-Eliminate

This file composes the exact adaptive-Compare guarantee over all potential
ordered arm pairs.  Preallocating a fresh iid comparison stream to each pair
is a finite product presentation of the source's fresh-comparisons model; the
realized Seq-Eliminate path consumes only its `challengers.length` streams.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The two inequalities required for one realized adaptive Seq-Eliminate call. -/
def AdaptiveCompareStepCallValid {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (count : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ) (outcome : Ω)
    (incumbent challenger : Arm) : Prop :=
  0 ≤ preferenceGap
      (adaptiveCompareStep observation count epsilon delta outcome incumbent challenger) incumbent ∧
    -epsilon ≤ preferenceGap
      (adaptiveCompareStep observation count epsilon delta outcome incumbent challenger) challenger

/-- A call in the indeterminate comparison interval is valid under either decision. -/
theorem adaptiveCompareStepCallValid_of_middleGap
    {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (count : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ) (outcome : Ω)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (incumbent challenger : Arm)
    (hpositive : 0 ≤ preferenceGap challenger incumbent)
    (hmiddle : preferenceGap challenger incumbent ≤ epsilon) :
    AdaptiveCompareStepCallValid observation count preferenceGap epsilon delta outcome
      incumbent challenger := by
  unfold AdaptiveCompareStepCallValid
  cases hdecision : adaptiveCompare (observation challenger incumbent) count 0 epsilon delta outcome with
  | lower =>
      simp only [adaptiveCompareStep, hdecision]
      constructor
      · rw [hself]
      · rw [hantisymmetric challenger incumbent]
        linarith
  | upper =>
      simp only [adaptiveCompareStep, hdecision]
      constructor
      · exact hpositive
      · rw [hself]
        linarith

/--
All ordered-pair calls satisfy Seq-Eliminate's local validity condition except
on an event of probability at most `delta`.  This simultaneous form remains
valid when a later algorithmic phase selects its challenger list from the
same preallocated comparison streams.
-/
theorem adaptiveCompare_allPairCallValid_failure_probability_of_ceilingBudget
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Arm → Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ)
    (hindependent : ∀ challenger incumbent,
      iIndepFun (observation challenger incumbent) law)
    (hmeasurable : ∀ challenger incumbent sample,
      Measurable (observation challenger incumbent sample))
    (hbounded : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)),
        ∀ᵐ outcome ∂law, observation challenger incumbent sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)),
        law[observation challenger incumbent sample] =
          1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | ∃ pair : Arm × Arm,
      ¬ AdaptiveCompareStepCallValid observation
        (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
        preferenceGap epsilon (delta / (Fintype.card (Arm × Arm) : ℝ))
        outcome pair.2 pair.1} ≤ delta := by
  let pairCount : ℕ := Fintype.card (Arm × Arm)
  let callDelta : ℝ := delta / (pairCount : ℝ)
  let budget : ℕ := fixedSampleBudget 0 epsilon callDelta
  let callValid : Arm × Arm → Ω → Prop := fun pair outcome =>
    AdaptiveCompareStepCallValid observation budget preferenceGap epsilon callDelta outcome pair.2 pair.1
  have hpairCount : 0 < pairCount := by
    unfold pairCount
    exact Fintype.card_pos
  have hpairCountReal : 0 < (pairCount : ℝ) := by exact_mod_cast hpairCount
  have hpairCountGeOne : 1 ≤ (pairCount : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hpairCount)
  have hcallDeltaPos : 0 < callDelta := by
    exact div_pos hdelta hpairCountReal
  have hcallDeltaLeOne : callDelta ≤ 1 := by
    have hle : delta / (pairCount : ℝ) ≤ delta := by
      apply (div_le_iff₀ hpairCountReal).mpr
      nlinarith
    exact hle.trans hdeltaLeOne
  have hbudget : budget = fixedSampleBudget 0 epsilon
      (delta / (Fintype.card (Arm × Arm) : ℝ)) := by
    rfl
  have hcall : ∀ pair : Arm × Arm,
      law.real {outcome | ¬ callValid pair outcome} ≤ callDelta := by
    rintro ⟨challenger, incumbent⟩
    by_cases hsmall : preferenceGap challenger incumbent ≤ 0
    · calc
        law.real {outcome | ¬ callValid (challenger, incumbent) outcome} ≤
            law.real {outcome | adaptiveCompare
              (observation challenger incumbent) budget 0 epsilon callDelta outcome ≠ .lower} := by
              refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
              intro outcome hinvalid
              by_contra hdecision
              have hdecision' : adaptiveCompare
                  (observation challenger incumbent) budget 0 epsilon callDelta outcome = .lower :=
                not_ne_iff.mp hdecision
              apply hinvalid
              unfold callValid AdaptiveCompareStepCallValid
              simp only [adaptiveCompareStep, hdecision']
              constructor
              · rw [hself]
              · rw [hantisymmetric challenger incumbent]
                linarith
        _ ≤ callDelta := by
          change law.real {outcome | adaptiveCompare
              (observation challenger incumbent)
                (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
                0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome ≠ .lower} ≤
              delta / (Fintype.card (Arm × Arm) : ℝ)
          apply adaptiveCompare_lower_failure_probability_of_ceilingBudget law
            (observation challenger incumbent) 0 epsilon
            (preferenceGap challenger incumbent) (delta / (Fintype.card (Arm × Arm) : ℝ))
          · exact hindependent challenger incumbent
          · exact hmeasurable challenger incumbent
          · exact hbounded challenger incumbent
          · exact hmean challenger incumbent
          · exact hsmall
          · exact hepsilon
          · exact hcallDeltaPos
          · exact hcallDeltaLeOne
    · have hpositive : 0 ≤ preferenceGap challenger incumbent :=
        le_of_lt (lt_of_not_ge hsmall)
      by_cases hlarge : epsilon ≤ preferenceGap challenger incumbent
      · calc
          law.real {outcome | ¬ callValid (challenger, incumbent) outcome} ≤
              law.real {outcome | adaptiveCompare
                (observation challenger incumbent) budget 0 epsilon callDelta outcome ≠ .upper} := by
                refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
                intro outcome hinvalid
                by_contra hdecision
                have hdecision' : adaptiveCompare
                    (observation challenger incumbent) budget 0 epsilon callDelta outcome = .upper :=
                  not_ne_iff.mp hdecision
                apply hinvalid
                unfold callValid AdaptiveCompareStepCallValid
                simp only [adaptiveCompareStep, hdecision']
                constructor
                · exact hpositive
                · rw [hself]
                  linarith
          _ ≤ callDelta := by
            change law.real {outcome | adaptiveCompare
                (observation challenger incumbent)
                  (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
                  0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome ≠ .upper} ≤
                delta / (Fintype.card (Arm × Arm) : ℝ)
            apply adaptiveCompare_upper_failure_probability_of_ceilingBudget law
              (observation challenger incumbent) 0 epsilon
              (preferenceGap challenger incumbent) (delta / (Fintype.card (Arm × Arm) : ℝ))
            · exact hindependent challenger incumbent
            · exact hmeasurable challenger incumbent
            · exact hbounded challenger incumbent
            · exact hmean challenger incumbent
            · exact hlarge
            · exact hepsilon
            · exact hcallDeltaPos
            · exact hcallDeltaLeOne
      · have hmiddle : preferenceGap challenger incumbent ≤ epsilon := le_of_not_ge hlarge
        have hallValid : ∀ outcome, callValid (challenger, incumbent) outcome := by
          intro outcome
          exact adaptiveCompareStepCallValid_of_middleGap observation budget preferenceGap
            epsilon callDelta outcome hantisymmetric hself incumbent challenger hpositive hmiddle
        have hempty : {outcome | ¬ callValid (challenger, incumbent) outcome} = ∅ := by
          ext outcome
          simp [hallValid outcome]
        rw [hempty]
        simp [le_of_lt hcallDeltaPos]
  have hunion : law.real {outcome | ∃ pair, ¬ callValid pair outcome} ≤ delta := by
    calc
      law.real {outcome | ∃ pair, ¬ callValid pair outcome} =
          law.real (⋃ pair ∈ (Finset.univ : Finset (Arm × Arm)),
            {outcome | ¬ callValid pair outcome}) := by
              congr 1
              ext outcome
              simp
      _ ≤ ∑ pair ∈ (Finset.univ : Finset (Arm × Arm)),
          law.real {outcome | ¬ callValid pair outcome} :=
        measureReal_biUnion_finset_le (Finset.univ : Finset (Arm × Arm))
          (fun pair => {outcome | ¬ callValid pair outcome})
      _ ≤ ∑ _pair ∈ (Finset.univ : Finset (Arm × Arm)), callDelta := by
        apply Finset.sum_le_sum
        intro pair _
        exact hcall pair
      _ = delta := by
        dsimp [callDelta, pairCount]
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [ne_of_gt hpairCountReal]
  simpa [callValid, budget, callDelta, pairCount] using hunion

/--
Appendix A.3 with the Appendix A.2 adaptive Compare implementation.  The
failure probability is at most `delta` after a finite union bound over all
ordered arm-pair streams.
-/
theorem adaptiveSeqEliminate_failure_probability_of_ceilingBudget
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Arm → Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ)
    (hindependent : ∀ challenger incumbent,
      iIndepFun (observation challenger incumbent) law)
    (hmeasurable : ∀ challenger incumbent sample,
      Measurable (observation challenger incumbent sample))
    (hbounded : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)),
        ∀ᵐ outcome ∂law, observation challenger incumbent sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)),
        law[observation challenger incumbent sample] =
          1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (maximum initial : Arm) (challengers : List Arm)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (happears : initial = maximum ∨ maximum ∈ challengers) :
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
      (sequentialEliminate
        (adaptiveCompareStep observation
          (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
          epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
        initial challengers)} ≤ delta := by
  calc
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
        (sequentialEliminate
          (adaptiveCompareStep observation
            (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
            epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
          initial challengers)} ≤
        law.real {outcome | ∃ pair : Arm × Arm,
          ¬ AdaptiveCompareStepCallValid observation
            (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
            preferenceGap epsilon (delta / (Fintype.card (Arm × Arm) : ℝ))
            outcome pair.2 pair.1} := by
              refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
              intro outcome hfailure
              by_contra hnoFailure
              apply hfailure
              exact sequentialEliminate_epsilonMaximum_of_maximumAppears preferenceGap epsilon
                (adaptiveCompareStep observation
                  (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
                  epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
                hantisymmetric hsst (le_of_lt hepsilon)
                (by
                  intro incumbent challenger
                  by_contra hinvalid
                  exact hnoFailure ⟨(challenger, incumbent), hinvalid⟩)
                maximum initial challengers hmaximum happears
    _ ≤ delta :=
      adaptiveCompare_allPairCallValid_failure_probability_of_ceilingBudget law
        observation preferenceGap epsilon delta hindependent hmeasurable hbounded hmean
        hantisymmetric hself hepsilon hdelta hdeltaLeOne

/--
The simultaneous all-pairs guarantee also applies to a challenger list chosen
by an earlier randomized phase.  This is the safe bridge needed for
OPT-Maximize: it does not condition on that phase or posit a new independent
Seq-Eliminate run.
-/
theorem adaptiveSeqEliminate_randomList_failure_probability_of_ceilingBudget
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Arm → Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ)
    (hindependent : ∀ challenger incumbent,
      iIndepFun (observation challenger incumbent) law)
    (hmeasurable : ∀ challenger incumbent sample,
      Measurable (observation challenger incumbent sample))
    (hbounded : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)),
        ∀ᵐ outcome ∂law, observation challenger incumbent sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)),
        law[observation challenger incumbent sample] =
          1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (maximum : Arm) (initial : Ω → Arm) (challengers : Ω → List Arm)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (happears : ∀ outcome,
      initial outcome = maximum ∨ maximum ∈ challengers outcome) :
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
      (sequentialEliminate
        (adaptiveCompareStep observation
          (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
          epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
        (initial outcome) (challengers outcome))} ≤ delta := by
  calc
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
        (sequentialEliminate
          (adaptiveCompareStep observation
            (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
            epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
          (initial outcome) (challengers outcome))} ≤
        law.real {outcome | ∃ pair : Arm × Arm,
          ¬ AdaptiveCompareStepCallValid observation
            (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
            preferenceGap epsilon (delta / (Fintype.card (Arm × Arm) : ℝ))
            outcome pair.2 pair.1} := by
              refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
              intro outcome hfailure
              by_contra hnoFailure
              apply hfailure
              exact sequentialEliminate_epsilonMaximum_of_maximumAppears preferenceGap epsilon
                (adaptiveCompareStep observation
                  (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
                  epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
                hantisymmetric hsst (le_of_lt hepsilon)
                (by
                  intro incumbent challenger
                  by_contra hinvalid
                  exact hnoFailure ⟨(challenger, incumbent), hinvalid⟩)
                maximum (initial outcome) (challengers outcome) hmaximum (happears outcome)
    _ ≤ delta :=
      adaptiveCompare_allPairCallValid_failure_probability_of_ceilingBudget law
        observation preferenceGap epsilon delta hindependent hmeasurable hbounded hmean
        hantisymmetric hself hepsilon hdelta hdeltaLeOne

/--
The form needed after Prune.  The candidate set and its enumeration may both
depend on the preceding phase's randomness; only on outcomes where that set
contains the absolute maximum does the Seq-Eliminate fallback need to be
correct.  A single all-pairs validity event proves exactly that conditional
claim without conditioning a dependent probability space.
-/
theorem adaptiveSeqEliminate_candidateContainsMax_failure_probability_of_ceilingBudget
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Arm → Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ)
    (hindependent : ∀ challenger incumbent,
      iIndepFun (observation challenger incumbent) law)
    (hmeasurable : ∀ challenger incumbent sample,
      Measurable (observation challenger incumbent sample))
    (hbounded : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)),
        ∀ᵐ outcome ∂law, observation challenger incumbent sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)),
        law[observation challenger incumbent sample] =
          1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (maximum : Arm) (candidates : Ω → Finset Arm)
    (initial : Ω → Arm) (challengers : Ω → List Arm)
    (henumerates : ∀ outcome, maximum ∈ candidates outcome →
      initial outcome :: challengers outcome = (candidates outcome).toList)
    (hmaximum : AbsoluteMaximum preferenceGap maximum) :
    law.real {outcome | maximum ∈ candidates outcome ∧
      ¬ EpsilonMaximum preferenceGap epsilon
        (sequentialEliminate
          (adaptiveCompareStep observation
            (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
            epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
          (initial outcome) (challengers outcome))} ≤ delta := by
  calc
    law.real {outcome | maximum ∈ candidates outcome ∧
        ¬ EpsilonMaximum preferenceGap epsilon
          (sequentialEliminate
            (adaptiveCompareStep observation
              (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
              epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
            (initial outcome) (challengers outcome))} ≤
        law.real {outcome | ∃ pair : Arm × Arm,
          ¬ AdaptiveCompareStepCallValid observation
            (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
            preferenceGap epsilon (delta / (Fintype.card (Arm × Arm) : ℝ))
            outcome pair.2 pair.1} := by
              refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
              intro outcome hfailure
              rcases hfailure with ⟨hmaximumMem, hseqFailure⟩
              by_contra hnoFailure
              apply hseqFailure
              apply sequentialEliminate_epsilonMaximum_of_maximumAppears preferenceGap epsilon
                (adaptiveCompareStep observation
                  (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
                  epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
                hantisymmetric hsst (le_of_lt hepsilon)
              · intro incumbent challenger
                by_contra hinvalid
                exact hnoFailure ⟨(challenger, incumbent), hinvalid⟩
              · exact hmaximum
              · have hmaximumList : maximum ∈ initial outcome :: challengers outcome := by
                  rw [henumerates outcome hmaximumMem]
                  exact Finset.mem_toList.mpr hmaximumMem
                rcases (by simpa only [List.mem_cons] using hmaximumList) with hhead | htail
                · exact Or.inl hhead.symm
                · exact Or.inr htail
    _ ≤ delta :=
      adaptiveCompare_allPairCallValid_failure_probability_of_ceilingBudget law
        observation preferenceGap epsilon delta hindependent hmeasurable hbounded hmean
        hantisymmetric hself hepsilon hdelta hdeltaLeOne

end FalahatgarEtAl2017MaxingRanking
