import AppliedModelingLib.Foundations.Probability.FiniteExpectation

/-!
# Finite PAC event composition

Finite preference-RL algorithms invoke many randomized subroutines. This module
records the union-bound step that turns a common per-call failure budget into a
simultaneous success probability.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- Finite-PMF event probability with classical decidability kept out of public interfaces. -/
noncomputable def pmfProbClassical {Outcome : Type*} [Fintype Outcome]
    (law : PMF Outcome) (event : Outcome → Prop) : ℝ := by
  classical
  exact pmfProb law event

/-- The classical wrapper agrees with any supplied finite-event decider. -/
theorem pmfProbClassical_eq_pmfProb
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (event : Outcome → Prop) [DecidablePred event] :
    pmfProbClassical law event = pmfProb law event := by
  classical
  unfold pmfProbClassical pmfProb
  apply pmfExp_congr
  intro outcome
  by_cases hevent : event outcome <;> simp [hevent]

/-- Classical finite-event probability commutes with pushforward. -/
theorem pmfProbClassical_map
    {Input Output : Type*}
    [Fintype Input] [Fintype Output]
    (law : PMF Input) (transform : Input → Output) (event : Output → Prop) :
    pmfProbClassical (law.map transform) event =
      pmfProbClassical law (fun input => event (transform input)) := by
  classical
  rw [pmfProbClassical_eq_pmfProb, pmfProbClassical_eq_pmfProb, pmfProb_map]

/-- Classical finite-event probability obeys the complement rule. -/
theorem pmfProbClassical_compl
    {Outcome : Type*} [Fintype Outcome]
    (law : PMF Outcome) (event : Outcome → Prop) :
    pmfProbClassical law (fun outcome => ¬ event outcome) =
      1 - pmfProbClassical law event := by
  classical
  rw [pmfProbClassical_eq_pmfProb, pmfProbClassical_eq_pmfProb, pmfProb_compl]
/-- The classical finite-event wrapper is independent of the particular
decision procedure chosen for its finite outcome type. -/
theorem pmfProbClassical_congr_decidableEq
    {Outcome : Type*} [Fintype Outcome]
    (outcomeDecidableEq₁ outcomeDecidableEq₂ : DecidableEq Outcome)
    (law : PMF Outcome) (event : Outcome → Prop) :
    (letI : DecidableEq Outcome := outcomeDecidableEq₁
     pmfProbClassical law event) =
    (letI : DecidableEq Outcome := outcomeDecidableEq₂
     pmfProbClassical law event) := by
  rfl

/-- Event probability is monotone under logical implication, without decidability in the interface. -/
theorem pmfProbClassical_le_of_imp
    {Outcome : Type*} [Fintype Outcome]
    (law : PMF Outcome) (first second : Outcome → Prop)
    (himp : ∀ outcome, first outcome → second outcome) :
    pmfProbClassical law first ≤ pmfProbClassical law second := by
  classical
  change pmfProb law first ≤ pmfProb law second
  exact pmfProb_le_of_imp law first second himp

/-- Event probability is monotone when the implication is required only on
the support of the finite law.  Outcomes outside that support have zero
mass, so this is the natural form for operational invariants. -/
theorem pmfProbClassical_le_of_support_imp
    {Outcome : Type*} [Fintype Outcome]
    (law : PMF Outcome) (first second : Outcome → Prop)
    (himp : ∀ outcome ∈ law.support, first outcome → second outcome) :
    pmfProbClassical law first ≤ pmfProbClassical law second := by
  classical
  change pmfExp law (fun outcome => if first outcome then 1 else 0) ≤
    pmfExp law (fun outcome => if second outcome then 1 else 0)
  unfold pmfExp
  apply Finset.sum_le_sum
  intro outcome _
  by_cases hsupport : outcome ∈ law.support
  · have hindicator : (if first outcome then (1 : ℝ) else 0) ≤
        if second outcome then 1 else 0 := by
      by_cases hfirst : first outcome
      · simp [hfirst, himp outcome hsupport hfirst]
      · by_cases hsecond : second outcome <;> simp [hfirst, hsecond]
    exact mul_le_mul_of_nonneg_left hindicator ENNReal.toReal_nonneg
  · have hzero : law outcome = 0 := by
      by_contra hnonzero
      exact hsupport ((law.mem_support_iff outcome).mpr hnonzero)
    simp [hzero]

/-- Classical finite-event probability depends only on the event extension. -/
theorem pmfProbClassical_congr
    {Outcome : Type*} [Fintype Outcome]
    (law : PMF Outcome) (first second : Outcome → Prop)
    (hiff : ∀ outcome, first outcome ↔ second outcome) :
    pmfProbClassical law first = pmfProbClassical law second := by
  apply le_antisymm
  · exact pmfProbClassical_le_of_imp law first second
      (fun outcome => (hiff outcome).mp)
  · exact pmfProbClassical_le_of_imp law second first
      (fun outcome => (hiff outcome).mpr)

/-- All indexed randomized subroutines succeed on this outcome. -/
def AllPACSucceed {Index Outcome : Type*}
    (failure : Index → Outcome → Prop) (outcome : Outcome) : Prop :=
  ∀ index, ¬ failure index outcome

/--
If each of finitely many PAC subroutines fails with probability at most
`delta / card`, then they all succeed with probability at least `1 - delta`.
-/
theorem pmfProb_allPACSucceed_ge_one_sub
    {Index Outcome : Type*} [Fintype Index] [Nonempty Index]
    [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (failure : Index → Outcome → Prop)
    (delta : ℝ)
    (hfailure : ∀ index,
      pmfProbClassical law (failure index) ≤ delta / (Fintype.card Index : ℝ)) :
    1 - delta ≤ pmfProbClassical law (AllPACSucceed failure) := by
  classical
  change 1 - delta ≤ pmfProb law (AllPACSucceed failure)
  have hfailure' : ∀ index,
      pmfProb law (failure index) ≤ delta / (Fintype.card Index : ℝ) := by
    intro index
    simpa [pmfProbClassical] using hfailure index
  have hunion := pmfProb_exists_le_card_mul law failure
    (delta / (Fintype.card Index : ℝ)) hfailure'
  have hcardPositive : 0 < (Fintype.card Index : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hscaled :
      (Fintype.card Index : ℝ) * (delta / (Fintype.card Index : ℝ)) = delta := by
    field_simp [ne_of_gt hcardPositive]
  have hunion' : pmfProb law (fun outcome => ∃ index, failure index outcome) ≤ delta := by
    linarith
  have hsuccessEq :
      pmfProb law (AllPACSucceed failure) =
        pmfProb law (fun outcome => ¬ ∃ index, failure index outcome) := by
    apply pmfProb_congr
    intro outcome
    simp [AllPACSucceed]
  rw [hsuccessEq, pmfProb_compl]
  linarith

/-- Two finite-PMF success certificates hold simultaneously with the sum of
their failure budgets. -/
theorem pmfProb_and_ge_one_sub_add
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (first second : Outcome → Prop)
    [DecidablePred first] [DecidablePred second]
    (firstFailure secondFailure : ℝ)
    (hfirst : 1 - firstFailure ≤ pmfProb law first)
    (hsecond : 1 - secondFailure ≤ pmfProb law second) :
    1 - (firstFailure + secondFailure) ≤
      pmfProb law (fun outcome => first outcome ∧ second outcome) := by
  classical
  have hnotFirst : pmfProb law (fun outcome => ¬ first outcome) ≤ firstFailure := by
    rw [pmfProb_compl]
    linarith
  have hnotSecond : pmfProb law (fun outcome => ¬ second outcome) ≤ secondFailure := by
    rw [pmfProb_compl]
    linarith
  have hunion := pmfProb_or_le law (fun outcome => ¬ first outcome)
    (fun outcome => ¬ second outcome)
  have hcomplement :
      pmfProb law (fun outcome => ¬ (first outcome ∧ second outcome)) =
        pmfProb law (fun outcome => ¬ first outcome ∨ ¬ second outcome) := by
    apply pmfProb_congr
    intro outcome
    tauto
  calc
    1 - (firstFailure + secondFailure) ≤
        1 - pmfProb law (fun outcome => ¬ (first outcome ∧ second outcome)) := by
          rw [hcomplement]
          linarith
    _ = pmfProb law (fun outcome => first outcome ∧ second outcome) := by
          rw [pmfProb_compl]
          ring

end PreferenceRL

end AppliedModelingLib
