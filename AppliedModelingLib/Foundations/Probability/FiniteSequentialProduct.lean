import AppliedModelingLib.Foundations.Probability.IndependentProduct

/-!
# Sequential realization of a finite independent product

A fixed finite sequence of fresh draws may be presented either as a recursive
sequential experiment or as the heterogeneous product PMF `pmfPi`.  This file
proves that the two presentations have exactly the same atom masses.  The
result is useful when a paper states a batch experiment but a concentration
argument is naturally expressed through a sequential filtration.
-/

namespace AppliedModelingLib

/-- Restrict a fixed finite schedule to an earlier prefix. -/
def fixedFiniteOutcomeSchedulePrefix
    {Outcome : Type*} {drawBudget drawCount : ℕ}
    (law : Fin drawBudget → PMF Outcome) (hdrawCount : drawCount ≤ drawBudget) :
    Fin drawCount → PMF Outcome := fun draw ↦
  law ⟨draw.1, Nat.lt_of_lt_of_le draw.2 hdrawCount⟩

@[simp]
theorem fixedFiniteOutcomeSchedulePrefix_castSucc
    {Outcome : Type*} {drawBudget drawCount : ℕ}
    (law : Fin drawBudget → PMF Outcome) (hdrawCount : drawCount + 1 ≤ drawBudget)
    (draw : Fin drawCount) :
    fixedFiniteOutcomeSchedulePrefix law hdrawCount draw.castSucc =
      fixedFiniteOutcomeSchedulePrefix law (Nat.le_of_succ_le hdrawCount) draw := rfl

@[simp]
theorem fixedFiniteOutcomeSchedulePrefix_last
    {Outcome : Type*} {drawBudget drawCount : ℕ}
    (law : Fin drawBudget → PMF Outcome) (hdrawCount : drawCount + 1 ≤ drawBudget) :
    fixedFiniteOutcomeSchedulePrefix law hdrawCount (Fin.last drawCount) =
      law ⟨drawCount, Nat.lt_of_succ_le hdrawCount⟩ := rfl

/-- Sequentially draw the first `drawCount` coordinates of a fixed finite
family of outcome laws. -/
noncomputable def fixedFiniteOutcomePrefixLaw
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    {drawBudget : ℕ} (law : Fin drawBudget → PMF Outcome) :
    (drawCount : ℕ) → drawCount ≤ drawBudget → PMF (Fin drawCount → Outcome)
  | 0, _ => PMF.pure Fin.elim0
  | drawCount + 1, hdrawCount =>
      (fixedFiniteOutcomePrefixLaw law drawCount
        (Nat.le_of_succ_le hdrawCount)).bind fun history =>
          (law ⟨drawCount, Nat.lt_of_succ_le hdrawCount⟩).map
            (fun outcome ↦ @Fin.snoc drawCount (fun _ ↦ Outcome) history outcome)

/-- Appending one fresh draw has a unique history/outcome preimage. -/
private theorem fixedFiniteOutcome_map_snoc_apply
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    {drawCount : ℕ} (response : PMF Outcome)
    (history target : Fin drawCount → Outcome) (outcome : Outcome) :
    PMF.map (fun fresh ↦ @Fin.snoc drawCount (fun _ ↦ Outcome) history fresh) response
        (@Fin.snoc drawCount (fun _ ↦ Outcome) target outcome) =
      if target = history then response outcome else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  by_cases htarget : target = history
  · subst target
    rw [Finset.sum_eq_single outcome]
    · simp
    · intro other _ hother
      rw [if_neg]
      intro hequal
      exact hother (Fin.snoc_inj.mp hequal).2.symm
    · simp
  · have hnoPreimage : ∀ other : Outcome,
        @Fin.snoc drawCount (fun _ ↦ Outcome) history other ≠
          @Fin.snoc drawCount (fun _ ↦ Outcome) target outcome := by
      intro other hequal
      exact htarget (Fin.snoc_inj.mp hequal).1.symm
    rw [if_neg htarget]
    apply Finset.sum_eq_zero
    intro other _
    rw [if_neg]
    exact (hnoPreimage other).symm

/-- The atom mass of the recursive prefix experiment is the product of its
coordinate masses. -/
theorem fixedFiniteOutcomePrefixLaw_apply
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    {drawBudget : ℕ} (law : Fin drawBudget → PMF Outcome) :
    ∀ (drawCount : ℕ) (hdrawCount : drawCount ≤ drawBudget)
      (history : Fin drawCount → Outcome),
      fixedFiniteOutcomePrefixLaw law drawCount hdrawCount history =
        ∏ draw : Fin drawCount,
          fixedFiniteOutcomeSchedulePrefix law hdrawCount draw (history draw) := by
  intro drawCount
  induction drawCount with
  | zero =>
      intro hdrawCount history
      have hhistory : history = Fin.elim0 := Subsingleton.elim _ _
      subst history
      simp [fixedFiniteOutcomePrefixLaw]
  | succ drawCount ih =>
      intro hdrawCount history
      cases history using Fin.snocCases with
      | snoc past outcome =>
          rw [fixedFiniteOutcomePrefixLaw]
          rw [PMF.bind_apply, tsum_fintype]
          simp_rw [fixedFiniteOutcome_map_snoc_apply]
          rw [Finset.sum_eq_single past]
          · rw [ih (Nat.le_of_succ_le hdrawCount) past,
              Fin.prod_univ_castSucc]
            simp
          · intro other _ hother
            simp [hother.symm]
          · simp

/-- Every prefix of a fixed sequential experiment is exactly its
heterogeneous independent product law. -/
theorem fixedFiniteOutcomePrefixLaw_eq_pmfPi
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    {drawBudget drawCount : ℕ} (law : Fin drawBudget → PMF Outcome)
    (hdrawCount : drawCount ≤ drawBudget) :
    fixedFiniteOutcomePrefixLaw law drawCount hdrawCount =
      pmfPi (fixedFiniteOutcomeSchedulePrefix law hdrawCount) := by
  apply PMF.ext
  intro history
  rw [fixedFiniteOutcomePrefixLaw_apply, pmfPi_apply]

/-- The complete sequential experiment has exactly the advertised batch
product law. -/
theorem fixedFiniteOutcomeLaw_eq_pmfPi
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    {drawBudget : ℕ} (law : Fin drawBudget → PMF Outcome) :
    fixedFiniteOutcomePrefixLaw law drawBudget (le_refl drawBudget) = pmfPi law := by
  simpa [fixedFiniteOutcomeSchedulePrefix] using
    fixedFiniteOutcomePrefixLaw_eq_pmfPi law (le_refl drawBudget)

/-- Pair one fixed context table with a table of coordinate outcomes. -/
def finiteCoordinateZip {Index Context Outcome : Type*}
    (context : Index → Context) (outcome : Index → Outcome) :
    Index → Context × Outcome := fun index ↦ (context index, outcome index)

/-- The coordinatewise zip map has exactly one outcome-table preimage when
its context table agrees with the target. -/
theorem pmfPi_map_finiteCoordinateZip_apply
    {Index Context Outcome : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype Context] [DecidableEq Context]
    [Fintype Outcome] [DecidableEq Outcome]
    (responseLaw : Index → PMF Outcome)
    (context : Index → Context) (target : Index → Context × Outcome) :
    (pmfPi responseLaw).map (finiteCoordinateZip context) target =
      if context = (fun index ↦ (target index).1) then
        pmfPi responseLaw (fun index ↦ (target index).2)
      else 0 := by
  classical
  rw [PMF.map_apply, tsum_fintype]
  by_cases hcontext : context = fun index ↦ (target index).1
  · subst context
    rw [if_pos rfl, Finset.sum_eq_single (fun index ↦ (target index).2)]
    · rw [if_pos]
      rfl
    · intro other _ hother
      rw [if_neg]
      intro hequal
      apply hother
      funext index
      exact (congrArg Prod.snd (congrFun hequal index)).symm
    · simp
  · rw [if_neg hcontext]
    apply Finset.sum_eq_zero
    intro other _
    rw [if_neg]
    intro hequal
    apply hcontext
    funext index
    exact (congrArg Prod.fst (congrFun hequal index)).symm

/-- One coordinate of a contextual draw followed by a conditional response
has the expected product atom mass. -/
theorem pmf_bind_map_pair_apply
    {Context Outcome : Type*}
    [Fintype Context] [DecidableEq Context]
    [Fintype Outcome] [DecidableEq Outcome]
    (contextLaw : PMF Context) (responseLaw : Context → PMF Outcome)
    (target : Context × Outcome) :
    (contextLaw.bind fun context ↦
      (responseLaw context).map (fun outcome ↦ (context, outcome))) target =
      contextLaw target.1 * responseLaw target.1 target.2 := by
  classical
  rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single target.1]
  · rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single target.2]
    · rw [if_pos]
      exact Prod.ext rfl rfl
    · intro other _ hother
      rw [if_neg]
      intro hequal
      exact hother (congrArg Prod.snd hequal).symm
    · simp
  · intro other _ hother
    have hmap : (responseLaw other).map (fun outcome ↦ (other, outcome)) target = 0 := by
      rw [PMF.map_apply, tsum_fintype]
      apply Finset.sum_eq_zero
      intro outcome _
      rw [if_neg]
      intro hequal
      exact hother (congrArg Prod.fst hequal).symm
    rw [hmap]
    simp
  · simp

/-- Drawing an independent table of contexts and then conditionally drawing
an independent response at every coordinate is exactly the independent table
of contextual one-coordinate draws. -/
theorem pmfPi_context_then_response_zip_eq
    {Index Context Outcome : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype Context] [DecidableEq Context]
    [Fintype Outcome] [DecidableEq Outcome]
    (contextLaw : Index → PMF Context)
    (responseLaw : Index → Context → PMF Outcome) :
    (pmfPi contextLaw).bind (fun context ↦
      (pmfPi (fun index ↦ responseLaw index (context index))).map
        (finiteCoordinateZip context)) =
      pmfPi (fun index ↦
        (contextLaw index).bind fun context ↦
          (responseLaw index context).map fun outcome ↦ (context, outcome)) := by
  classical
  apply PMF.ext
  intro target
  rw [PMF.bind_apply, tsum_fintype,
    Finset.sum_eq_single (fun index ↦ (target index).1)]
  · rw [pmfPi_map_finiteCoordinateZip_apply, if_pos rfl,
      pmfPi_apply, pmfPi_apply]
    calc
      (∏ index, contextLaw index (target index).1) *
          ∏ index, responseLaw index (target index).1 (target index).2 =
          ∏ index, contextLaw index (target index).1 *
            responseLaw index (target index).1 (target index).2 :=
        Finset.prod_mul_distrib.symm
      _ = ∏ index,
          ((contextLaw index).bind fun context ↦
            (responseLaw index context).map fun outcome ↦ (context, outcome))
              (target index) := by
        apply Finset.prod_congr rfl
        intro index _
        rw [pmf_bind_map_pair_apply]
  · intro other _ hother
    rw [pmfPi_map_finiteCoordinateZip_apply, if_neg hother]
    simp
  · simp

end AppliedModelingLib
