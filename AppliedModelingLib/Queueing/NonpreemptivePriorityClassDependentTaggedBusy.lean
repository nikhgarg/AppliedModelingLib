import AppliedModelingLib.Queueing.NonpreemptivePriorityClassDependentPhysicalBusyPeriod

/-!
# Tagged customers in a class-dependent priority event chain

This module adds one distinguished customer to the embedded
class-dependent nonpreemptive-priority queue.  The tag records its class and
the number of same-class customers that were ahead of it at the last event.
FIFO within that class means an active service of the tag's class removes a
positive predecessor count first, and removes the tag when that count is zero.

The resulting pathwise result is deliberately finite-start: the holding time
until the tag completes is bounded by the queue's busy holding time.  A later
stationary/Palm construction must still prove that its selected arrival has
this event-chain law.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

/-- An embedded priority-queue state together with an optional distinguished
customer.  When present, the natural number is the count of same-class jobs
that precede the tag. -/
structure ClassDependentNonpreemptivePriorityTaggedState (n : ℕ) where
  queue : NonpreemptivePriorityState n
  tag : Option (Fin n × ℕ)

/-- Admit a distinguished class-`i` customer after all customers already in
the displayed state.  The existing class population is exactly its initial
same-class predecessor count. -/
def admitClassDependentNonpreemptivePriorityTag
    {n : ℕ} (state : NonpreemptivePriorityState n) (i : Fin n) :
    ClassDependentNonpreemptivePriorityTaggedState n where
  queue := arriveNonpreemptivePriority state i
  tag := some (i, classNonpreemptivePriorityJobs state i)

/-- The one-event update of a queue carrying a distinguished customer.
Potential completions only remove the tag when they complete an active job of
its own class after all older same-class customers have completed. -/
noncomputable def stepClassDependentNonpreemptivePriorityTag
    {n : ℕ} (state : ClassDependentNonpreemptivePriorityTaggedState n)
    (event : ClassDependentNonpreemptivePriorityEvent n) :
    ClassDependentNonpreemptivePriorityTaggedState n :=
  { queue := stepClassDependentNonpreemptivePriority state.queue event
    tag :=
      match state.tag, event with
      | none, _ => none
      | some tag, .inl _ => some tag
      | some (tagClass, predecessorCount), .inr completionClass =>
          if state.queue.active = some completionClass then
            if completionClass = tagClass then
              match predecessorCount with
              | 0 => none
              | predecessorCount + 1 => some (tagClass, predecessorCount)
            else some (tagClass, predecessorCount)
          else some (tagClass, predecessorCount) }

/-- Forgetting the tag commutes with every embedded event update. -/
theorem stepClassDependentNonpreemptivePriorityTag_queue
    {n : ℕ} (state : ClassDependentNonpreemptivePriorityTaggedState n)
    (event : ClassDependentNonpreemptivePriorityEvent n) :
    (stepClassDependentNonpreemptivePriorityTag state event).queue =
      stepClassDependentNonpreemptivePriority state.queue event := rfl

/-- A valid tagged state has an idle-consistent queue, and a live tag sits
strictly behind fewer same-class customers than that class's population. -/
def classDependentNonpreemptivePriorityTagValid
    {n : ℕ} (state : ClassDependentNonpreemptivePriorityTaggedState n) : Prop :=
  nonpreemptivePriorityStateIdleConsistent state.queue ∧
    ∀ tagClass predecessorCount,
      state.tag = some (tagClass, predecessorCount) →
        predecessorCount < classNonpreemptivePriorityJobs state.queue tagClass

/-- A freshly admitted tag satisfies the queue and FIFO predecessor
invariants.  Immediate admission itself repairs any otherwise latent idle
backlog by making the server active. -/
theorem classDependentNonpreemptivePriorityTagValid_admit
    {n : ℕ} (state : NonpreemptivePriorityState n) (i : Fin n) :
    classDependentNonpreemptivePriorityTagValid
      (admitClassDependentNonpreemptivePriorityTag state i) := by
  constructor
  · exact nonpreemptivePriorityStateIdleConsistent_arrive state i
  · intro tagClass predecessorCount htag
    simp only [admitClassDependentNonpreemptivePriorityTag] at htag ⊢
    have hclass := congrArg Prod.fst (Option.some.inj htag)
    have hcount := congrArg Prod.snd (Option.some.inj htag)
    change i = tagClass at hclass
    change classNonpreemptivePriorityJobs state i = predecessorCount at hcount
    subst tagClass
    subst predecessorCount
    rw [classNonpreemptivePriorityJobs_arrive]
    simp

/-- The tagged FIFO predecessor invariant survives one arrival or potential
completion event. -/
theorem classDependentNonpreemptivePriorityTagValid_step
    {n : ℕ} (state : ClassDependentNonpreemptivePriorityTaggedState n)
    (event : ClassDependentNonpreemptivePriorityEvent n)
    (hvalid : classDependentNonpreemptivePriorityTagValid state) :
    classDependentNonpreemptivePriorityTagValid
      (stepClassDependentNonpreemptivePriorityTag state event) := by
  classical
  rcases hvalid with ⟨hconsistent, htag⟩
  constructor
  · simpa [stepClassDependentNonpreemptivePriorityTag] using
      (nonpreemptivePriorityStateIdleConsistent_stepClassDependent
        state.queue event hconsistent)
  · intro tagClass predecessorCount htag'
    cases hstored : state.tag with
    | none =>
        simp [stepClassDependentNonpreemptivePriorityTag, hstored] at htag'
    | some stored =>
        rcases stored with ⟨storedClass, storedCount⟩
        cases event with
        | inl arrivalClass =>
            have hold := htag storedClass storedCount hstored
            simp only [stepClassDependentNonpreemptivePriorityTag, hstored] at htag'
            have hclass := congrArg Prod.fst (Option.some.inj htag')
            have hcount := congrArg Prod.snd (Option.some.inj htag')
            change storedClass = tagClass at hclass
            change storedCount = predecessorCount at hcount
            subst tagClass
            subst predecessorCount
            change storedCount < classNonpreemptivePriorityJobs
              (stepClassDependentNonpreemptivePriority state.queue (.inl arrivalClass))
              storedClass
            rw [classNonpreemptivePriorityJobs_stepClassDependent_arrival]
            split_ifs <;> omega
        | inr completionClass =>
            by_cases hactive : state.queue.active = some completionClass
            · by_cases hclass : completionClass = storedClass
              · subst completionClass
                cases hcount : storedCount with
                | zero =>
                    simp [stepClassDependentNonpreemptivePriorityTag, hstored,
                      hactive, hcount] at htag'
                | succ previousCount =>
                    have hstored' : state.tag = some (storedClass, previousCount + 1) := by
                      simpa [hcount] using hstored
                    have hold := htag storedClass (previousCount + 1) hstored'
                    have hpair : storedClass = tagClass ∧ previousCount = predecessorCount := by
                      simpa [stepClassDependentNonpreemptivePriorityTag, hstored,
                        hactive, hcount] using htag'
                    rcases hpair with ⟨htagClass, hpredecessorCount⟩
                    subst tagClass
                    subst predecessorCount
                    change previousCount < classNonpreemptivePriorityJobs
                      (stepClassDependentNonpreemptivePriority state.queue (.inr storedClass))
                      storedClass
                    have hcompletion :=
                      classNonpreemptivePriorityJobs_stepClassDependent_completion_of_active
                        state.queue storedClass storedClass hactive
                    simp only [if_pos] at hcompletion
                    omega
              · have hold := htag storedClass storedCount hstored
                have hpair : storedClass = tagClass ∧ storedCount = predecessorCount := by
                  simpa [stepClassDependentNonpreemptivePriorityTag, hstored,
                    hactive, hclass] using htag'
                rcases hpair with ⟨htagClass, hpredecessorCount⟩
                subst tagClass
                subst predecessorCount
                change storedCount < classNonpreemptivePriorityJobs
                  (stepClassDependentNonpreemptivePriority state.queue (.inr completionClass))
                  storedClass
                have hcompletion :=
                  classNonpreemptivePriorityJobs_stepClassDependent_completion_of_active
                    state.queue completionClass storedClass hactive
                have hne : storedClass ≠ completionClass := Ne.symm hclass
                simp only [if_neg hne, add_zero] at hcompletion
                rw [hcompletion]
                exact hold
            · have hold := htag storedClass storedCount hstored
              have hpair : storedClass = tagClass ∧ storedCount = predecessorCount := by
                simpa [stepClassDependentNonpreemptivePriorityTag, hstored,
                  hactive] using htag'
              rcases hpair with ⟨htagClass, hpredecessorCount⟩
              subst tagClass
              subst predecessorCount
              change storedCount < classNonpreemptivePriorityJobs
                (stepClassDependentNonpreemptivePriority state.queue (.inr completionClass))
                storedClass
              rw [stepClassDependentNonpreemptivePriority_completion_of_inactive
                state.queue completionClass hactive]
              exact hold

/-- A live tag prevents the embedded queue from being idle. -/
theorem ClassDependentNonpreemptivePriorityTaggedState.active_ne_none_of_tag_ne_none
    {n : ℕ} (state : ClassDependentNonpreemptivePriorityTaggedState n)
    (hvalid : classDependentNonpreemptivePriorityTagValid state)
    (htag : state.tag ≠ none) :
    state.queue.active ≠ none := by
  rcases hvalid with ⟨hconsistent, hpredecessor⟩
  cases hstored : state.tag with
  | none => exact (htag hstored).elim
  | some stored =>
      rcases stored with ⟨tagClass, predecessorCount⟩
      intro hidle
      have hlt := hpredecessor tagClass predecessorCount hstored
      have hwaiting := hconsistent hidle tagClass
      simp [classNonpreemptivePriorityJobs, hidle, hwaiting] at hlt

/-- Stop the tagged update once the underlying queue first becomes idle. -/
noncomputable def stopAtIdleClassDependentNonpreemptivePriorityTagStep
    {n : ℕ} (state : ClassDependentNonpreemptivePriorityTaggedState n)
    (event : ClassDependentNonpreemptivePriorityEvent n) :
    ClassDependentNonpreemptivePriorityTaggedState n :=
  if state.queue.active = none then state
  else stepClassDependentNonpreemptivePriorityTag state event

/-- Forgetting the tag also commutes with the idle-stopped update. -/
theorem stopAtIdleClassDependentNonpreemptivePriorityTagStep_queue
    {n : ℕ} (state : ClassDependentNonpreemptivePriorityTaggedState n)
    (event : ClassDependentNonpreemptivePriorityEvent n) :
    (stopAtIdleClassDependentNonpreemptivePriorityTagStep state event).queue =
      stopAtIdleClassDependentNonpreemptivePriorityStep state.queue event := by
  by_cases hidle : state.queue.active = none
  · simp [stopAtIdleClassDependentNonpreemptivePriorityTagStep,
      stopAtIdleClassDependentNonpreemptivePriorityStep, hidle]
  · rw [stopAtIdleClassDependentNonpreemptivePriorityTagStep, if_neg hidle,
      stopAtIdleClassDependentNonpreemptivePriorityStep, if_neg hidle]
    exact stepClassDependentNonpreemptivePriorityTag_queue state event

/-- Validity is preserved along the idle-stopped tagged event chain. -/
theorem classDependentNonpreemptivePriorityTagValid_stopAtIdleStep
    {n : ℕ} (state : ClassDependentNonpreemptivePriorityTaggedState n)
    (event : ClassDependentNonpreemptivePriorityEvent n)
    (hvalid : classDependentNonpreemptivePriorityTagValid state) :
    classDependentNonpreemptivePriorityTagValid
      (stopAtIdleClassDependentNonpreemptivePriorityTagStep state event) := by
  by_cases hidle : state.queue.active = none
  · simpa [stopAtIdleClassDependentNonpreemptivePriorityTagStep, hidle] using hvalid
  · simpa [stopAtIdleClassDependentNonpreemptivePriorityTagStep, hidle] using
      classDependentNonpreemptivePriorityTagValid_step state event hvalid

/-- The queue projection of every finite tagged trajectory is the ordinary
idle-stopped priority trajectory from the projected initial state. -/
theorem finiteEventTrajectory_stopAtIdleClassDependentNonpreemptivePriorityTag_queue
    {n : ℕ} (initial : ClassDependentNonpreemptivePriorityTaggedState n)
    (horizon : ℕ) (sample : Fin horizon → ClassDependentNonpreemptivePriorityEvent n) :
    (Probability.finiteEventTrajectory initial
      stopAtIdleClassDependentNonpreemptivePriorityTagStep horizon sample).queue =
      Probability.finiteEventTrajectory initial.queue
        stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample := by
  induction horizon with
  | zero => rfl
  | succ horizon ih =>
      simp only [Probability.finiteEventTrajectory]
      rw [stopAtIdleClassDependentNonpreemptivePriorityTagStep_queue, ih]

/-- A live tag at a finite stopped horizon makes the ordinary queue trajectory
busy at the same horizon. -/
theorem finiteEventTrajectory_tag_ne_none_imp_busy
    {n : ℕ} (initial : ClassDependentNonpreemptivePriorityTaggedState n)
    (hvalid : classDependentNonpreemptivePriorityTagValid initial)
    (horizon : ℕ) (sample : Fin horizon → ClassDependentNonpreemptivePriorityEvent n)
    (htag : (Probability.finiteEventTrajectory initial
      stopAtIdleClassDependentNonpreemptivePriorityTagStep horizon sample).tag ≠ none) :
    classDependentNonpreemptivePriorityBusy
      (Probability.finiteEventTrajectory initial.queue
        stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample) := by
  have htrajectoryValid : classDependentNonpreemptivePriorityTagValid
      (Probability.finiteEventTrajectory initial
        stopAtIdleClassDependentNonpreemptivePriorityTagStep horizon sample) := by
    exact Probability.finiteEventTrajectory_invariant initial
      stopAtIdleClassDependentNonpreemptivePriorityTagStep hvalid
      (fun state event hstate =>
        classDependentNonpreemptivePriorityTagValid_stopAtIdleStep state event hstate)
      horizon sample
  rw [← finiteEventTrajectory_stopAtIdleClassDependentNonpreemptivePriorityTag_queue]
  exact ClassDependentNonpreemptivePriorityTaggedState.active_ne_none_of_tag_ne_none
    _ htrajectoryValid htag

/-- The event that the tag has not yet completed after a finite stopped
event prefix. -/
def classDependentNonpreemptivePriorityTagBusyEvent
    {n : ℕ} (initial : ClassDependentNonpreemptivePriorityTaggedState n)
    (horizon : ℕ) : Set (ℕ → ClassDependentNonpreemptivePriorityEvent n) :=
  {omega | (Probability.finiteEventTrajectory initial
    stopAtIdleClassDependentNonpreemptivePriorityTagStep horizon
    (Probability.IIDStream.block 0 horizon omega)).tag ≠ none}

/-- Every finite tagged-busy event is Borel on the IID event stream. -/
theorem measurableSet_classDependentNonpreemptivePriorityTagBusyEvent
    {n : ℕ} (initial : ClassDependentNonpreemptivePriorityTaggedState n)
    (horizon : ℕ) :
    MeasurableSet (classDependentNonpreemptivePriorityTagBusyEvent initial horizon) := by
  let s : Set (Fin horizon → ClassDependentNonpreemptivePriorityEvent n) :=
    {sample | (Probability.finiteEventTrajectory initial
      stopAtIdleClassDependentNonpreemptivePriorityTagStep horizon sample).tag ≠ none}
  have hs : MeasurableSet s := (Set.toFinite s).measurableSet
  change MeasurableSet ((Probability.IIDStream.block 0 horizon) ⁻¹' s)
  exact hs.preimage (Probability.IIDStream.measurable_block 0 horizon)

/-- Tag survival at a finite event horizon is contained in ordinary queue
survival at that horizon. -/
theorem classDependentNonpreemptivePriorityTagBusyEvent_subset_busyEvent
    {n : ℕ} (initial : ClassDependentNonpreemptivePriorityTaggedState n)
    (hvalid : classDependentNonpreemptivePriorityTagValid initial)
    (horizon : ℕ) :
    classDependentNonpreemptivePriorityTagBusyEvent initial horizon ⊆
      classDependentNonpreemptivePriorityBusyEvent initial.queue horizon := by
  intro omega htag
  exact finiteEventTrajectory_tag_ne_none_imp_busy initial hvalid horizon
    (Probability.IIDStream.block 0 horizon omega) htag

/-- The physical holding time accrued while a distinguished customer is live.
The independent gap stream is the same one used for the ordinary busy period. -/
noncomputable def classDependentNonpreemptivePriorityTagHoldingTime
    {n : ℕ} (initial : ClassDependentNonpreemptivePriorityTaggedState n) :
    ((ℕ → ClassDependentNonpreemptivePriorityEvent n) × (ℕ → ℝ)) → ENNReal :=
  Probability.IIDStream.externalWeightedENNReward
    (classDependentNonpreemptivePriorityTagBusyEvent initial) ENNReal.ofReal

/-- A tagged customer's physical holding time is pathwise no greater than the
full busy holding time from the same post-arrival queue state. -/
theorem classDependentNonpreemptivePriorityTagHoldingTime_le_busyHoldingTime
    {n : ℕ} (initial : ClassDependentNonpreemptivePriorityTaggedState n)
    (hvalid : classDependentNonpreemptivePriorityTagValid initial)
    (path : (ℕ → ClassDependentNonpreemptivePriorityEvent n) × (ℕ → ℝ)) :
    classDependentNonpreemptivePriorityTagHoldingTime initial path ≤
      classDependentNonpreemptivePriorityBusyHoldingTime initial.queue path := by
  unfold classDependentNonpreemptivePriorityTagHoldingTime
    classDependentNonpreemptivePriorityBusyHoldingTime
    Probability.IIDStream.externalWeightedENNReward
  apply ENNReal.tsum_le_tsum
  intro horizon
  by_cases htag : path.1 ∈
      classDependentNonpreemptivePriorityTagBusyEvent initial horizon
  · have htag' : path ∈ Prod.fst ⁻¹'
        classDependentNonpreemptivePriorityTagBusyEvent initial horizon := htag
    have hbusy' : path ∈ Prod.fst ⁻¹'
        classDependentNonpreemptivePriorityBusyEvent initial.queue horizon :=
      classDependentNonpreemptivePriorityTagBusyEvent_subset_busyEvent
        initial hvalid horizon htag
    rw [Set.indicator_of_mem htag', Set.indicator_of_mem hbusy']
  · have htag' : path ∉ Prod.fst ⁻¹'
        classDependentNonpreemptivePriorityTagBusyEvent initial horizon := htag
    rw [Set.indicator_of_notMem htag']
    exact bot_le

/-- The tagged holding time evaluated on the canonical physical exponential
event race. -/
noncomputable def classDependentNonpreemptivePriorityEventRaceTagHoldingTime
    {n : ℕ} (initial : ClassDependentNonpreemptivePriorityTaggedState n) :
    (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n) → ENNReal :=
  fun path => classDependentNonpreemptivePriorityTagHoldingTime initial
    (Probability.finiteExponentialRaceWinnerGapPaths path)

/-- On the physical exponential event race, the tagged holding time is still
bounded pathwise by the full busy holding time of the projected queue. -/
theorem classDependentNonpreemptivePriorityEventRaceTagHoldingTime_le_busyHoldingTime
    {n : ℕ} (initial : ClassDependentNonpreemptivePriorityTaggedState n)
    (hvalid : classDependentNonpreemptivePriorityTagValid initial)
    (path : ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n) :
    classDependentNonpreemptivePriorityEventRaceTagHoldingTime initial path ≤
      classDependentNonpreemptivePriorityEventRaceBusyHoldingTime initial.queue path := by
  exact classDependentNonpreemptivePriorityTagHoldingTime_le_busyHoldingTime
    initial hvalid (Probability.finiteExponentialRaceWinnerGapPaths path)

/-- Evaluate a tagged physical event-race holding time after an external
initial-state draw. -/
noncomputable def externalInitialClassDependentNonpreemptivePriorityEventRaceTagHoldingTime
    {σ : Type*} {n : ℕ}
    (initial : σ → ClassDependentNonpreemptivePriorityTaggedState n) :
    (σ × (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n)) → ENNReal :=
  fun z => classDependentNonpreemptivePriorityEventRaceTagHoldingTime
    (initial z.1) z.2

/--
Under strict load, a tagged customer's physical holding time has finite
expectation from any independent random initial tagged state whose queue
projection has finite Lyapunov work.  The proof uses only pathwise domination
by the ordinary busy excursion; a stationary or Palm construction supplies
the product representation and finite initial-work hypothesis separately.
-/
theorem lintegral_externalInitialClassDependentNonpreemptivePriorityEventRaceTagHoldingTime_ne_top
    {σ : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : σ → ClassDependentNonpreemptivePriorityTaggedState n)
    (hvalid : ∀ x, classDependentNonpreemptivePriorityTagValid (initial x))
    (hcount : Measurable (fun z : σ ×
      (ℕ → ClassDependentNonpreemptivePriorityEvent n) =>
      classDependentNonpreemptivePriorityBusyEventCount (initial z.1).queue z.2))
    (hbusy : ∀ horizon, MeasurableSet
      (externalInitialClassDependentNonpreemptivePriorityBusyEvent
        (fun x => (initial x).queue) horizon))
    (hinitial : ∫⁻ x, ENNReal.ofReal
      (nonpreemptivePriorityMeanWork meanService (initial x).queue /
        classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService) ∂ρ ≠ ⊤) :
    ∫⁻ z, externalInitialClassDependentNonpreemptivePriorityEventRaceTagHoldingTime
      initial z ∂(ρ.prod (classDependentNonpreemptivePriorityEventRaceMeasure
        arrivalRate (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))) ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    (lintegral_externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime_ne_top
      ρ arrivalRate meanService hn harrivalRate hmeanService hstable
      (fun x => (initial x).queue) hcount hbusy hinitial)
  apply MeasureTheory.lintegral_mono
  intro z
  simpa [externalInitialClassDependentNonpreemptivePriorityEventRaceTagHoldingTime,
    externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime] using
    (classDependentNonpreemptivePriorityEventRaceTagHoldingTime_le_busyHoldingTime
      (initial z.1) (hvalid z.1) z.2)

end

end AppliedModelingLib.Queueing
