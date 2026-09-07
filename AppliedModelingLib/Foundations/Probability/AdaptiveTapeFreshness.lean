import AppliedModelingLib.Foundations.Probability.AdaptiveTape
import AppliedModelingLib.Foundations.Probability.HeterogeneousProductResampling

/-!
# Causal freshness of a finite adaptive tape

An adaptive tape run at a fixed horizon depends only on the entries that it
has already consumed.  This deterministic fact is the causal half of the
finite deferred-decision argument for an adaptively selected next cell.
-/

namespace AppliedModelingLib

/-- If two finite tapes agree at every entry consumed by the first run, their
completed adaptive event lists agree. -/
theorem adaptiveTapeEvents_eq_of_agree_on_consumed
    {Coordinate Data : Type*} {visitBudget : ℕ} [DecidableEq Coordinate]
    (tape tape' : Coordinate → Fin visitBudget → Data)
    (scheduler : AdaptiveTapeScheduler Coordinate Data) :
    ∀ (rounds : ℕ) (hrounds : rounds ≤ visitBudget),
      (∀ (coordinate : Coordinate) (visit : Fin visitBudget),
        visit.1 < adaptiveTapeVisitCount
            (adaptiveTapeEvents tape scheduler rounds hrounds) coordinate →
          tape coordinate visit = tape' coordinate visit) →
        adaptiveTapeEvents tape scheduler rounds hrounds =
          adaptiveTapeEvents tape' scheduler rounds hrounds
  | 0, _, _ => by
      simp [adaptiveTapeEvents, adaptiveTapeRun]
  | rounds + 1, hrounds, hagree => by
      let hprevious : rounds ≤ visitBudget := Nat.le_of_succ_le hrounds
      let previous := adaptiveTapeEvents tape scheduler rounds hprevious
      let selected := scheduler previous
      let consumed := adaptiveTapeVisitCount previous selected
      have hconsumed : consumed < visitBudget := by
        calc
          consumed ≤ previous.length := adaptiveTapeVisitCount_le_length previous selected
          _ = rounds := adaptiveTapeEvents_length tape scheduler rounds hprevious
          _ < rounds + 1 := Nat.lt_succ_self rounds
          _ ≤ visitBudget := hrounds
      have hfull :
          adaptiveTapeEvents tape scheduler (rounds + 1) hrounds =
            previous ++ [(selected, tape selected ⟨consumed, hconsumed⟩)] := by
        simpa [previous, selected, consumed] using
          (adaptiveTapeEvents_succ tape scheduler rounds hrounds)
      have hcount_le (coordinate : Coordinate) :
          adaptiveTapeVisitCount previous coordinate ≤
            adaptiveTapeVisitCount
              (adaptiveTapeEvents tape scheduler (rounds + 1) hrounds) coordinate := by
        rw [hfull, adaptiveTapeVisitCount_append_singleton]
        by_cases hselected : selected = coordinate
        · simp [hselected, Nat.le_add_right]
        · simp [hselected]
      have hagree_previous :
          ∀ (coordinate : Coordinate) (visit : Fin visitBudget),
            visit.1 < adaptiveTapeVisitCount previous coordinate →
              tape coordinate visit = tape' coordinate visit := by
        intro coordinate visit hvisit
        apply hagree coordinate visit
        exact lt_of_lt_of_le hvisit (hcount_le coordinate)
      have hprevious_eq :
          previous = adaptiveTapeEvents tape' scheduler rounds hprevious := by
        exact adaptiveTapeEvents_eq_of_agree_on_consumed tape tape' scheduler rounds
          hprevious hagree_previous
      have hselected_lt :
          (⟨consumed, hconsumed⟩ : Fin visitBudget).1 <
            adaptiveTapeVisitCount
              (adaptiveTapeEvents tape scheduler (rounds + 1) hrounds) selected := by
        rw [hfull, adaptiveTapeVisitCount_append_singleton]
        simpa [consumed] using
          (Nat.lt_succ_self (adaptiveTapeVisitCount previous selected))
      have hdata : tape selected ⟨consumed, hconsumed⟩ =
          tape' selected ⟨consumed, hconsumed⟩ :=
        hagree selected ⟨consumed, hconsumed⟩ hselected_lt
      have hfull' :
          adaptiveTapeEvents tape' scheduler (rounds + 1) hrounds =
            previous ++ [(selected, tape' selected ⟨consumed, hconsumed⟩)] := by
        simpa [previous, selected, consumed, hprevious_eq] using
          (adaptiveTapeEvents_succ tape' scheduler rounds hrounds)
      rw [hfull, hfull']
      simp [hdata]

/-- A selector that is unchanged by resampling its own selected coordinate has
an invariant selection event at every fixed coordinate.  The reverse direction
uses a second update restoring the old coordinate value. -/
theorem selector_eq_iff_update_eq
    {ι α : Type*} [DecidableEq ι]
    (selector : (ι → α) → ι)
    (hcausal : ∀ (sample : ι → α) (replacement : α),
      selector (Function.update sample (selector sample) replacement) = selector sample)
    (sample : ι → α) (coordinate : ι) (replacement : α) :
    selector (Function.update sample coordinate replacement) = coordinate ↔
      selector sample = coordinate := by
  constructor
  · intro hselected
    have hrestore := hcausal (Function.update sample coordinate replacement)
      (sample coordinate)
    rw [hselected] at hrestore
    have hupdate : Function.update
        (Function.update sample coordinate replacement) coordinate (sample coordinate) =
          sample := by
      funext index
      by_cases hindex : index = coordinate <;> simp [Function.update, hindex]
    simpa [hupdate] using hrestore
  · intro hselected
    simpa [hselected] using hcausal sample replacement

/-- Partitioning a finite sum by the unique value of a selector recovers the
selected branch. -/
theorem sum_ite_selector_eq
    {ι β γ : Type*} [Fintype ι] [DecidableEq ι]
    (selector : β → ι) (sample : β) (branch : ι → γ) [AddCommMonoid γ] :
    (∑ coordinate : ι,
      if selector sample = coordinate then branch coordinate else 0) =
      branch (selector sample) := by
  classical
  rw [Finset.sum_eq_single (selector sample)]
  · simp
  · intro coordinate _ hne
    simp [Ne.symm hne]
  · simp

/-- A causally selected coordinate of a finite heterogeneous product is fresh
from its own coordinate law.  The proof partitions by the selected coordinate,
uses fixed-coordinate resampling on each branch, and recombines the branches. -/
theorem pmfExp_pmfPi_adaptive_update_eq
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : ι → PMF α) (selector : (ι → α) → ι)
    (hcausal : ∀ (sample : ι → α) (replacement : α),
      selector (Function.update sample (selector sample) replacement) = selector sample)
    (statistic : (ι → α) → ℝ) :
    pmfExp (pmfPi μ) statistic =
      pmfExp (pmfPi μ) (fun sample =>
        pmfExp (μ (selector sample)) (fun replacement =>
          statistic (Function.update sample (selector sample) replacement))) := by
  classical
  let branch : ι → (ι → α) → ℝ := fun coordinate sample =>
    if selector sample = coordinate then statistic sample else 0
  have hdecompose (sample : ι → α) :
      (∑ coordinate : ι, branch coordinate sample) = statistic sample := by
    exact sum_ite_selector_eq selector sample (fun _ => statistic sample)
  have hbranch (coordinate : ι) :
      pmfExp (pmfPi μ) (branch coordinate) =
        pmfExp (pmfPi μ) (fun sample =>
          pmfExp (μ coordinate) (fun replacement =>
            if selector sample = coordinate then
              statistic (Function.update sample coordinate replacement)
            else 0)) := by
    rw [← pmfExp_pmfPi_resample_eq μ (branch coordinate) coordinate]
    apply pmfExp_congr
    intro sample
    apply pmfExp_congr
    intro replacement
    unfold branch
    by_cases hselected : selector sample = coordinate
    · have hselected' : selector (Function.update sample coordinate replacement) = coordinate :=
        (selector_eq_iff_update_eq selector hcausal sample coordinate replacement).2 hselected
      simp [hselected, hselected']
    · have hselected' : selector (Function.update sample coordinate replacement) ≠ coordinate :=
        fun h => hselected
          ((selector_eq_iff_update_eq selector hcausal sample coordinate replacement).1 h)
      simp [hselected, hselected']
  calc
    pmfExp (pmfPi μ) statistic =
        pmfExp (pmfPi μ) (fun sample => ∑ coordinate : ι, branch coordinate sample) := by
          apply pmfExp_congr
          intro sample
          exact (hdecompose sample).symm
    _ = ∑ coordinate : ι, pmfExp (pmfPi μ) (branch coordinate) :=
          pmfExp_univ_sum (pmfPi μ) branch
    _ = ∑ coordinate : ι, pmfExp (pmfPi μ) (fun sample =>
          pmfExp (μ coordinate) (fun replacement =>
            if selector sample = coordinate then
              statistic (Function.update sample coordinate replacement)
            else 0)) := by
          apply Finset.sum_congr rfl
          intro coordinate _
          exact hbranch coordinate
    _ = pmfExp (pmfPi μ) (fun sample =>
          ∑ coordinate : ι,
            pmfExp (μ coordinate) (fun replacement =>
              if selector sample = coordinate then
                statistic (Function.update sample coordinate replacement)
              else 0)) := by
          symm
          exact pmfExp_univ_sum (pmfPi μ) _
    _ = pmfExp (pmfPi μ) (fun sample =>
          pmfExp (μ (selector sample)) (fun replacement =>
            statistic (Function.update sample (selector sample) replacement))) := by
          apply pmfExp_congr
          intro sample
          calc
            ∑ coordinate : ι,
                pmfExp (μ coordinate) (fun replacement =>
                  if selector sample = coordinate then
                    statistic (Function.update sample coordinate replacement)
                  else 0) =
                ∑ coordinate : ι,
                  if selector sample = coordinate then
                    pmfExp (μ coordinate) (fun replacement =>
                      statistic (Function.update sample coordinate replacement))
                  else 0 := by
                    apply Finset.sum_congr rfl
                    intro coordinate _
                    by_cases hselected : selector sample = coordinate
                    · simp [hselected]
                    · simp [hselected, pmfExp_const]
            _ = pmfExp (μ (selector sample)) (fun replacement =>
                statistic (Function.update sample (selector sample) replacement)) := by
                  exact sum_ite_selector_eq selector sample
                    (fun coordinate => pmfExp (μ coordinate) (fun replacement =>
                      statistic (Function.update sample coordinate replacement)))

end AppliedModelingLib
