import AL16SupplyDemandMatching.ContinuumLattice
import Mathlib.Algebra.BigOperators.Option
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Supply-and-Demand Lemma Core for Azevedo--Leshno

This module formalizes the no-blocking part of the cutoff-to-stable direction
of Azevedo and Leshno's Lemma 1.  It keeps the source's individual-demand
semantics explicit: a student can demand a college only if affordable, and a
strictly preferred college that the student does not demand is unaffordable.

The remaining measurable-matching and right-continuity clauses of Definition 1
are intentionally not packaged into a stability conclusion here.  The checked
theorem proves the substantive blocking-pair argument at
`docs/source_microsoft_2013.txt:2006-2014` from Definition 2.
-/

namespace AL16SupplyDemandMatching

open scoped Topology
open AppliedModelingLib.Matching
open Filter
open MeasureTheory Set

universe u v

variable {Student : Type u} {College : Type v} [Fintype College]

/-- Real score coordinate of a source student. -/
def al16ScoreValue
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (theta : Student) (c : College) : ℝ :=
  score theta c

/-- A student-college pair blocks the matching induced by a cutoff demand rule. -/
def al16DemandInducedBlocks
    (demand : AL16Cutoff College -> College -> ℝ)
    (capacity : College -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (P : AL16Cutoff College) (theta : Student) (c : College) : Prop :=
  prefers theta (some c) (choice P theta) ∧
    (demand P c < capacity c ∨
      ∃ theta' : Student,
        choice P theta' = some c ∧
          al16ScoreValue score theta' c < al16ScoreValue score theta c)

/-- No student-college pair blocks a demand-induced matching. -/
def al16DemandInducedNoBlocking
    (demand : AL16Cutoff College -> College -> ℝ)
    (capacity : College -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (P : AL16Cutoff College) : Prop :=
  ∀ theta : Student, ∀ c : College,
    ¬ al16DemandInducedBlocks demand capacity score prefers choice P theta c

/--
The favorite-affordable consequences of the source demand rule (2.1).

`none` represents the unmatched outside option.  Since the source makes every
college acceptable, it is chosen exactly when no college is affordable.
-/
def al16DemandChoiceSemantics
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College) : Prop :=
  ∀ P theta,
    match choice P theta with
    | none =>
        ∀ c : College,
          al16ScoreValue score theta c < al16CutoffValue P c
    | some c =>
        al16CutoffValue P c ≤ al16ScoreValue score theta c ∧
          ∀ d : College,
            al16CutoffValue P d ≤ al16ScoreValue score theta d ->
              ¬ prefers theta (some d) (some c)

/-- A college is affordable exactly when the student's score meets its cutoff. -/
def al16Affordable
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (P : AL16Cutoff College) (theta : Student) (c : College) : Prop :=
  al16CutoffValue P c ≤ al16ScoreValue score theta c

/--
Strict preference induced by a source student's numerical college ranking.

Every college is preferred to the unmatched outside option, as in the source's
all-colleges-acceptable normalization.
-/
def al16RankPrefers
    (rank : Student -> College -> Nat) (theta : Student) :
    Option College -> Option College -> Prop
  | some c, some d => rank theta c < rank theta d
  | some _, none => True
  | none, _ => False

private theorem al16ExistsAffordableRank
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (P : AL16Cutoff College) (theta : Student)
    (h : ∃ c : College, al16Affordable score P theta c) :
    ∃ n : Nat, ∃ c : College,
      al16Affordable score P theta c ∧ rank theta c = n := by
  rcases h with ⟨c, hc⟩
  exact ⟨rank theta c, c, hc, rfl⟩

noncomputable def al16FavoriteAffordableCollege
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (P : AL16Cutoff College) (theta : Student)
    (h : ∃ c : College, al16Affordable score P theta c) : College := by
  classical
  exact Classical.choose
    (Nat.find_spec (al16ExistsAffordableRank score rank P theta h))

private theorem al16FavoriteAffordableCollege_affordable
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (P : AL16Cutoff College) (theta : Student)
    (h : ∃ c : College, al16Affordable score P theta c) :
    al16Affordable score P theta
      (al16FavoriteAffordableCollege score rank P theta h) := by
  classical
  exact (Classical.choose_spec
    (Nat.find_spec (al16ExistsAffordableRank score rank P theta h))).1

private theorem al16FavoriteAffordableCollege_rank_le
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (P : AL16Cutoff College) (theta : Student)
    (h : ∃ c : College, al16Affordable score P theta c)
    (d : College) (hd : al16Affordable score P theta d) :
    rank theta (al16FavoriteAffordableCollege score rank P theta h) ≤ rank theta d := by
  classical
  let hExists := al16ExistsAffordableRank score rank P theta h
  have hmin : Nat.find hExists ≤ rank theta d :=
    Nat.find_min' hExists ⟨d, hd, rfl⟩
  have hchosen :
      rank theta (al16FavoriteAffordableCollege score rank P theta h) = Nat.find hExists :=
    (Classical.choose_spec (Nat.find_spec hExists)).2
  exact hchosen.symm ▸ hmin

/-- The source's favorite-affordable demand choice constructed from student ranks. -/
noncomputable def al16FavoriteAffordableChoice
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (P : AL16Cutoff College) (theta : Student) : Option College := by
  classical
  by_cases h : ∃ c : College, al16Affordable score P theta c
  · exact some (al16FavoriteAffordableCollege score rank P theta h)
  · exact none

private theorem al16FavoriteAffordableChoice_none
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (P : AL16Cutoff College) (theta : Student)
    (h : ¬ ∃ c : College, al16Affordable score P theta c) :
    al16FavoriteAffordableChoice score rank P theta = none := by
  simp [al16FavoriteAffordableChoice, h]

private theorem al16FavoriteAffordableChoice_some
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (P : AL16Cutoff College) (theta : Student)
    (h : ∃ c : College, al16Affordable score P theta c) :
    al16FavoriteAffordableChoice score rank P theta =
      some (al16FavoriteAffordableCollege score rank P theta h) := by
  simp [al16FavoriteAffordableChoice, h]

private theorem al16FavoriteAffordableChoice_some_iff
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (P : AL16Cutoff College) (theta : Student) (c : College)
    (hrank_injective : Function.Injective (rank theta)) :
    al16FavoriteAffordableChoice score rank P theta = some c ↔
      al16Affordable score P theta c ∧
        ∀ d : College,
          al16Affordable score P theta d -> ¬ rank theta d < rank theta c := by
  constructor
  · intro hchoice
    by_cases h : ∃ d : College, al16Affordable score P theta d
    · have hselected := al16FavoriteAffordableChoice_some score rank P theta h
      have hselected_eq :
          al16FavoriteAffordableCollege score rank P theta h = c :=
        Option.some.inj (hselected.symm.trans hchoice)
      refine ⟨?_, ?_⟩
      · simpa [hselected_eq] using
          (al16FavoriteAffordableCollege_affordable score rank P theta h)
      · intro d hd hlt
        have hle :=
          al16FavoriteAffordableCollege_rank_le score rank P theta h d hd
        have hle' : rank theta c ≤ rank theta d := by
          simpa [hselected_eq] using hle
        exact (not_lt_of_ge hle') hlt
    · have hnone := al16FavoriteAffordableChoice_none score rank P theta h
      rw [hnone] at hchoice
      cases hchoice
  · rintro ⟨hc, hminimal⟩
    have h : ∃ d : College, al16Affordable score P theta d := ⟨c, hc⟩
    rw [al16FavoriteAffordableChoice_some score rank P theta h]
    have hselected_affordable :=
      al16FavoriteAffordableCollege_affordable score rank P theta h
    have hle :=
      al16FavoriteAffordableCollege_rank_le score rank P theta h c hc
    have hge : rank theta c ≤
        rank theta (al16FavoriteAffordableCollege score rank P theta h) :=
      le_of_not_gt
        (hminimal (al16FavoriteAffordableCollege score rank P theta h)
          hselected_affordable)
    have hrank_eq :
        rank theta (al16FavoriteAffordableCollege score rank P theta h) =
          rank theta c :=
      le_antisymm hle hge
    have hcollege_eq :
        al16FavoriteAffordableCollege score rank P theta h = c :=
      hrank_injective hrank_eq
    simpa [hcollege_eq]

private theorem al16FavoriteAffordableChoice_none_iff
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (P : AL16Cutoff College) (theta : Student) :
    al16FavoriteAffordableChoice score rank P theta = none ↔
      ∀ c : College, ¬ al16Affordable score P theta c := by
  constructor
  · intro hnone c hc
    have h : ∃ d : College, al16Affordable score P theta d := ⟨c, hc⟩
    have hsome := al16FavoriteAffordableChoice_some score rank P theta h
    rw [hnone] at hsome
    cases hsome
  · intro hnone
    apply al16FavoriteAffordableChoice_none score rank P theta
    rintro ⟨c, hc⟩
    exact hnone c hc

/-- Affordability fibers are measurable from measurable score coordinates. -/
theorem al16Affordable_fiber_measurable
    [MeasurableSpace Student]
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (hscore_measurable :
      ∀ c : College, Measurable (fun theta => al16ScoreValue score theta c))
    (P : AL16Cutoff College) (c : College) :
    MeasurableSet {theta | al16Affordable score P theta c} := by
  simpa [al16Affordable] using
    (measurableSet_le measurable_const (hscore_measurable c))

/--
The favorite-affordable selector has measurable fibers when score coordinates
and finite ranking coordinates are measurable.  This discharges the fiber
measurability needed to define the source aggregate-demand masses.
-/
theorem al16FavoriteAffordableChoice_fiber_measurable
    [MeasurableSpace Student]
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (hscore_measurable :
      ∀ c : College, Measurable (fun theta => al16ScoreValue score theta c))
    (hrank_measurable : ∀ c : College, Measurable (fun theta => rank theta c))
    (hrank_injective : ∀ theta : Student, Function.Injective (rank theta))
    (P : AL16Cutoff College) (o : Option College) :
    MeasurableSet ((al16FavoriteAffordableChoice score rank P) ⁻¹' ({o} : Set (Option College))) := by
  have haffordable : ∀ c : College,
      MeasurableSet {theta | al16Affordable score P theta c} :=
    fun c => al16Affordable_fiber_measurable score hscore_measurable P c
  cases o with
  | none =>
      have hset :
          (al16FavoriteAffordableChoice score rank P) ⁻¹' ({none} : Set (Option College)) =
            ⋂ c : College, {theta | al16Affordable score P theta c}ᶜ := by
        ext theta
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter,
          Set.mem_compl_iff, Set.mem_setOf_eq]
        exact al16FavoriteAffordableChoice_none_iff score rank P theta
      rw [hset]
      exact MeasurableSet.iInter fun c => (haffordable c).compl
  | some c =>
      have hset :
          (al16FavoriteAffordableChoice score rank P) ⁻¹' ({some c} : Set (Option College)) =
            {theta | al16Affordable score P theta c} ∩
              ⋂ d : College,
                ({theta | al16Affordable score P theta d} ∩
                  {theta | rank theta d < rank theta c})ᶜ := by
        ext theta
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq]
        rw [al16FavoriteAffordableChoice_some_iff score rank P theta c
          (hrank_injective theta)]
        constructor
        · rintro ⟨hc, hminimal⟩
          refine ⟨hc, ?_⟩
          intro d hd
          exact hminimal d hd.1 hd.2
        · rintro ⟨hc, hminimal⟩
          refine ⟨hc, ?_⟩
          intro d hd hlt
          exact hminimal d ⟨hd, hlt⟩
      rw [hset]
      refine (haffordable c).inter (MeasurableSet.iInter fun d => ?_)
      exact ((haffordable d).inter
        (measurableSet_lt (hrank_measurable d) (hrank_measurable c))).compl

/--
Changing neither a student's rank ordering nor any affordability event leaves
the constructed favorite-affordable choice unchanged.
-/
theorem al16FavoriteAffordableChoice_eq_of_rank_and_affordability
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (P : AL16Cutoff College) (theta theta' : Student)
    (hrank : rank theta = rank theta')
    (hrank_injective : Function.Injective (rank theta))
    (haffordable :
      ∀ c : College,
        al16Affordable score P theta c ↔ al16Affordable score P theta' c) :
    al16FavoriteAffordableChoice score rank P theta =
      al16FavoriteAffordableChoice score rank P theta' := by
  cases hchoice : al16FavoriteAffordableChoice score rank P theta with
  | none =>
      have hnone : ∀ c : College, ¬ al16Affordable score P theta c :=
        (al16FavoriteAffordableChoice_none_iff score rank P theta).1 hchoice
      have hnone' : ∀ c : College, ¬ al16Affordable score P theta' c := by
        intro c hc
        exact hnone c ((haffordable c).2 hc)
      symm
      exact (al16FavoriteAffordableChoice_none_iff score rank P theta').2 hnone'
  | some c =>
      have hsome :=
        (al16FavoriteAffordableChoice_some_iff score rank P theta c hrank_injective).1
          hchoice
      have hrank_injective' : Function.Injective (rank theta') := by
        rw [← hrank]
        exact hrank_injective
      symm
      apply (al16FavoriteAffordableChoice_some_iff score rank P theta' c
        hrank_injective').2
      refine ⟨(haffordable c).1 hsome.1, ?_⟩
      intro d hd hlt
      have hlt' : rank theta d < rank theta c := by
        simpa [hrank] using hlt
      exact hsome.2 d ((haffordable d).2 hd) hlt'

/-- Holding a student's rank fixed, the favorite-affordable selector depends only on
which colleges are affordable. -/
theorem al16FavoriteAffordableChoice_eq_of_affordability
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (P Q : AL16Cutoff College) (theta : Student)
    (hrank_injective : Function.Injective (rank theta))
    (haffordable :
      ∀ c : College,
        al16Affordable score P theta c ↔ al16Affordable score Q theta c) :
    al16FavoriteAffordableChoice score rank P theta =
      al16FavoriteAffordableChoice score rank Q theta := by
  cases hchoice : al16FavoriteAffordableChoice score rank P theta with
  | none =>
      have hnone : ∀ c : College, ¬ al16Affordable score P theta c :=
        (al16FavoriteAffordableChoice_none_iff score rank P theta).1 hchoice
      have hnone' : ∀ c : College, ¬ al16Affordable score Q theta c := by
        intro c hc
        exact hnone c ((haffordable c).2 hc)
      exact ((al16FavoriteAffordableChoice_none_iff score rank Q theta).2 hnone').symm
  | some c =>
      have hsome :=
        (al16FavoriteAffordableChoice_some_iff score rank P theta c hrank_injective).1
          hchoice
      have hsome' : al16FavoriteAffordableChoice score rank Q theta = some c :=
        (al16FavoriteAffordableChoice_some_iff score rank Q theta c hrank_injective).2
          ⟨(haffordable c).1 hsome.1, fun d hd hlt =>
            hsome.2 d ((haffordable d).2 hd) hlt⟩
      exact hsome'.symm

/-- A known affordable college with no affordable better rank is the selector's choice. -/
theorem al16FavoriteAffordableChoice_eq_some_of_no_better
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (P : AL16Cutoff College) (theta : Student) (c : College)
    (hrank_injective : Function.Injective (rank theta))
    (haffordable : al16Affordable score P theta c)
    (hno_better :
      ∀ d : College,
        al16Affordable score P theta d -> ¬ rank theta d < rank theta c) :
    al16FavoriteAffordableChoice score rank P theta = some c :=
  (al16FavoriteAffordableChoice_some_iff score rank P theta c hrank_injective).2
    ⟨haffordable, hno_better⟩

/-- If no college is affordable, the selector chooses the unmatched option. -/
theorem al16FavoriteAffordableChoice_eq_none_of_no_affordable
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (P : AL16Cutoff College) (theta : Student)
    (hno_affordable : ∀ c : College, ¬ al16Affordable score P theta c) :
    al16FavoriteAffordableChoice score rank P theta = none :=
  (al16FavoriteAffordableChoice_none_iff score rank P theta).2 hno_affordable

/-- The constructed choice satisfies the source's literal favorite-affordable rule. -/
theorem al16FavoriteAffordableChoice_semantics
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat) :
    al16DemandChoiceSemantics score (al16RankPrefers rank)
      (al16FavoriteAffordableChoice score rank) := by
  intro P theta
  by_cases h : ∃ c : College, al16Affordable score P theta c
  · rw [al16FavoriteAffordableChoice_some score rank P theta h]
    refine ⟨al16FavoriteAffordableCollege_affordable score rank P theta h, ?_⟩
    intro d hd hpreferred
    have hrank :
        rank theta (al16FavoriteAffordableCollege score rank P theta h) ≤ rank theta d :=
      al16FavoriteAffordableCollege_rank_le score rank P theta h d hd
    exact (not_lt_of_ge hrank) (by simpa [al16RankPrefers] using hpreferred)
  · rw [al16FavoriteAffordableChoice_none score rank P theta h]
    intro c
    exact lt_of_not_ge (fun hc => h ⟨c, hc⟩)

/-- Rank-induced strict preference is irreflexive. -/
theorem al16RankPrefers_irrefl
    (rank : Student -> College -> Nat) :
    ∀ theta x, ¬ al16RankPrefers rank theta x x := by
  intro theta x
  cases x <;> simp [al16RankPrefers]

/-- An injective numerical rank gives a strict total order over colleges. -/
theorem al16RankPrefers_total
    (rank : Student -> College -> Nat)
    (hrank_injective : ∀ theta : Student, Function.Injective (rank theta)) :
    ∀ theta : Student, ∀ c d : College,
      c = d ∨ al16RankPrefers rank theta (some c) (some d) ∨
        al16RankPrefers rank theta (some d) (some c) := by
  intro theta c d
  rcases lt_trichotomy (rank theta c) (rank theta d) with hlt | heq | hgt
  · exact Or.inr (Or.inl hlt)
  · exact Or.inl (hrank_injective theta heq)
  · exact Or.inr (Or.inr hgt)

private theorem al16DemandChoice_affordable
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    {P : AL16Cutoff College} {theta : Student} {c : College}
    (hchosen : choice P theta = some c) :
    al16CutoffValue P c ≤ al16ScoreValue score theta c := by
  have hsemantics := hchoice P theta
  rw [hchosen] at hsemantics
  exact hsemantics.1

private theorem al16PreferredUnchosen_unaffordable
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    {P : AL16Cutoff College} {theta : Student} {c : College}
    (hunchosen : choice P theta ≠ some c)
    (hpreferred : prefers theta (some c) (choice P theta)) :
    al16ScoreValue score theta c < al16CutoffValue P c := by
  cases hchoice_theta : choice P theta with
  | none =>
      have hsemantics := hchoice P theta
      rw [hchoice_theta] at hsemantics
      exact hsemantics c
  | some d =>
      by_contra hnot
      have haffordable :
          al16CutoffValue P c ≤ al16ScoreValue score theta c :=
        le_of_not_gt hnot
      have hnot_preferred : ¬ prefers theta (some c) (some d) :=
        by
          have hsemantics := hchoice P theta
          rw [hchoice_theta] at hsemantics
          exact hsemantics.2 c haffordable
      apply hnot_preferred
      simpa [hchoice_theta] using hpreferred

/-- Students who demand a given college at a cutoff. -/
def al16DemandChoiceSet
    (choice : AL16Cutoff College -> Student -> Option College)
    (P : AL16Cutoff College) (c : College) : Set Student :=
  {theta | choice P theta = some c}

/-- Students who choose the unmatched outside option at a cutoff. -/
def al16OutsideChoiceSet
    (choice : AL16Cutoff College -> Student -> Option College)
    (P : AL16Cutoff College) : Set Student :=
  {theta | choice P theta = none}

/--
Sequential continuity of favorite-affordable aggregate demand at a cutoff whose
score-boundary sets have zero mass.  This is the reusable core of the AL16
Assumption 1 continuity argument, parameterized by the concrete score and rank
primitives instead of the source carrier.
-/
theorem al16FavoriteAffordableAggregateDemand_tendsto_of_coordinatewiseTendsto
    [MeasurableSpace Student]
    (mu : Measure Student) [IsProbabilityMeasure mu]
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (hscore_measurable :
      ∀ c : College, Measurable (fun theta => al16ScoreValue score theta c))
    (hrank_measurable : ∀ c : College, Measurable (fun theta => rank theta c))
    (hrank_injective : ∀ theta : Student, Function.Injective (rank theta))
    (P : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College)
    (hboundary_null :
      ∀ d : College,
        mu {theta | al16ScoreValue score theta d = al16CutoffValue Q d} = 0)
    (hPQ : al16CoordinatewiseTendsto P Q) (c : College) :
    Tendsto
      (fun n => mu.real
        (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank) (P n) c))
      atTop
      (𝓝 (mu.real
        (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank) Q c))) := by
  have hboundary :
      ∀ᵐ theta ∂mu, ∀ d : College,
        al16ScoreValue score theta d ≠ al16CutoffValue Q d := by
    apply ae_all_iff.mpr
    intro d
    apply ae_iff.mpr
    simpa only [not_not] using hboundary_null d
  have hchoice :
      ∀ᵐ theta ∂mu, ∀ᶠ n in atTop,
        al16FavoriteAffordableChoice score rank (P n) theta =
          al16FavoriteAffordableChoice score rank Q theta := by
    filter_upwards [hboundary] with theta htheta
    have haffordable : ∀ d : College, ∀ᶠ n in atTop,
        al16Affordable score (P n) theta d ↔
          al16Affordable score Q theta d := by
      intro d
      rcases lt_or_gt_of_ne (htheta d) with hscore_lt | hcutoff_lt
      · filter_upwards [(hPQ d).eventually_const_lt hscore_lt] with n hn
        simpa only [al16Affordable] using
          (iff_of_false (not_le_of_gt hn) (not_le_of_gt hscore_lt))
      · filter_upwards [(hPQ d).eventually_lt_const hcutoff_lt] with n hn
        simpa only [al16Affordable] using
          (iff_of_true (le_of_lt hn) (le_of_lt hcutoff_lt))
    have hall : ∀ᶠ n in atTop, ∀ d : College,
        al16Affordable score (P n) theta d ↔
          al16Affordable score Q theta d :=
      Filter.eventually_all.2 haffordable
    filter_upwards [hall] with n hn
    exact al16FavoriteAffordableChoice_eq_of_affordability score rank
      (P n) Q theta (hrank_injective theta) hn
  have hmembership :
      ∀ᵐ theta ∂mu, ∀ᶠ n in atTop,
        theta ∈ al16DemandChoiceSet (al16FavoriteAffordableChoice score rank)
            (P n) c ↔
          theta ∈ al16DemandChoiceSet (al16FavoriteAffordableChoice score rank)
            Q c := by
    filter_upwards [hchoice] with theta hchoice
    filter_upwards [hchoice] with n hn
    simp only [al16DemandChoiceSet, Set.mem_setOf_eq]
    rw [hn]
  have hmeasurableQ :
      MeasurableSet
        (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank) Q c) := by
    change MeasurableSet
      ((al16FavoriteAffordableChoice score rank Q) ⁻¹'
        ({some c} : Set (Option College)))
    exact al16FavoriteAffordableChoice_fiber_measurable
      score rank hscore_measurable hrank_measurable hrank_injective Q (some c)
  have hmeasurableP : ∀ n : ℕ,
      MeasurableSet
        (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank) (P n) c) := by
    intro n
    change MeasurableSet
      ((al16FavoriteAffordableChoice score rank (P n)) ⁻¹'
        ({some c} : Set (Option College)))
    exact al16FavoriteAffordableChoice_fiber_measurable
      score rank hscore_measurable hrank_measurable hrank_injective (P n) (some c)
  have hmeasure :
      Tendsto
        (fun n => mu
          (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank) (P n) c))
        atTop
        (𝓝 (mu
          (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank) Q c))) :=
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
      hmeasurableQ hmeasurableP hmembership
  have hreal :=
    (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure
  simpa only [Function.comp_apply, measureReal_def] using hreal

/--
At a coordinate where `Q` has the higher cutoff, a student demanding that
college at `Q` also demands it at `P sup Q`.
-/
theorem al16Choice_sup_eq_of_choice_eq
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (hprefers_total :
      ∀ theta : Student, ∀ c d : College,
        c = d ∨ prefers theta (some c) (some d) ∨
          prefers theta (some d) (some c))
    {P Q : AL16Cutoff College} {theta : Student} {c : College}
    (hPQ : al16CutoffValue P c ≤ al16CutoffValue Q c)
    (hQchoice : choice Q theta = some c) :
    choice (P ⊔ Q) theta = some c := by
  have hQsemantics := hchoice Q theta
  rw [hQchoice] at hQsemantics
  have hsup_affordable_c :
      al16CutoffValue (P ⊔ Q) c ≤ al16ScoreValue score theta c := by
    rw [show al16CutoffValue (P ⊔ Q) c = al16CutoffValue Q c by
      change max (↑(P c) : ℝ) (↑(Q c) : ℝ) = (↑(Q c) : ℝ)
      exact max_eq_right hPQ]
    exact hQsemantics.1
  cases hsup_choice : choice (P ⊔ Q) theta with
  | none =>
      have hsup_semantics := hchoice (P ⊔ Q) theta
      rw [hsup_choice] at hsup_semantics
      exact False.elim ((not_lt_of_ge hsup_affordable_c) (hsup_semantics c))
  | some d =>
      by_cases hcd : c = d
      · simpa [hcd] using hsup_choice
      · have hsup_semantics := hchoice (P ⊔ Q) theta
        rw [hsup_choice] at hsup_semantics
        rcases hprefers_total theta c d with hEq | hcd_preferred | hdc_preferred
        · exact False.elim (hcd hEq)
        · exact False.elim (hsup_semantics.2 c hsup_affordable_c hcd_preferred)
        · have hQ_le_sup :
              al16CutoffValue Q d ≤ al16CutoffValue (P ⊔ Q) d := by
            change (↑(Q d) : ℝ) ≤ max (↑(P d) : ℝ) (↑(Q d) : ℝ)
            exact le_max_right _ _
          have hQ_affordable_d :
              al16CutoffValue Q d ≤ al16ScoreValue score theta d :=
            hQ_le_sup.trans hsup_semantics.1
          exact False.elim (hQsemantics.2 d hQ_affordable_d hdc_preferred)

/--
At a coordinate where `P` has the lower cutoff, a student demanding that
college at `P inf Q` also demands it at `P`.
-/
theorem al16Choice_eq_of_choice_inf_eq
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (hprefers_total :
      ∀ theta : Student, ∀ c d : College,
        c = d ∨ prefers theta (some c) (some d) ∨
          prefers theta (some d) (some c))
    {P Q : AL16Cutoff College} {theta : Student} {c : College}
    (hPQ : al16CutoffValue P c ≤ al16CutoffValue Q c)
    (hinf_choice : choice (P ⊓ Q) theta = some c) :
    choice P theta = some c := by
  have hinf_semantics := hchoice (P ⊓ Q) theta
  rw [hinf_choice] at hinf_semantics
  have hP_affordable_c :
      al16CutoffValue P c ≤ al16ScoreValue score theta c := by
    rw [← show al16CutoffValue (P ⊓ Q) c = al16CutoffValue P c by
      change min (↑(P c) : ℝ) (↑(Q c) : ℝ) = (↑(P c) : ℝ)
      exact min_eq_left hPQ]
    exact hinf_semantics.1
  cases hP_choice : choice P theta with
  | none =>
      have hP_semantics := hchoice P theta
      rw [hP_choice] at hP_semantics
      exact False.elim ((not_lt_of_ge hP_affordable_c) (hP_semantics c))
  | some d =>
      by_cases hcd : c = d
      · simpa [hcd] using hP_choice
      · have hP_semantics := hchoice P theta
        rw [hP_choice] at hP_semantics
        rcases hprefers_total theta c d with hEq | hcd_preferred | hdc_preferred
        · exact False.elim (hcd hEq)
        · exact False.elim (hP_semantics.2 c hP_affordable_c hcd_preferred)
        · have hinf_le_P :
              al16CutoffValue (P ⊓ Q) d ≤ al16CutoffValue P d := by
            change min (↑(P d) : ℝ) (↑(Q d) : ℝ) ≤ (↑(P d) : ℝ)
            exact min_le_left _ _
          have hinf_affordable_d :
              al16CutoffValue (P ⊓ Q) d ≤ al16ScoreValue score theta d :=
            hinf_le_P.trans hP_semantics.1
          exact False.elim (hinf_semantics.2 d hinf_affordable_d hdc_preferred)

/-- Higher cutoffs cannot turn an unmatched student into a matched student. -/
theorem al16Choice_sup_eq_none_of_choice_eq_none
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    {P Q : AL16Cutoff College} {theta : Student}
    (hQchoice : choice Q theta = none) :
    choice (P ⊔ Q) theta = none := by
  have hQsemantics := hchoice Q theta
  rw [hQchoice] at hQsemantics
  cases hsup_choice : choice (P ⊔ Q) theta with
  | none => rfl
  | some c =>
      have hsup_semantics := hchoice (P ⊔ Q) theta
      rw [hsup_choice] at hsup_semantics
      have hQ_le_sup :
          al16CutoffValue Q c ≤ al16CutoffValue (P ⊔ Q) c := by
        change (↑(Q c) : ℝ) ≤ max (↑(P c) : ℝ) (↑(Q c) : ℝ)
        exact le_max_right _ _
      exact False.elim
        ((not_lt_of_ge (hQ_le_sup.trans hsup_semantics.1)) (hQsemantics c))

/-- Lower cutoffs cannot turn an unmatched student into a matched student. -/
theorem al16Choice_eq_none_of_choice_inf_eq_none
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    {P Q : AL16Cutoff College} {theta : Student}
    (hinf_choice : choice (P ⊓ Q) theta = none) :
    choice P theta = none := by
  have hinf_semantics := hchoice (P ⊓ Q) theta
  rw [hinf_choice] at hinf_semantics
  cases hP_choice : choice P theta with
  | none => rfl
  | some c =>
      have hP_semantics := hchoice P theta
      rw [hP_choice] at hP_semantics
      have hinf_le_P :
          al16CutoffValue (P ⊓ Q) c ≤ al16CutoffValue P c := by
        change min (↑(P c) : ℝ) (↑(Q c) : ℝ) ≤ (↑(P c) : ℝ)
        exact min_le_left _ _
      exact False.elim
        ((not_lt_of_ge (hinf_le_P.trans hP_semantics.1)) (hinf_semantics c))

/-- The pointwise demand-set inclusion used for the source's `sup` comparison. -/
theorem al16DemandChoiceSet_subset_sup
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (hprefers_total :
      ∀ theta : Student, ∀ c d : College,
        c = d ∨ prefers theta (some c) (some d) ∨
          prefers theta (some d) (some c))
    {P Q : AL16Cutoff College} {c : College}
    (hPQ : al16CutoffValue P c ≤ al16CutoffValue Q c) :
    al16DemandChoiceSet choice Q c ⊆ al16DemandChoiceSet choice (P ⊔ Q) c := by
  intro theta htheta
  exact al16Choice_sup_eq_of_choice_eq score prefers choice hchoice hprefers_total hPQ htheta

/-- The pointwise demand-set inclusion used for the source's `inf` comparison. -/
theorem al16DemandChoiceSet_inf_subset
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (hprefers_total :
      ∀ theta : Student, ∀ c d : College,
        c = d ∨ prefers theta (some c) (some d) ∨
          prefers theta (some d) (some c))
    {P Q : AL16Cutoff College} {c : College}
    (hPQ : al16CutoffValue P c ≤ al16CutoffValue Q c) :
    al16DemandChoiceSet choice (P ⊓ Q) c ⊆ al16DemandChoiceSet choice P c := by
  intro theta htheta
  exact al16Choice_eq_of_choice_inf_eq score prefers choice hchoice hprefers_total hPQ htheta

/-- The pointwise unmatched-set inclusion used for the source's `sup` comparison. -/
theorem al16OutsideChoiceSet_subset_sup
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (P Q : AL16Cutoff College) :
    al16OutsideChoiceSet choice Q ⊆ al16OutsideChoiceSet choice (P ⊔ Q) := by
  intro theta htheta
  exact al16Choice_sup_eq_none_of_choice_eq_none score prefers choice hchoice htheta

/-- The pointwise unmatched-set inclusion used for the source's `inf` comparison. -/
theorem al16OutsideChoiceSet_inf_subset
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (P Q : AL16Cutoff College) :
    al16OutsideChoiceSet choice (P ⊓ Q) ⊆ al16OutsideChoiceSet choice P := by
  intro theta htheta
  exact al16Choice_eq_none_of_choice_inf_eq_none score prefers choice hchoice htheta

/--
Lift the source's pointwise `sup` comparison to aggregate demand through an
explicit monotone mass functional.
-/
theorem al16AggregateDemand_le_sup_of_choice_semantics
    (demand : AL16Cutoff College -> College -> ℝ)
    (mass : Set Student -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hmass_mono : ∀ {A B : Set Student}, A ⊆ B -> mass A ≤ mass B)
    (hdemand : ∀ P c, demand P c = mass (al16DemandChoiceSet choice P c))
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (hprefers_total :
      ∀ theta : Student, ∀ c d : College,
        c = d ∨ prefers theta (some c) (some d) ∨
          prefers theta (some d) (some c))
    {P Q : AL16Cutoff College} {c : College}
    (hPQ : al16CutoffValue P c ≤ al16CutoffValue Q c) :
    demand Q c ≤ demand (P ⊔ Q) c := by
  rw [hdemand Q c, hdemand (P ⊔ Q) c]
  exact hmass_mono (al16DemandChoiceSet_subset_sup score prefers choice hchoice
    hprefers_total hPQ)

/-- Lift the source's pointwise `inf` comparison to aggregate demand. -/
theorem al16AggregateDemand_inf_le_of_choice_semantics
    (demand : AL16Cutoff College -> College -> ℝ)
    (mass : Set Student -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hmass_mono : ∀ {A B : Set Student}, A ⊆ B -> mass A ≤ mass B)
    (hdemand : ∀ P c, demand P c = mass (al16DemandChoiceSet choice P c))
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (hprefers_total :
      ∀ theta : Student, ∀ c d : College,
        c = d ∨ prefers theta (some c) (some d) ∨
          prefers theta (some d) (some c))
    {P Q : AL16Cutoff College} {c : College}
    (hPQ : al16CutoffValue P c ≤ al16CutoffValue Q c) :
    demand (P ⊓ Q) c ≤ demand P c := by
  rw [hdemand (P ⊓ Q) c, hdemand P c]
  exact hmass_mono (al16DemandChoiceSet_inf_subset score prefers choice hchoice
    hprefers_total hPQ)

/-- Lift the source's pointwise `sup` comparison to unmatched aggregate mass. -/
theorem al16Outside_le_sup_of_choice_semantics
    (outside : AL16Cutoff College -> ℝ)
    (mass : Set Student -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hmass_mono : ∀ {A B : Set Student}, A ⊆ B -> mass A ≤ mass B)
    (houtside : ∀ P, outside P = mass (al16OutsideChoiceSet choice P))
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (P Q : AL16Cutoff College) :
    outside Q ≤ outside (P ⊔ Q) := by
  rw [houtside Q, houtside (P ⊔ Q)]
  exact hmass_mono (al16OutsideChoiceSet_subset_sup score prefers choice hchoice P Q)

/-- Lift the source's pointwise `inf` comparison to unmatched aggregate mass. -/
theorem al16Outside_inf_le_of_choice_semantics
    (outside : AL16Cutoff College -> ℝ)
    (mass : Set Student -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hmass_mono : ∀ {A B : Set Student}, A ⊆ B -> mass A ≤ mass B)
    (houtside : ∀ P, outside P = mass (al16OutsideChoiceSet choice P))
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (P Q : AL16Cutoff College) :
    outside (P ⊓ Q) ≤ outside P := by
  rw [houtside (P ⊓ Q), houtside P]
  exact hmass_mono (al16OutsideChoiceSet_inf_subset score prefers choice hchoice P Q)

/-- Monotonicity of source aggregate mass when it is a probability measure. -/
theorem al16MeasureMass_mono
    [MeasurableSpace Student]
    (mu : Measure Student) [IsProbabilityMeasure mu]
    {A B : Set Student} (hAB : A ⊆ B) :
    mu.real A ≤ mu.real B :=
  measureReal_mono hAB

/--
The unit-mass identity in the A.1 proof from a probability measure and the
finite partition of students by their `Option College` demand outcome.
-/
theorem al16UnitMassPartition_of_measure_choice
    [MeasurableSpace Student]
    (mu : Measure Student) [IsProbabilityMeasure mu]
    (choice : AL16Cutoff College -> Student -> Option College)
    (hmeasurable :
      ∀ P : AL16Cutoff College, ∀ o : Option College,
        MeasurableSet ((choice P) ⁻¹' ({o} : Set (Option College))))
    (P : AL16Cutoff College) :
    mu.real (al16OutsideChoiceSet choice P) +
      ∑ c : College, mu.real (al16DemandChoiceSet choice P c) = 1 := by
  have hsum := sum_measureReal_preimage_singleton
    (μ := mu) (s := (Finset.univ : Finset (Option College))) (f := choice P)
    (fun o _ => hmeasurable P o)
  simpa [al16OutsideChoiceSet, al16DemandChoiceSet, Fintype.sum_option] using hsum

/--
The A.1 complete-lattice conclusion with its mass-conservation and monotonicity
premises derived from the source probability measure.
-/
theorem al16SourceMarketClearing_completeLattice_of_probability_measure_choice_primitives
    [MeasurableSpace Student]
    (mu : Measure Student) [IsProbabilityMeasure mu]
    (demand : AL16Cutoff College -> College -> ℝ)
    (outside : AL16Cutoff College -> ℝ)
    (capacity : College -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hdemand :
      ∀ P c, demand P c = mu.real (al16DemandChoiceSet choice P c))
    (houtside : ∀ P, outside P = mu.real (al16OutsideChoiceSet choice P))
    (hmeasurable :
      ∀ P : AL16Cutoff College, ∀ o : Option College,
        MeasurableSet ((choice P) ⁻¹' ({o} : Set (Option College))))
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (hprefers_total :
      ∀ theta : Student, ∀ c d : College,
        c = d ∨ prefers theta (some c) (some d) ∨
          prefers theta (some d) (some c))
    (hdemand_continuous :
      ∀ (P : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto P Q ->
          ∀ c : College,
            Tendsto (fun n => demand (P n) c) atTop (𝓝 (demand Q c)))
    (hnonempty : ∃ P : AL16Cutoff College,
      al16SourceMarketClearing demand capacity P) :
    CompleteLatticeOn (al16SourceMarketClearing demand capacity) al16CutoffLe :=
  al16SourceMarketClearing_completeLattice_of_continuum_primitives
    demand outside capacity hnonempty
    (fun P => by
      rw [houtside P]
      simp_rw [hdemand P]
      exact al16UnitMassPartition_of_measure_choice mu choice hmeasurable P)
    (fun P Q =>
      by
        simpa [sup_comm] using
          al16Outside_le_sup_of_choice_semantics outside mu.real score prefers choice
            (fun {A B} hAB => al16MeasureMass_mono mu hAB) houtside hchoice Q P)
    (fun P Q c hPQ =>
      al16AggregateDemand_le_sup_of_choice_semantics demand mu.real score prefers choice
        (fun {A B} hAB => al16MeasureMass_mono mu hAB) hdemand hchoice hprefers_total hPQ)
    (fun P Q =>
      al16Outside_inf_le_of_choice_semantics outside mu.real score prefers choice
        (fun {A B} hAB => al16MeasureMass_mono mu hAB) houtside hchoice P Q)
    (fun P Q c hPQ =>
      al16AggregateDemand_inf_le_of_choice_semantics demand mu.real score prefers choice
        (fun {A B} hAB => al16MeasureMass_mono mu hAB) hdemand hchoice hprefers_total hPQ)
    hdemand_continuous

/--
The probability-measure choice-primitive lattice theorem with sequential
closedness supplied directly instead of through global demand continuity.
-/
theorem al16SourceMarketClearing_completeLattice_of_probability_measure_choice_primitives_of_limit_closed
    [MeasurableSpace Student]
    (mu : Measure Student) [IsProbabilityMeasure mu]
    (demand : AL16Cutoff College -> College -> ℝ)
    (outside : AL16Cutoff College -> ℝ)
    (capacity : College -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hdemand :
      ∀ P c, demand P c = mu.real (al16DemandChoiceSet choice P c))
    (houtside : ∀ P, outside P = mu.real (al16OutsideChoiceSet choice P))
    (hmeasurable :
      ∀ P : AL16Cutoff College, ∀ o : Option College,
        MeasurableSet ((choice P) ⁻¹' ({o} : Set (Option College))))
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (hprefers_total :
      ∀ theta : Student, ∀ c d : College,
        c = d ∨ prefers theta (some c) (some d) ∨
          prefers theta (some d) (some c))
    (hclosed :
      ∀ (P : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College),
        (∀ n, al16SourceMarketClearing demand capacity (P n)) ->
          al16CoordinatewiseTendsto P Q ->
            al16SourceMarketClearing demand capacity Q)
    (hnonempty : ∃ P : AL16Cutoff College,
      al16SourceMarketClearing demand capacity P) :
    CompleteLatticeOn (al16SourceMarketClearing demand capacity) al16CutoffLe :=
  al16SourceMarketClearing_completeLattice_of_continuum_primitives_of_limit_closed
    demand outside capacity hnonempty
    (fun P => by
      rw [houtside P]
      simp_rw [hdemand P]
      exact al16UnitMassPartition_of_measure_choice mu choice hmeasurable P)
    (fun P Q =>
      by
        simpa [sup_comm] using
          al16Outside_le_sup_of_choice_semantics outside mu.real score prefers choice
            (fun {A B} hAB => al16MeasureMass_mono mu hAB) houtside hchoice Q P)
    (fun P Q c hPQ =>
      al16AggregateDemand_le_sup_of_choice_semantics demand mu.real score prefers choice
        (fun {A B} hAB => al16MeasureMass_mono mu hAB) hdemand hchoice hprefers_total hPQ)
    (fun P Q =>
      al16Outside_inf_le_of_choice_semantics outside mu.real score prefers choice
        (fun {A B} hAB => al16MeasureMass_mono mu hAB) houtside hchoice P Q)
    (fun P Q c hPQ =>
      al16AggregateDemand_inf_le_of_choice_semantics demand mu.real score prefers choice
        (fun {A B} hAB => al16MeasureMass_mono mu hAB) hdemand hchoice hprefers_total hPQ)
    hclosed

/--
Theorem A.1 from the source probability measure and literal choice semantics,
with nonempty clearing still made explicit.
-/
theorem al16TheoremA1_of_probability_measure_choice_primitives
    [MeasurableSpace Student]
    (mu : Measure Student) [IsProbabilityMeasure mu]
    (demand : AL16Cutoff College -> College -> ℝ)
    (outside : AL16Cutoff College -> ℝ)
    (capacity : College -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hdemand :
      ∀ P c, demand P c = mu.real (al16DemandChoiceSet choice P c))
    (houtside : ∀ P, outside P = mu.real (al16OutsideChoiceSet choice P))
    (hmeasurable :
      ∀ P : AL16Cutoff College, ∀ o : Option College,
        MeasurableSet ((choice P) ⁻¹' ({o} : Set (Option College))))
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (hprefers_total :
      ∀ theta : Student, ∀ c d : College,
        c = d ∨ prefers theta (some c) (some d) ∨
          prefers theta (some d) (some c))
    (hdemand_continuous :
      ∀ (P : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto P Q ->
          ∀ c : College,
            Tendsto (fun n => demand (P n) c) atTop (𝓝 (demand Q c)))
    (hnonempty : ∃ P : AL16Cutoff College, al16SourceMarketClearing demand capacity P) :
    (∃ P : AL16Cutoff College, al16SourceMarketClearing demand capacity P) ∧
      CompleteLatticeOn (al16SourceMarketClearing demand capacity) al16CutoffLe :=
  ⟨hnonempty,
    al16SourceMarketClearing_completeLattice_of_probability_measure_choice_primitives
      mu demand outside capacity score prefers choice hdemand houtside hmeasurable
      hchoice hprefers_total hdemand_continuous hnonempty⟩

/--
The A.1 complete-lattice conclusion with the four source comparison formulas
derived from literal choice and aggregate-mass semantics.

The remaining visible inputs are the unit-mass partition, demand continuity,
and the source cutoff domain already fixed by `AL16Cutoff`; none is a lattice
or market-clearing conclusion.
-/
theorem al16SourceMarketClearing_completeLattice_of_choice_primitives
    (demand : AL16Cutoff College -> College -> ℝ)
    (outside : AL16Cutoff College -> ℝ)
    (capacity : College -> ℝ)
    (mass : Set Student -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (hmass_mono : ∀ {A B : Set Student}, A ⊆ B -> mass A ≤ mass B)
    (hdemand : ∀ P c, demand P c = mass (al16DemandChoiceSet choice P c))
    (houtside : ∀ P, outside P = mass (al16OutsideChoiceSet choice P))
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (hprefers_total :
      ∀ theta : Student, ∀ c d : College,
        c = d ∨ prefers theta (some c) (some d) ∨
          prefers theta (some d) (some c))
    (hdemand_continuous :
      ∀ (P : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto P Q ->
          ∀ c : College,
            Tendsto (fun n => demand (P n) c) atTop (𝓝 (demand Q c)))
    (hnonempty : ∃ P : AL16Cutoff College,
      al16SourceMarketClearing demand capacity P) :
    CompleteLatticeOn (al16SourceMarketClearing demand capacity) al16CutoffLe :=
  al16SourceMarketClearing_completeLattice_of_continuum_primitives
    demand outside capacity hnonempty hmass
    (fun P Q =>
      by
        simpa [sup_comm] using
          al16Outside_le_sup_of_choice_semantics outside mass score prefers choice
            hmass_mono houtside hchoice Q P)
    (fun P Q c hPQ =>
      al16AggregateDemand_le_sup_of_choice_semantics demand mass score prefers choice
        hmass_mono hdemand hchoice hprefers_total hPQ)
    (fun P Q =>
      al16Outside_inf_le_of_choice_semantics outside mass score prefers choice
        hmass_mono houtside hchoice P Q)
    (fun P Q c hPQ =>
      al16AggregateDemand_inf_le_of_choice_semantics demand mass score prefers choice
        hmass_mono hdemand hchoice hprefers_total hPQ)
    hdemand_continuous

/--
Theorem A.1 from literal choice semantics, once the source's nonempty
market-clearing proof is supplied as a visible premise.
-/
theorem al16TheoremA1_of_choice_primitives
    (demand : AL16Cutoff College -> College -> ℝ)
    (outside : AL16Cutoff College -> ℝ)
    (capacity : College -> ℝ)
    (mass : Set Student -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hmass : ∀ P : AL16Cutoff College, outside P + ∑ c, demand P c = 1)
    (hmass_mono : ∀ {A B : Set Student}, A ⊆ B -> mass A ≤ mass B)
    (hdemand : ∀ P c, demand P c = mass (al16DemandChoiceSet choice P c))
    (houtside : ∀ P, outside P = mass (al16OutsideChoiceSet choice P))
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (hprefers_total :
      ∀ theta : Student, ∀ c d : College,
        c = d ∨ prefers theta (some c) (some d) ∨
          prefers theta (some d) (some c))
    (hdemand_continuous :
      ∀ (P : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto P Q ->
          ∀ c : College,
            Tendsto (fun n => demand (P n) c) atTop (𝓝 (demand Q c)))
    (hnonempty : ∃ P : AL16Cutoff College, al16SourceMarketClearing demand capacity P) :
    (∃ P : AL16Cutoff College, al16SourceMarketClearing demand capacity P) ∧
      CompleteLatticeOn (al16SourceMarketClearing demand capacity) al16CutoffLe :=
  ⟨hnonempty,
    al16SourceMarketClearing_completeLattice_of_choice_primitives
      demand outside capacity mass score prefers choice hmass hmass_mono hdemand
      houtside hchoice hprefers_total hdemand_continuous hnonempty⟩

/--
The no-blocking core of Lemma 1's cutoff-to-stable direction.

The two individual-choice premises are the direct logical content of equation
(2.1): a demanded college is affordable, and a strictly preferred unchosen
college is unaffordable.  Definition 2 then rules out an empty seat at that
college, while affordability of every admitted student rules out displacement
of a lower-scoring student.
-/
theorem al16DemandInducedNoBlocking_of_marketClearing
    (demand : AL16Cutoff College -> College -> ℝ)
    (capacity : College -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hprefers_irrefl : ∀ theta x, ¬ prefers theta x x)
    (hchoice_affordable :
      ∀ P theta c,
        choice P theta = some c ->
          al16CutoffValue P c ≤ al16ScoreValue score theta c)
    (hpreferred_unchosen_unaffordable :
      ∀ P theta c,
        choice P theta ≠ some c ->
          prefers theta (some c) (choice P theta) ->
            al16ScoreValue score theta c < al16CutoffValue P c)
    {P : AL16Cutoff College}
    (hP : al16SourceMarketClearing demand capacity P) :
    al16DemandInducedNoBlocking demand capacity score prefers choice P := by
  intro theta c hblocks
  rcases hblocks with ⟨hpreferred, hseat | ⟨theta', hchoice, hlowerScore⟩⟩
  · have hunchosen : choice P theta ≠ some c := by
      intro hchoice_theta
      apply hprefers_irrefl theta (some c)
      simpa [hchoice_theta] using hpreferred
    have hscore_lt_cutoff :
        al16ScoreValue score theta c < al16CutoffValue P c :=
      hpreferred_unchosen_unaffordable P theta c hunchosen hpreferred
    have hcutoff_positive : 0 < al16CutoffValue P c :=
      lt_of_le_of_lt (score theta c).property.1 hscore_lt_cutoff
    exact (ne_of_lt hseat) (hP.2 c hcutoff_positive)
  · have hunchosen : choice P theta ≠ some c := by
      intro hchoice_theta
      apply hprefers_irrefl theta (some c)
      simpa [hchoice_theta] using hpreferred
    have hscore_lt_cutoff :
        al16ScoreValue score theta c < al16CutoffValue P c :=
      hpreferred_unchosen_unaffordable P theta c hunchosen hpreferred
    have hcutoff_le_score :
        al16CutoffValue P c ≤ al16ScoreValue score theta' c :=
      hchoice_affordable P theta' c hchoice
    have hscore_lt :
        al16ScoreValue score theta c < al16ScoreValue score theta' c :=
      hscore_lt_cutoff.trans_le hcutoff_le_score
    exact (not_lt_of_ge hscore_lt.le) hlowerScore

/--
Lemma 1's no-blocking argument from the literal favorite-affordable demand
semantics, without accepting its two pointwise consequences as assumptions.
-/
theorem al16DemandInducedNoBlocking_of_favoriteAffordable_marketClearing
    (demand : AL16Cutoff College -> College -> ℝ)
    (capacity : College -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hprefers_irrefl : ∀ theta x, ¬ prefers theta x x)
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    {P : AL16Cutoff College}
    (hP : al16SourceMarketClearing demand capacity P) :
    al16DemandInducedNoBlocking demand capacity score prefers choice P :=
  al16DemandInducedNoBlocking_of_marketClearing demand capacity score prefers choice
    hprefers_irrefl
    (fun P theta c hchosen =>
      al16DemandChoice_affordable score prefers choice hchoice hchosen)
    (fun P theta c hunchosen hpreferred =>
      al16PreferredUnchosen_unaffordable score prefers choice hchoice hunchosen hpreferred)
    hP

/--
Lemma 1's no-blocking argument for the executable source choice constructed
from an injective student ranking.
-/
theorem al16DemandInducedNoBlocking_of_ranked_choice_marketClearing
    (demand : AL16Cutoff College -> College -> ℝ)
    (capacity : College -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    {P : AL16Cutoff College}
    (hP : al16SourceMarketClearing demand capacity P) :
    al16DemandInducedNoBlocking demand capacity score (al16RankPrefers rank)
      (al16FavoriteAffordableChoice score rank) P :=
  al16DemandInducedNoBlocking_of_favoriteAffordable_marketClearing
    demand capacity score (al16RankPrefers rank) (al16FavoriteAffordableChoice score rank)
    (al16RankPrefers_irrefl rank)
    (al16FavoriteAffordableChoice_semantics score rank)
    hP

/--
The A.1 complete-lattice conclusion with the source demand choice constructed
from a student's injective ranking of the finite college set.
-/
theorem al16SourceMarketClearing_completeLattice_of_probability_measure_ranked_choice_primitives
    [MeasurableSpace Student]
    (mu : Measure Student) [IsProbabilityMeasure mu]
    (demand : AL16Cutoff College -> College -> ℝ)
    (outside : AL16Cutoff College -> ℝ)
    (capacity : College -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (hdemand :
      ∀ P c,
        demand P c = mu.real
          (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank) P c))
    (houtside :
      ∀ P,
        outside P = mu.real
          (al16OutsideChoiceSet (al16FavoriteAffordableChoice score rank) P))
    (hscore_measurable :
      ∀ c : College, Measurable (fun theta => al16ScoreValue score theta c))
    (hrank_measurable : ∀ c : College, Measurable (fun theta => rank theta c))
    (hrank_injective : ∀ theta : Student, Function.Injective (rank theta))
    (hdemand_continuous :
      ∀ (P : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto P Q ->
          ∀ c : College,
            Tendsto (fun n => demand (P n) c) atTop (𝓝 (demand Q c)))
    (hnonempty : ∃ P : AL16Cutoff College,
      al16SourceMarketClearing demand capacity P) :
    CompleteLatticeOn (al16SourceMarketClearing demand capacity) al16CutoffLe :=
  al16SourceMarketClearing_completeLattice_of_probability_measure_choice_primitives
    mu demand outside capacity score (al16RankPrefers rank)
    (al16FavoriteAffordableChoice score rank) hdemand houtside
    (al16FavoriteAffordableChoice_fiber_measurable score rank hscore_measurable
      hrank_measurable hrank_injective)
    (al16FavoriteAffordableChoice_semantics score rank)
    (al16RankPrefers_total rank hrank_injective)
    hdemand_continuous hnonempty

/--
The ranked-choice probability-measure lattice theorem with sequential
closedness supplied directly.
-/
theorem al16SourceMarketClearing_completeLattice_of_probability_measure_ranked_choice_primitives_of_limit_closed
    [MeasurableSpace Student]
    (mu : Measure Student) [IsProbabilityMeasure mu]
    (demand : AL16Cutoff College -> College -> ℝ)
    (outside : AL16Cutoff College -> ℝ)
    (capacity : College -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (hdemand :
      ∀ P c,
        demand P c = mu.real
          (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank) P c))
    (houtside :
      ∀ P,
        outside P = mu.real
          (al16OutsideChoiceSet (al16FavoriteAffordableChoice score rank) P))
    (hscore_measurable :
      ∀ c : College, Measurable (fun theta => al16ScoreValue score theta c))
    (hrank_measurable : ∀ c : College, Measurable (fun theta => rank theta c))
    (hrank_injective : ∀ theta : Student, Function.Injective (rank theta))
    (hclosed :
      ∀ (P : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College),
        (∀ n, al16SourceMarketClearing demand capacity (P n)) ->
          al16CoordinatewiseTendsto P Q ->
            al16SourceMarketClearing demand capacity Q)
    (hnonempty : ∃ P : AL16Cutoff College,
      al16SourceMarketClearing demand capacity P) :
    CompleteLatticeOn (al16SourceMarketClearing demand capacity) al16CutoffLe :=
  al16SourceMarketClearing_completeLattice_of_probability_measure_choice_primitives_of_limit_closed
    mu demand outside capacity score (al16RankPrefers rank)
    (al16FavoriteAffordableChoice score rank) hdemand houtside
    (al16FavoriteAffordableChoice_fiber_measurable score rank hscore_measurable
      hrank_measurable hrank_injective)
    (al16FavoriteAffordableChoice_semantics score rank)
    (al16RankPrefers_total rank hrank_injective)
    hclosed hnonempty

/--
The equal-college-demand clause from the proof of Theorem A1, exposed for the
source rural-hospitals theorem.  The proof uses only the probability-mass
partition and the source `sup` comparison for favorite-affordable demand.
-/
theorem al16AggregateDemand_eq_of_probability_measure_choice_primitives
    [MeasurableSpace Student]
    (mu : Measure Student) [IsProbabilityMeasure mu]
    (demand : AL16Cutoff College -> College -> ℝ)
    (outside : AL16Cutoff College -> ℝ)
    (capacity : College -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hdemand :
      ∀ P c, demand P c = mu.real (al16DemandChoiceSet choice P c))
    (houtside : ∀ P, outside P = mu.real (al16OutsideChoiceSet choice P))
    (hmeasurable :
      ∀ P : AL16Cutoff College, ∀ o : Option College,
        MeasurableSet ((choice P) ⁻¹' ({o} : Set (Option College))))
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (hprefers_total :
      ∀ theta : Student, ∀ c d : College,
        c = d ∨ prefers theta (some c) (some d) ∨
          prefers theta (some d) (some c))
    {P Q : AL16Cutoff College}
    (hP : al16SourceMarketClearing demand capacity P)
    (hQ : al16SourceMarketClearing demand capacity Q) :
    ∀ c : College, demand P c = demand Q c :=
  al16SourceMarketClearing_aggregateDemand_eq_of_sup_primitives demand outside
    capacity
    (fun R => by
      rw [houtside R]
      simp_rw [hdemand R]
      exact al16UnitMassPartition_of_measure_choice mu choice hmeasurable R)
    (fun P Q =>
      by
        simpa [sup_comm] using
          al16Outside_le_sup_of_choice_semantics outside mu.real score prefers choice
            (fun {A B} hAB => al16MeasureMass_mono mu hAB) houtside hchoice Q P)
    (fun P Q c hPQ =>
      al16AggregateDemand_le_sup_of_choice_semantics demand mu.real score prefers choice
        (fun {A B} hAB => al16MeasureMass_mono mu hAB) hdemand hchoice hprefers_total hPQ)
    hP hQ

/--
The source probability-measure version of the equality between a clearing
cutoff's college demand and demand at the coordinatewise `sup` of two clearing
cutoffs.
-/
theorem al16AggregateDemand_eq_sup_of_probability_measure_choice_primitives
    [MeasurableSpace Student]
    (mu : Measure Student) [IsProbabilityMeasure mu]
    (demand : AL16Cutoff College -> College -> ℝ)
    (outside : AL16Cutoff College -> ℝ)
    (capacity : College -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (prefers : Student -> Option College -> Option College -> Prop)
    (choice : AL16Cutoff College -> Student -> Option College)
    (hdemand :
      ∀ P c, demand P c = mu.real (al16DemandChoiceSet choice P c))
    (houtside : ∀ P, outside P = mu.real (al16OutsideChoiceSet choice P))
    (hmeasurable :
      ∀ P : AL16Cutoff College, ∀ o : Option College,
        MeasurableSet ((choice P) ⁻¹' ({o} : Set (Option College))))
    (hchoice : al16DemandChoiceSemantics score prefers choice)
    (hprefers_total :
      ∀ theta : Student, ∀ c d : College,
        c = d ∨ prefers theta (some c) (some d) ∨
          prefers theta (some d) (some c))
    {P Q : AL16Cutoff College}
    (hP : al16SourceMarketClearing demand capacity P)
    (hQ : al16SourceMarketClearing demand capacity Q) :
    ∀ c : College, demand P c = demand (P ⊔ Q) c :=
  al16SourceMarketClearing_aggregateDemand_eq_sup_of_sup_primitives demand outside
    capacity
    (fun R => by
      rw [houtside R]
      simp_rw [hdemand R]
      exact al16UnitMassPartition_of_measure_choice mu choice hmeasurable R)
    (fun P Q =>
      by
        simpa [sup_comm] using
          al16Outside_le_sup_of_choice_semantics outside mu.real score prefers choice
            (fun {A B} hAB => al16MeasureMass_mono mu hAB) houtside hchoice Q P)
    (fun P Q c hPQ =>
      al16AggregateDemand_le_sup_of_choice_semantics demand mu.real score prefers choice
        (fun {A B} hAB => al16MeasureMass_mono mu hAB) hdemand hchoice hprefers_total hPQ)
    hP hQ

/--
Theorem A.1 from source probability, rank-based favorite-affordable demand,
and an explicit nonempty-clearing witness.
-/
theorem al16TheoremA1_of_probability_measure_ranked_choice_primitives
    [MeasurableSpace Student]
    (mu : Measure Student) [IsProbabilityMeasure mu]
    (demand : AL16Cutoff College -> College -> ℝ)
    (outside : AL16Cutoff College -> ℝ)
    (capacity : College -> ℝ)
    (score : Student -> College -> Set.Icc (0 : ℝ) 1)
    (rank : Student -> College -> Nat)
    (hdemand :
      ∀ P c,
        demand P c = mu.real
          (al16DemandChoiceSet (al16FavoriteAffordableChoice score rank) P c))
    (houtside :
      ∀ P,
        outside P = mu.real
          (al16OutsideChoiceSet (al16FavoriteAffordableChoice score rank) P))
    (hscore_measurable :
      ∀ c : College, Measurable (fun theta => al16ScoreValue score theta c))
    (hrank_measurable : ∀ c : College, Measurable (fun theta => rank theta c))
    (hrank_injective : ∀ theta : Student, Function.Injective (rank theta))
    (hdemand_continuous :
      ∀ (P : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto P Q ->
          ∀ c : College,
            Tendsto (fun n => demand (P n) c) atTop (𝓝 (demand Q c)))
    (hnonempty : ∃ P : AL16Cutoff College, al16SourceMarketClearing demand capacity P) :
    (∃ P : AL16Cutoff College, al16SourceMarketClearing demand capacity P) ∧
      CompleteLatticeOn (al16SourceMarketClearing demand capacity) al16CutoffLe :=
  ⟨hnonempty,
    al16SourceMarketClearing_completeLattice_of_probability_measure_ranked_choice_primitives
      mu demand outside capacity score rank hdemand houtside hscore_measurable
      hrank_measurable
      hrank_injective hdemand_continuous hnonempty⟩

end AL16SupplyDemandMatching
