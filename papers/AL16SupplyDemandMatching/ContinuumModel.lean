import AL16SupplyDemandMatching.ContinuumSupplyDemand
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Concrete Continuum Primitives for Azevedo--Leshno

This module fixes the source carrier of student types: a finite strict ranking
of colleges together with a score vector in `[0, 1]^C`.  It deliberately
contains only source primitives and facts derived from them.  In particular,
it does not package market-clearing existence, a lattice conclusion, or either
direction of the supply-and-demand lemma.

The source anchors are `docs/source_microsoft_2013.txt:428-435,472-474` for
the type and measure space, and `:524-546` for favorite-affordable demand and
aggregate demand.
-/

namespace AL16SupplyDemandMatching

open scoped Topology
open AppliedModelingLib.Matching
open Filter
open MeasureTheory Set

universe v

variable {College : Type v} [Fintype College]

/-- A strict ordering of the finite college set, represented by a permutation. -/
abbrev AL16Ranking (College : Type v) [Fintype College] :=
  College ≃ Fin (Fintype.card College)

/-- The source gives the finite ranking component its discrete sigma algebra. -/
instance : MeasurableSpace (AL16Ranking College) := ⊤

instance : DiscreteMeasurableSpace (AL16Ranking College) :=
  ⟨fun _ => trivial⟩

/-- The source ranking carrier is finite because it consists of finite-set permutations. -/
noncomputable instance : Fintype (AL16Ranking College) := Fintype.ofFinite _

/-- A source student is a strict ranking paired with one score in `[0, 1]` per college. -/
abbrev AL16SourceStudent (College : Type v) [Fintype College] :=
  AL16Ranking College × (College -> Set.Icc (0 : ℝ) 1)

/-- The score coordinate of a concrete source student. -/
def al16SourceScore (theta : AL16SourceStudent College) (c : College) :
    Set.Icc (0 : ℝ) 1 :=
  theta.2 c

/-- The numerical rank of a concrete source student's college ordering. -/
def al16SourceRank (theta : AL16SourceStudent College) (c : College) : Nat :=
  (theta.1 c).val

/-- The source's strict preference relation induced by the ranking component. -/
abbrev al16SourcePrefers :
    AL16SourceStudent College -> Option College -> Option College -> Prop :=
  al16RankPrefers al16SourceRank

/-- The source's favorite-affordable demand choice at a cutoff vector. -/
noncomputable def al16SourceChoice (P : AL16Cutoff College) :
    AL16SourceStudent College -> Option College :=
  al16FavoriteAffordableChoice al16SourceScore al16SourceRank P

/-- Source score coordinates are measurable for the product Borel sigma algebra. -/
theorem al16SourceScore_measurable (c : College) :
    Measurable (fun theta : AL16SourceStudent College =>
      al16ScoreValue al16SourceScore theta c) := by
  exact measurable_subtype_coe.comp ((measurable_pi_apply c).comp measurable_snd)

/-- Source rank coordinates are measurable because the ranking component is finite discrete. -/
theorem al16SourceRank_measurable (c : College) :
    Measurable (fun theta : AL16SourceStudent College => al16SourceRank theta c) := by
  exact (Measurable.of_discrete :
    Measurable (fun r : AL16Ranking College => (r c).val)).comp measurable_fst

/-- Each concrete source ranking is injective, hence a strict college ordering. -/
theorem al16SourceRank_injective :
    ∀ theta : AL16SourceStudent College,
      Function.Injective (al16SourceRank theta) := by
  intro theta c d h
  apply theta.1.injective
  exact Fin.ext h

/-- The favorite-affordable source demand has measurable finite-outcome fibers. -/
theorem al16SourceChoice_fiber_measurable
    (P : AL16Cutoff College) (o : Option College) :
    MeasurableSet ((al16SourceChoice P) ⁻¹' ({o} : Set (Option College))) := by
  simpa [al16SourceChoice] using
    (al16FavoriteAffordableChoice_fiber_measurable al16SourceScore al16SourceRank
      al16SourceScore_measurable al16SourceRank_measurable al16SourceRank_injective P o)

/-- The concrete source selector satisfies the displayed favorite-affordable rule (2.1). -/
theorem al16SourceChoice_semantics :
    al16DemandChoiceSemantics (College := College)
      al16SourceScore al16SourcePrefers al16SourceChoice := by
  simpa [al16SourceChoice] using
    (al16FavoriteAffordableChoice_semantics al16SourceScore al16SourceRank)

/-- Aggregate demand is the source probability mass of students choosing a college. -/
def al16SourceAggregateDemand
    (mu : Measure (AL16SourceStudent College))
    (P : AL16Cutoff College) (c : College) : ℝ :=
  mu.real (al16DemandChoiceSet al16SourceChoice P c)

/-- Outside-option demand is the source probability mass of unmatched students. -/
def al16SourceOutsideDemand
    (mu : Measure (AL16SourceStudent College))
    (P : AL16Cutoff College) : ℝ :=
  mu.real (al16OutsideChoiceSet al16SourceChoice P)

/-- The source's strict-preferences assumption: each college score level has zero mass. -/
def al16SourceStrictPreferences
    (mu : Measure (AL16SourceStudent College)) : Prop :=
  ∀ c : College, ∀ x : ℝ,
    mu {theta | al16ScoreValue al16SourceScore theta c = x} = 0

/--
A source ranking puts every college in `preferred` ahead of every college
outside `preferred`. This is the fixed preference order `≻+` used in Appendix
B's proof of Theorem 1 part (1).
-/
def al16RankingPrioritizes
    (rank : AL16Ranking College) (preferred : Finset College) : Prop :=
  ∀ c d : College, c ∈ preferred -> d ∉ preferred -> (rank c).val < (rank d).val

/--
The score slab used in Appendix B's full-support argument: a fixed ranking and
scores lying between two cutoff vectors on every coordinate in `preferred`.
-/
def al16SourceCutoffSlab
    (preferred : Finset College) (rank : AL16Ranking College)
    (lower upper : AL16Cutoff College) : Set (AL16SourceStudent College) :=
  {theta |
    theta.1 = rank ∧
      ∀ c : College, c ∈ preferred ->
        al16CutoffValue lower c ≤ al16ScoreValue al16SourceScore theta c ∧
          al16ScoreValue al16SourceScore theta c < al16CutoffValue upper c}

/--
The full-support consequence used by Appendix B of Azevedo--Leshno Theorem 1:
every nonempty positive-width cutoff slab has positive source mass for some
ranking that orders the slab coordinates above the others.
-/
def al16SourceFullSupportCutoffSlabs
    (mu : Measure (AL16SourceStudent College)) : Prop :=
  ∀ (preferred : Finset College) (lower upper : AL16Cutoff College),
    preferred.Nonempty ->
      (∀ c : College, c ∈ preferred ->
        al16CutoffValue lower c < al16CutoffValue upper c) ->
        ∃ rank : AL16Ranking College,
          al16RankingPrioritizes rank preferred ∧
            0 < mu.real (al16SourceCutoffSlab preferred rank lower upper)

/--
Under Assumption 1's zero-mass score levels, favorite-affordable aggregate
demand is sequentially continuous at every coordinatewise cutoff limit.  Away
from the finite union of cutoff score hyperplanes, every affordability event
is eventually constant; measurable choice fibers then give convergence of
their probability masses.
-/
theorem al16SourceAggregateDemand_tendsto_of_coordinatewiseTendsto
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (hstrict : al16SourceStrictPreferences mu)
    (P : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College)
    (hPQ : al16CoordinatewiseTendsto P Q) (c : College) :
    Tendsto (fun n => al16SourceAggregateDemand mu (P n) c)
      atTop (𝓝 (al16SourceAggregateDemand mu Q c)) := by
  have hboundary :
      ∀ᵐ theta ∂mu, ∀ d : College,
        al16ScoreValue al16SourceScore theta d ≠ al16CutoffValue Q d := by
    apply ae_all_iff.mpr
    intro d
    apply ae_iff.mpr
    simpa only [not_not] using hstrict d (al16CutoffValue Q d)
  have hchoice :
      ∀ᵐ theta ∂mu, ∀ᶠ n in atTop,
        al16SourceChoice (P n) theta = al16SourceChoice Q theta := by
    filter_upwards [hboundary] with theta htheta
    have haffordable : ∀ d : College, ∀ᶠ n in atTop,
        al16Affordable al16SourceScore (P n) theta d ↔
          al16Affordable al16SourceScore Q theta d := by
      intro d
      rcases lt_or_gt_of_ne (htheta d) with hscore_lt | hcutoff_lt
      · filter_upwards [(hPQ d).eventually_const_lt hscore_lt] with n hn
        simpa only [al16Affordable] using
          (iff_of_false (not_le_of_gt hn) (not_le_of_gt hscore_lt))
      · filter_upwards [(hPQ d).eventually_lt_const hcutoff_lt] with n hn
        simpa only [al16Affordable] using
          (iff_of_true (le_of_lt hn) (le_of_lt hcutoff_lt))
    have hall : ∀ᶠ n in atTop, ∀ d : College,
        al16Affordable al16SourceScore (P n) theta d ↔
          al16Affordable al16SourceScore Q theta d :=
      Filter.eventually_all.2 haffordable
    filter_upwards [hall] with n hn
    simpa only [al16SourceChoice] using
      (al16FavoriteAffordableChoice_eq_of_affordability
        al16SourceScore al16SourceRank (P n) Q theta
        (al16SourceRank_injective theta) hn)
  have hmembership :
      ∀ᵐ theta ∂mu, ∀ᶠ n in atTop,
        theta ∈ al16DemandChoiceSet al16SourceChoice (P n) c ↔
          theta ∈ al16DemandChoiceSet al16SourceChoice Q c := by
    filter_upwards [hchoice] with theta hchoice
    filter_upwards [hchoice] with n hn
    simp only [al16DemandChoiceSet, Set.mem_setOf_eq]
    rw [hn]
  have hmeasurableQ :
      MeasurableSet (al16DemandChoiceSet al16SourceChoice Q c) := by
    change MeasurableSet ((al16SourceChoice Q) ⁻¹' ({some c} : Set (Option College)))
    exact al16SourceChoice_fiber_measurable Q (some c)
  have hmeasurableP : ∀ n : ℕ,
      MeasurableSet (al16DemandChoiceSet al16SourceChoice (P n) c) := by
    intro n
    change MeasurableSet ((al16SourceChoice (P n)) ⁻¹' ({some c} : Set (Option College)))
    exact al16SourceChoice_fiber_measurable (P n) (some c)
  have hmeasure :
      Tendsto (fun n => mu (al16DemandChoiceSet al16SourceChoice (P n) c))
        atTop (𝓝 (mu (al16DemandChoiceSet al16SourceChoice Q c))) :=
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
      hmeasurableQ hmeasurableP hmembership
  have hreal :=
    (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure
  simpa only [Function.comp_apply, al16SourceAggregateDemand, measureReal_def] using hreal

/--
A source score path is coordinatewise decreasing to its limit, exactly as in
Definition 1's right-continuity clause (`source_microsoft_2013.txt:443-448`).
-/
def al16SourceScorePathConvergesDown
    (e : College -> Set.Icc (0 : ℝ) 1)
    (eSeq : ℕ -> College -> Set.Icc (0 : ℝ) 1) : Prop :=
  (∀ c : College,
    Tendsto (fun n => ((eSeq n c : Set.Icc (0 : ℝ) 1) : ℝ)) atTop
      (𝓝 ((e c : Set.Icc (0 : ℝ) 1) : ℝ))) ∧
  (∀ n : ℕ, ∀ c : College,
    ((eSeq (n + 1) c : Set.Icc (0 : ℝ) 1) : ℝ) ≤
      ((eSeq n c : Set.Icc (0 : ℝ) 1) : ℝ)) ∧
  ∀ n : ℕ, ∀ c : College,
    ((e c : Set.Icc (0 : ℝ) 1) : ℝ) ≤
      ((eSeq n c : Set.Icc (0 : ℝ) 1) : ℝ)

/-- Definition 1's right-continuity condition for a concrete source matching. -/
def al16SourceMatchingRightContinuous
    (matching : AL16SourceStudent College -> Option College) : Prop :=
  ∀ (r : AL16Ranking College)
    (e : College -> Set.Icc (0 : ℝ) 1)
    (eSeq : ℕ -> College -> Set.Icc (0 : ℝ) 1),
    al16SourceScorePathConvergesDown e eSeq ->
      ∃ K : ℕ, ∀ k ≥ K,
        matching ⟨r, eSeq k⟩ = matching ⟨r, e⟩

/-- The favorite-affordable matching satisfies Definition 1's right continuity. -/
theorem al16SourceChoice_rightContinuous (P : AL16Cutoff College) :
    al16SourceMatchingRightContinuous (al16SourceChoice P) := by
  intro r e eSeq hpath
  rcases hpath with ⟨hconv, _, hbelow⟩
  have heventually : ∀ c : College, ∀ᶠ n in atTop,
      al16Affordable al16SourceScore P ⟨r, eSeq n⟩ c ↔
        al16Affordable al16SourceScore P ⟨r, e⟩ c := by
    intro c
    by_cases haff : al16Affordable al16SourceScore P ⟨r, e⟩ c
    · refine Filter.Eventually.of_forall fun n => iff_of_true ?_ haff
      have haff' : ((P c : Set.Icc (0 : ℝ) 1) : ℝ) ≤
          ((e c : Set.Icc (0 : ℝ) 1) : ℝ) := by
        simpa [al16Affordable, al16CutoffValue, al16ScoreValue, al16SourceScore] using haff
      have hbelow' : ((e c : Set.Icc (0 : ℝ) 1) : ℝ) ≤
          ((eSeq n c : Set.Icc (0 : ℝ) 1) : ℝ) := hbelow n c
      simpa [al16Affordable, al16CutoffValue, al16ScoreValue, al16SourceScore] using
        haff'.trans hbelow'
    · have hlt : ((e c : Set.Icc (0 : ℝ) 1) : ℝ) <
          ((P c : Set.Icc (0 : ℝ) 1) : ℝ) := by
        simpa [al16Affordable, al16CutoffValue, al16ScoreValue, al16SourceScore] using
          lt_of_not_ge haff
      filter_upwards [(hconv c).eventually_lt_const hlt] with n hn
      apply iff_of_false _ haff
      intro haff'
      have haff'' : ((P c : Set.Icc (0 : ℝ) 1) : ℝ) ≤
          ((eSeq n c : Set.Icc (0 : ℝ) 1) : ℝ) := by
        simpa [al16Affordable, al16CutoffValue, al16ScoreValue, al16SourceScore] using haff'
      exact (not_lt_of_ge haff'') hn
  have hall : ∀ᶠ n in atTop, ∀ c : College,
      al16Affordable al16SourceScore P ⟨r, eSeq n⟩ c ↔
        al16Affordable al16SourceScore P ⟨r, e⟩ c :=
    Filter.eventually_all.2 heventually
  rcases hall.exists_forall_of_atTop with ⟨K, hK⟩
  refine ⟨K, fun k hk => ?_⟩
  exact al16FavoriteAffordableChoice_eq_of_rank_and_affordability
    al16SourceScore al16SourceRank P ⟨r, eSeq k⟩ ⟨r, e⟩ rfl
    (al16SourceRank_injective ⟨r, eSeq k⟩) (hK k hk)

/-!
The next auxiliary path raises one score coordinate by a vanishing amount.
It is the explicit sequence used to extract the strictly-better nearby type
from Definition 1 right continuity in the stable-to-cutoff proof.
-/

private noncomputable def al16SourceScoreLift
    (e : College -> Set.Icc (0 : ℝ) 1) (c : College)
    (n : ℕ) : College -> Set.Icc (0 : ℝ) 1 := by
  classical
  intro d
  by_cases hdc : d = c
  · subst d
    refine ⟨(e c : ℝ) + (1 - (e c : ℝ)) / ((n : ℝ) + 1), ?_, ?_⟩
    · have he : 0 ≤ (e c : ℝ) := (e c).property.1
      have hnum : 0 ≤ 1 - (e c : ℝ) := sub_nonneg.mpr (e c).property.2
      have hden : 0 < (n : ℝ) + 1 := by positivity
      exact add_nonneg he (div_nonneg hnum hden.le)
    · have hnonneg : 0 ≤ 1 - (e c : ℝ) := sub_nonneg.mpr (e c).property.2
      have hden : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
      have hdiv : (1 - (e c : ℝ)) / ((n : ℝ) + 1) ≤ 1 - (e c : ℝ) :=
        div_le_self hnonneg hden
      linarith
  · exact e d

private theorem al16SourceScoreLift_apply_self
    (e : College -> Set.Icc (0 : ℝ) 1) (c : College) (n : ℕ) :
    ((al16SourceScoreLift e c n c : Set.Icc (0 : ℝ) 1) : ℝ) =
      (e c : ℝ) + (1 - (e c : ℝ)) / ((n : ℝ) + 1) := by
  simp [al16SourceScoreLift]

private theorem al16SourceScoreLift_apply_ne
    (e : College -> Set.Icc (0 : ℝ) 1) (c d : College) (n : ℕ) (hdc : d ≠ c) :
    al16SourceScoreLift e c n d = e d := by
  simp [al16SourceScoreLift, hdc]

private theorem al16SourceScoreLift_tendsto
    (e : College -> Set.Icc (0 : ℝ) 1) (c d : College) :
    Tendsto (fun n => ((al16SourceScoreLift e c n d : Set.Icc (0 : ℝ) 1) : ℝ)) atTop
      (𝓝 ((e d : Set.Icc (0 : ℝ) 1) : ℝ)) := by
  by_cases hdc : d = c
  · subst d
    rw [show (fun n => ((al16SourceScoreLift e c n c : Set.Icc (0 : ℝ) 1) : ℝ)) =
      fun n : ℕ => (e c : ℝ) + (1 - (e c : ℝ)) / ((n : ℝ) + 1) by
        funext n
        exact al16SourceScoreLift_apply_self e c n]
    have hdiv : Tendsto
        (fun n : ℕ => (1 - (e c : ℝ)) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        ((tendsto_const_nhds (x := 1 - (e c : ℝ))).mul
          (tendsto_one_div_add_atTop_nhds_zero_nat :
            Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0)))
    simpa using (tendsto_const_nhds (x := (e c : ℝ))).add hdiv
  · rw [show (fun n => ((al16SourceScoreLift e c n d : Set.Icc (0 : ℝ) 1) : ℝ)) =
      fun _ : ℕ => (e d : ℝ) by
        funext n
        rw [al16SourceScoreLift_apply_ne e c d n hdc]]
    exact tendsto_const_nhds

private theorem al16SourceScoreLift_ge
    (e : College -> Set.Icc (0 : ℝ) 1) (c d : College) (n : ℕ) :
    ((e d : Set.Icc (0 : ℝ) 1) : ℝ) ≤
      ((al16SourceScoreLift e c n d : Set.Icc (0 : ℝ) 1) : ℝ) := by
  by_cases hdc : d = c
  · subst d
    rw [al16SourceScoreLift_apply_self]
    have hnum : 0 ≤ 1 - (e c : ℝ) := sub_nonneg.mpr (e c).property.2
    have hden : 0 < (n : ℝ) + 1 := by positivity
    exact le_add_of_nonneg_right (div_nonneg hnum hden.le)
  · rw [al16SourceScoreLift_apply_ne e c d n hdc]

private theorem al16SourceScoreLift_decreasing
    (e : College -> Set.Icc (0 : ℝ) 1) (c d : College) (n : ℕ) :
    ((al16SourceScoreLift e c (n + 1) d : Set.Icc (0 : ℝ) 1) : ℝ) ≤
      ((al16SourceScoreLift e c n d : Set.Icc (0 : ℝ) 1) : ℝ) := by
  by_cases hdc : d = c
  · subst d
    rw [al16SourceScoreLift_apply_self, al16SourceScoreLift_apply_self]
    have hnonneg : 0 ≤ 1 - (e c : ℝ) := sub_nonneg.mpr (e c).property.2
    have hdenpos : 0 < (n : ℝ) + 1 := by positivity
    have hden_le : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) + 1 := by
      push_cast
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    have hinv : 1 / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
      exact one_div_le_one_div_of_le hdenpos hden_le
    have hmul := mul_le_mul_of_nonneg_left hinv hnonneg
    simpa [div_eq_mul_inv] using add_le_add_left hmul (e c : ℝ)
  · rw [al16SourceScoreLift_apply_ne e c d (n + 1) hdc,
      al16SourceScoreLift_apply_ne e c d n hdc]

private theorem al16SourceScoreLift_strict_self
    (e : College -> Set.Icc (0 : ℝ) 1) (c : College) (n : ℕ)
    (h : (e c : ℝ) < 1) :
    ((e c : Set.Icc (0 : ℝ) 1) : ℝ) <
      ((al16SourceScoreLift e c n c : Set.Icc (0 : ℝ) 1) : ℝ) := by
  rw [al16SourceScoreLift_apply_self]
  have hnum : 0 < 1 - (e c : ℝ) := sub_pos.mpr h
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hdiv : 0 < (1 - (e c : ℝ)) / ((n : ℝ) + 1) := div_pos hnum hden
  linarith

/--
Right continuity supplies a nearby same-rank student with a strictly higher
score at any coordinate that is below one, while preserving the match.
-/
theorem al16SourceMatchingRightContinuous_exists_higher_score
    (matching : AL16SourceStudent College -> Option College)
    (hcontinuous : al16SourceMatchingRightContinuous matching)
    (r : AL16Ranking College)
    (e : College -> Set.Icc (0 : ℝ) 1)
    (o : Option College) {c : College}
    (hmatching : matching ⟨r, e⟩ = o)
    (hc_lt_one : (e c : ℝ) < 1) :
    ∃ theta' : AL16SourceStudent College,
      theta'.1 = r ∧ matching theta' = o ∧
        al16ScoreValue al16SourceScore ⟨r, e⟩ c <
          al16ScoreValue al16SourceScore theta' c := by
  have hpath : al16SourceScorePathConvergesDown e
      (fun n => al16SourceScoreLift e c n) :=
    ⟨fun d => al16SourceScoreLift_tendsto e c d,
      fun n d => al16SourceScoreLift_decreasing e c d n,
      fun n d => al16SourceScoreLift_ge e c d n⟩
  rcases hcontinuous r e (fun n => al16SourceScoreLift e c n) hpath with ⟨K, hK⟩
  refine ⟨⟨r, al16SourceScoreLift e c K⟩, rfl, ?_, ?_⟩
  · rw [hK K le_rfl]
    exact hmatching
  · simpa [al16ScoreValue, al16SourceScore] using
      al16SourceScoreLift_strict_self e c K hc_lt_one

/-- The students assigned to a college by an `Option College` source matching. -/
def al16SourceMatchingCollegeSet
    (matching : AL16SourceStudent College -> Option College)
    (c : College) : Set (AL16SourceStudent College) :=
  {theta | matching theta = some c}

/-- The students assigned to the outside option by an `Option College` source matching. -/
def al16SourceMatchingUnmatchedSet
    (matching : AL16SourceStudent College -> Option College) :
    Set (AL16SourceStudent College) :=
  {theta | matching theta = none}

/--
A blocking pair for a concrete source matching, using the source's capacity
and strictly-lower-score alternatives (`source_microsoft_2013.txt:488-495`).
-/
def al16SourceMatchingBlocks
    (mu : Measure (AL16SourceStudent College))
    (capacity : College -> ℝ)
    (matching : AL16SourceStudent College -> Option College)
    (theta : AL16SourceStudent College) (c : College) : Prop :=
  al16SourcePrefers theta (some c) (matching theta) ∧
    (mu.real (al16SourceMatchingCollegeSet matching c) < capacity c ∨
      ∃ theta' : AL16SourceStudent College,
        matching theta' = some c ∧
          al16ScoreValue al16SourceScore theta' c <
            al16ScoreValue al16SourceScore theta c)

/-- Source matching feasibility: measurable college fibers and capacity bounds. -/
def al16SourceMatchingFeasible
    (mu : Measure (AL16SourceStudent College))
    (capacity : College -> ℝ)
    (matching : AL16SourceStudent College -> Option College) : Prop :=
  (∀ c : College, MeasurableSet (al16SourceMatchingCollegeSet matching c)) ∧
    ∀ c : College, mu.real (al16SourceMatchingCollegeSet matching c) ≤ capacity c

/-- The source's college/student consistency clause, made explicit for fiber matching. -/
def al16SourceMatchingConsistent
    (matching : AL16SourceStudent College -> Option College) : Prop :=
  ∀ theta : AL16SourceStudent College, ∀ c : College,
    matching theta = some c ↔ theta ∈ al16SourceMatchingCollegeSet matching c

/-- Consistency follows definitionally from representing college matches as fibers. -/
theorem al16SourceMatching_consistent
    (matching : AL16SourceStudent College -> Option College) :
    al16SourceMatchingConsistent matching := by
  intro theta c
  rfl

/--
Definition 1 for the concrete source carrier.  Student assignments use
`Option College`, so its first clause is represented by the codomain; the
remaining matching and stability clauses are visible below.
-/
def al16SourceStableMatching
    (mu : Measure (AL16SourceStudent College))
    (capacity : College -> ℝ)
    (matching : AL16SourceStudent College -> Option College) : Prop :=
  al16SourceMatchingFeasible mu capacity matching ∧
    al16SourceMatchingConsistent matching ∧
      al16SourceMatchingRightContinuous matching ∧
        ∀ theta : AL16SourceStudent College, ∀ c : College,
          ¬ al16SourceMatchingBlocks mu capacity matching theta c

/--
Lemma 1's cutoff-to-stable direction for the literal source demand matching.
All Definition 1 clauses, including right continuity, are derived from the
concrete source construction and Definition 2 market clearing.
-/
theorem al16SourceChoice_stable_of_marketClearing
    (mu : Measure (AL16SourceStudent College))
    (capacity : College -> ℝ)
    {P : AL16Cutoff College}
    (hP : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P) :
    al16SourceStableMatching mu capacity (al16SourceChoice P) := by
  refine ⟨?_, al16SourceMatching_consistent (al16SourceChoice P),
    al16SourceChoice_rightContinuous P, ?_⟩
  · constructor
    · intro c
      change MeasurableSet ((al16SourceChoice P) ⁻¹' ({some c} : Set (Option College)))
      exact al16SourceChoice_fiber_measurable P (some c)
    · intro c
      change mu.real (al16DemandChoiceSet al16SourceChoice P c) ≤ capacity c
      exact hP.1 c
  · intro theta c hblocks
    have hnoBlocks :=
      al16DemandInducedNoBlocking_of_ranked_choice_marketClearing
        (al16SourceAggregateDemand mu) capacity al16SourceScore al16SourceRank hP
    apply hnoBlocks theta c
    simpa [al16DemandInducedBlocks, al16SourceMatchingBlocks,
      al16SourceAggregateDemand, al16SourceMatchingCollegeSet, al16SourceChoice,
      al16SourcePrefers, al16DemandChoiceSet] using hblocks

/-- A source ranking that places a specified college first. -/
noncomputable def al16SourceRankingWithTop (c : College) : AL16Ranking College :=
  let zero : Fin (Fintype.card College) :=
    ⟨0, Fintype.card_pos_iff.mpr ⟨c⟩⟩
  (Fintype.equivFin College).trans
    (Equiv.swap zero (Fintype.equivFin College c))

theorem al16SourceRankingWithTop_top (c : College) :
    (al16SourceRankingWithTop c c).val = 0 := by
  simp [al16SourceRankingWithTop]

/--
A score vector at which `c` is exactly at its cutoff and every other score is
zero.  Together with a ranking that puts `c` first, this is the source's
marginal-student witness in the proof that `P_{M_P} = P`.
-/
noncomputable def al16SourceScoreAtCutoff
    (P : AL16Cutoff College) (c : College) : College -> Set.Icc (0 : ℝ) 1 := by
  classical
  exact fun d => if d = c then P c else ⟨0, by norm_num⟩

/--
The source marginal-score cutoff (2.2), made total by assigning cutoff zero to
an empty college fiber.  On a nonempty fiber it is exactly the infimum of its
assigned score coordinates.  The zero branch is explicit rather than hidden;
the checked `P_{M_P}` inverse below uses nonempty fibers only.
-/
noncomputable def al16SourceMatchingCutoff
    (matching : AL16SourceStudent College -> Option College) : AL16Cutoff College := by
  classical
  exact fun c => if h : ∃ theta : AL16SourceStudent College, matching theta = some c then
    sInf ((fun theta => al16SourceScore theta c) ''
      al16SourceMatchingCollegeSet matching c)
  else ⟨0, by norm_num⟩

/-- Every student assigned to `c` has score at least the source marginal cutoff. -/
theorem al16SourceMatchingCutoff_le_score_of_assigned
    (matching : AL16SourceStudent College -> Option College)
    {theta : AL16SourceStudent College} {c : College}
    (hmatching : matching theta = some c) :
    al16CutoffValue (al16SourceMatchingCutoff matching) c ≤
      al16ScoreValue al16SourceScore theta c := by
  change al16SourceMatchingCutoff matching c ≤ al16SourceScore theta c
  rw [al16SourceMatchingCutoff, dif_pos ⟨theta, hmatching⟩]
  apply sInf_le
  exact ⟨theta, hmatching, rfl⟩

/-- The source's marginal student at `P_c` demands `c` when `c` is ranked first. -/
theorem al16SourceChoice_at_cutoff (P : AL16Cutoff College) (c : College) :
    al16SourceChoice P
      ⟨al16SourceRankingWithTop c, al16SourceScoreAtCutoff P c⟩ = some c := by
  simpa [al16SourceChoice] using
    (al16FavoriteAffordableChoice_eq_some_of_no_better
      al16SourceScore al16SourceRank P
      ⟨al16SourceRankingWithTop c, al16SourceScoreAtCutoff P c⟩ c
      (al16SourceRank_injective
        ⟨al16SourceRankingWithTop c, al16SourceScoreAtCutoff P c⟩)
      (by
        simp [al16Affordable, al16CutoffValue, al16ScoreValue,
          al16SourceScore, al16SourceScoreAtCutoff])
      (by
        intro d _
        rw [show al16SourceRank
            ⟨al16SourceRankingWithTop c, al16SourceScoreAtCutoff P c⟩ c = 0 by
          exact al16SourceRankingWithTop_top c]
        exact Nat.not_lt_zero _))

/--
The first inverse law in Lemma 1: taking the marginal-score cutoff of the
favorite-affordable matching recovers the original cutoff vector.
-/
theorem al16SourceMatchingCutoff_choice_eq (P : AL16Cutoff College) :
    al16SourceMatchingCutoff (al16SourceChoice P) = P := by
  funext c
  apply Subtype.ext
  change ((al16SourceMatchingCutoff (al16SourceChoice P) c : Set.Icc (0 : ℝ) 1) : ℝ) =
    ((P c : Set.Icc (0 : ℝ) 1) : ℝ)
  apply le_antisymm
  · let theta : AL16SourceStudent College :=
      ⟨al16SourceRankingWithTop c, al16SourceScoreAtCutoff P c⟩
    calc
      ((al16SourceMatchingCutoff (al16SourceChoice P) c : Set.Icc (0 : ℝ) 1) : ℝ) ≤
          ((al16SourceScore theta c : Set.Icc (0 : ℝ) 1) : ℝ) :=
        al16SourceMatchingCutoff_le_score_of_assigned (al16SourceChoice P)
          (al16SourceChoice_at_cutoff P c)
      _ = ((P c : Set.Icc (0 : ℝ) 1) : ℝ) := by
        simp [theta, al16SourceScore, al16SourceScoreAtCutoff]
  · have hwitness :
      ∃ theta : AL16SourceStudent College, al16SourceChoice P theta = some c :=
        ⟨⟨al16SourceRankingWithTop c, al16SourceScoreAtCutoff P c⟩,
          al16SourceChoice_at_cutoff P c⟩
    change (P c : Set.Icc (0 : ℝ) 1) ≤ al16SourceMatchingCutoff (al16SourceChoice P) c
    rw [al16SourceMatchingCutoff, dif_pos hwitness]
    apply le_sInf
    rintro score ⟨theta, hmatching, rfl⟩
    have hsemantics := al16SourceChoice_semantics P theta
    rw [hmatching] at hsemantics
    change ((P c : Set.Icc (0 : ℝ) 1) : ℝ) ≤
      ((al16SourceScore theta c : Set.Icc (0 : ℝ) 1) : ℝ)
    simpa [al16Affordable, al16CutoffValue, al16ScoreValue] using hsemantics.1

/--
For a stable matching, a student who prefers `c` cannot face either an
underfilled `c` or an assignee at a strictly lower `c` score.  This is the
blocking-pair contrapositive used in Lemma 1's stable-to-cutoff direction
(`source_microsoft_2013.txt:1984-2018`).
-/
theorem al16SourceStableMatching_preferred_not_underfilled_and_no_lower
    (mu : Measure (AL16SourceStudent College))
    (capacity : College -> ℝ)
    (matching : AL16SourceStudent College -> Option College)
    (hstable : al16SourceStableMatching mu capacity matching)
    {theta : AL16SourceStudent College} {c : College}
    (hprefers : al16SourcePrefers theta (some c) (matching theta)) :
    (¬ mu.real (al16SourceMatchingCollegeSet matching c) < capacity c) ∧
      (∀ theta' : AL16SourceStudent College,
        matching theta' = some c ->
          al16ScoreValue al16SourceScore theta c ≤
            al16ScoreValue al16SourceScore theta' c) := by
  constructor
  · intro hunder
    exact (hstable.2.2.2 theta c) ⟨hprefers, Or.inl hunder⟩
  · intro theta' hmatching
    by_contra hnot
    apply hstable.2.2.2 theta c
    refine ⟨hprefers, Or.inr ⟨theta', hmatching, ?_⟩⟩
    exact lt_of_not_ge hnot

/--
Under the source's positive-capacity and strict-score-law assumptions, every
college preferred to a stable assignment lies strictly above its marginal
assigned-score cutoff.  The score-one endpoint uses the zero mass of that
score level; below one, Definition 1 right continuity supplies the nearby
higher-score witness required by the infimum argument.
-/
theorem al16SourceStableMatching_preferred_score_lt_matchingCutoff
    (mu : Measure (AL16SourceStudent College))
    (capacity : College -> ℝ)
    (matching : AL16SourceStudent College -> Option College)
    (hstable : al16SourceStableMatching mu capacity matching)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hstrict : al16SourceStrictPreferences mu)
    {theta : AL16SourceStudent College} {c : College}
    (hprefers : al16SourcePrefers theta (some c) (matching theta)) :
    al16ScoreValue al16SourceScore theta c <
      al16CutoffValue (al16SourceMatchingCutoff matching) c := by
  rcases theta with ⟨r, e⟩
  have hfacts := al16SourceStableMatching_preferred_not_underfilled_and_no_lower
    mu capacity matching hstable hprefers
  rcases hfacts with ⟨hnotunder, hnoLower⟩
  have hnonempty : ∃ theta : AL16SourceStudent College, matching theta = some c := by
    by_contra hnone
    push Not at hnone
    have hempty : al16SourceMatchingCollegeSet matching c = ∅ := by
      ext theta
      simp [al16SourceMatchingCollegeSet, hnone theta]
    have hmass_zero : mu.real (al16SourceMatchingCollegeSet matching c) = 0 := by
      rw [hempty]
      simp
    apply hnotunder
    rw [hmass_zero]
    exact hcapacity_pos c
  by_cases hlt_one : (e c : ℝ) < 1
  · rcases al16SourceMatchingRightContinuous_exists_higher_score matching hstable.2.2.1
      r e (matching ⟨r, e⟩) (rfl) hlt_one with
      ⟨theta', hrank', hmatch', hscore_lt⟩
    rcases theta' with ⟨r', e'⟩
    change r' = r at hrank'
    subst r'
    have hprefers' : al16SourcePrefers ⟨r, e'⟩ (some c)
        (matching ⟨r, e'⟩) := by
      rw [hmatch']
      simpa [al16SourcePrefers, al16SourceRank] using hprefers
    have hnoLower' :=
      (al16SourceStableMatching_preferred_not_underfilled_and_no_lower
        mu capacity matching hstable hprefers').2
    have hscore_plus_le_cutoff :
        al16ScoreValue al16SourceScore ⟨r, e'⟩ c ≤
          al16CutoffValue (al16SourceMatchingCutoff matching) c := by
      change al16SourceScore ⟨r, e'⟩ c ≤
        al16SourceMatchingCutoff matching c
      rw [al16SourceMatchingCutoff, dif_pos hnonempty]
      apply le_sInf
      rintro score ⟨theta'', hmatch'', rfl⟩
      change matching theta'' = some c at hmatch''
      change ((al16SourceScore ⟨r, e'⟩ c : Set.Icc (0 : ℝ) 1) : ℝ) ≤
        ((al16SourceScore theta'' c : Set.Icc (0 : ℝ) 1) : ℝ)
      exact hnoLower' theta'' hmatch''
    exact hscore_lt.trans_le hscore_plus_le_cutoff
  · have hscore_eq_one : (e c : ℝ) = 1 :=
      le_antisymm (e c).property.2 (le_of_not_gt hlt_one)
    have hsubset : al16SourceMatchingCollegeSet matching c ⊆
        {theta | al16ScoreValue al16SourceScore theta c = 1} := by
      intro theta' hmatch'
      change matching theta' = some c at hmatch'
      have hge := hnoLower theta' hmatch'
      change (e c : ℝ) ≤ al16ScoreValue al16SourceScore theta' c at hge
      have hle : al16ScoreValue al16SourceScore theta' c ≤ 1 :=
        (al16SourceScore theta' c).property.2
      change al16ScoreValue al16SourceScore theta' c = 1
      linarith [hscore_eq_one]
    have hmass_zero : mu.real (al16SourceMatchingCollegeSet matching c) = 0 := by
      have hlevel := hstrict c 1
      have hlevel_ne_top :
          mu {theta | al16ScoreValue al16SourceScore theta c = 1} ≠ (⊤ : ENNReal) := by
        rw [hlevel]
        simp
      apply le_antisymm
      · calc
          mu.real (al16SourceMatchingCollegeSet matching c) ≤
              mu.real {theta | al16ScoreValue al16SourceScore theta c = 1} :=
            measureReal_mono hsubset hlevel_ne_top
          _ = 0 := by
            apply (measureReal_eq_zero_iff hlevel_ne_top).2
            exact hlevel
      · positivity
    exfalso
    apply hnotunder
    rw [hmass_zero]
    exact hcapacity_pos c

/--
The stable-to-cutoff inverse in Lemma 1: every source-stable matching is the
favorite-affordable matching at its marginal-score cutoff.  For an unmatched
student, every college is preferred and the stable preferred-college gap makes
all of them unaffordable.  For a matched student, the assigned college is
affordable and the same gap rules out every strictly preferred alternative.
-/
theorem al16SourceChoice_matchingCutoff_eq_of_stable
    (mu : Measure (AL16SourceStudent College))
    (capacity : College -> ℝ)
    (matching : AL16SourceStudent College -> Option College)
    (hstable : al16SourceStableMatching mu capacity matching)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hstrict : al16SourceStrictPreferences mu) :
    ∀ theta : AL16SourceStudent College,
      al16SourceChoice (al16SourceMatchingCutoff matching) theta = matching theta := by
  intro theta
  cases hmatching : matching theta with
  | none =>
      change al16FavoriteAffordableChoice al16SourceScore al16SourceRank
        (al16SourceMatchingCutoff matching) theta = none
      apply al16FavoriteAffordableChoice_eq_none_of_no_affordable
      intro c haffordable
      have hprefers : al16SourcePrefers theta (some c) (matching theta) := by
        rw [hmatching]
        trivial
      have hgap := al16SourceStableMatching_preferred_score_lt_matchingCutoff
        mu capacity matching hstable hcapacity_pos hstrict hprefers
      exact (not_le_of_gt hgap) haffordable
  | some a =>
      change al16FavoriteAffordableChoice al16SourceScore al16SourceRank
        (al16SourceMatchingCutoff matching) theta = some a
      apply al16FavoriteAffordableChoice_eq_some_of_no_better
      · exact al16SourceRank_injective theta
      · exact al16SourceMatchingCutoff_le_score_of_assigned matching hmatching
      · intro d haffordable hbetter
        have hprefers : al16SourcePrefers theta (some d) (matching theta) := by
          rw [hmatching]
          exact hbetter
        have hgap := al16SourceStableMatching_preferred_score_lt_matchingCutoff
          mu capacity matching hstable hcapacity_pos hstrict hprefers
        exact (not_le_of_gt hgap) haffordable

/--
The stable-to-cutoff clearing direction in Lemma 1.  The inverse just proved
identifies cutoff demand with the stable matching's college fibers, giving weak
capacity.  At a positive cutoff, an underfilled college would be blocked by the
zero-score student who ranks it first; assigning that student instead forces
the marginal cutoff to be zero.
-/
theorem al16SourceMatchingCutoff_marketClearing_of_stable
    (mu : Measure (AL16SourceStudent College))
    (capacity : College -> ℝ)
    (matching : AL16SourceStudent College -> Option College)
    (hstable : al16SourceStableMatching mu capacity matching)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hstrict : al16SourceStrictPreferences mu) :
    al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity
      (al16SourceMatchingCutoff matching) := by
  have hchoice := al16SourceChoice_matchingCutoff_eq_of_stable
    mu capacity matching hstable hcapacity_pos hstrict
  have hchoiceSet (c : College) :
      al16DemandChoiceSet al16SourceChoice (al16SourceMatchingCutoff matching) c =
        al16SourceMatchingCollegeSet matching c := by
    ext theta
    change al16SourceChoice (al16SourceMatchingCutoff matching) theta = some c ↔
      matching theta = some c
    rw [hchoice theta]
  constructor
  · intro c
    change mu.real
      (al16DemandChoiceSet al16SourceChoice (al16SourceMatchingCutoff matching) c) ≤
        capacity c
    rw [hchoiceSet c]
    exact hstable.1.2 c
  · intro c hpositive
    change mu.real
      (al16DemandChoiceSet al16SourceChoice (al16SourceMatchingCutoff matching) c) =
        capacity c
    rw [hchoiceSet c]
    refine le_antisymm (hstable.1.2 c) ?_
    apply le_of_not_gt
    intro hunder
    let zeroCutoff : AL16Cutoff College := fun _ => ⟨0, by norm_num⟩
    let theta0 : AL16SourceStudent College :=
      ⟨al16SourceRankingWithTop c, al16SourceScoreAtCutoff zeroCutoff c⟩
    have hmatchc : matching theta0 = some c := by
      by_contra hnot
      apply (hstable.2.2.2 theta0 c)
      refine ⟨?_, Or.inl hunder⟩
      cases hcurrent : matching theta0 with
      | none => trivial
      | some d =>
          change al16SourceRank theta0 c < al16SourceRank theta0 d
          have htop : al16SourceRank theta0 c = 0 := by
            change (al16SourceRankingWithTop c c).val = 0
            exact al16SourceRankingWithTop_top c
          have hdc : d ≠ c := by
            intro hdc
            subst d
            exact hnot hcurrent
          have hnonzero : al16SourceRank theta0 d ≠ 0 := by
            intro hdzero
            apply hdc
            apply al16SourceRank_injective theta0
            rw [htop, hdzero]
          simpa [htop] using Nat.pos_of_ne_zero hnonzero
    have hcutoff_le_zero :
        al16CutoffValue (al16SourceMatchingCutoff matching) c ≤ 0 := by
      calc
        al16CutoffValue (al16SourceMatchingCutoff matching) c ≤
            al16ScoreValue al16SourceScore theta0 c :=
          al16SourceMatchingCutoff_le_score_of_assigned matching hmatchc
        _ = 0 := by
          simp [theta0, zeroCutoff, al16SourceScore, al16SourceScoreAtCutoff,
            al16ScoreValue]
    exact (not_lt_of_ge hcutoff_le_zero) hpositive

/--
The equal-aggregate-demand step from the proof of Theorem A1, specialized to
the literal source carrier.  This is the first sentence of the proof of
Theorem A2: any two market-clearing cutoffs have the same college demand.
-/
theorem al16SourceAggregateDemand_eq_of_marketClearing
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    {P Q : AL16Cutoff College}
    (hP : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P)
    (hQ : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Q) :
    ∀ c : College,
      al16SourceAggregateDemand mu P c = al16SourceAggregateDemand mu Q c :=
  al16AggregateDemand_eq_of_probability_measure_choice_primitives
    mu (al16SourceAggregateDemand mu) (al16SourceOutsideDemand mu) capacity
    al16SourceScore al16SourcePrefers al16SourceChoice
    (fun _ _ => rfl) (fun _ => rfl) al16SourceChoice_fiber_measurable
    al16SourceChoice_semantics
    (al16RankPrefers_total al16SourceRank al16SourceRank_injective)
    hP hQ

/--
Concrete source exact-fill specialization. Definition 2 itself only gives
weak capacity and positive-cutoff equality; if the unmatched outside mass is
zero and total capacity is the unit source mass, finite summation forces every
college to be exactly filled.
-/
theorem al16SourceMarketClearing_exactFill_of_noOutside_totalCapacity
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    {P : AL16Cutoff College}
    (hP : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P)
    (houtside_zero : al16SourceOutsideDemand mu P = 0)
    (hcapacity_sum : (∑ c : College, capacity c) = 1) :
    ∀ c : College, al16SourceAggregateDemand mu P c = capacity c := by
  have hmass :
      al16SourceOutsideDemand mu P +
        ∑ c : College, al16SourceAggregateDemand mu P c = 1 := by
    simpa [al16SourceOutsideDemand, al16SourceAggregateDemand] using
      (al16UnitMassPartition_of_measure_choice
        mu al16SourceChoice al16SourceChoice_fiber_measurable P)
  exact al16MarketClearing_exactFill_of_noOutside_totalCapacity
    (al16SourceAggregateDemand mu) (al16SourceOutsideDemand mu) capacity
    hmass hP houtside_zero hcapacity_sum

/--
If any source cutoff coordinate is zero, every student has at least one
affordable college, so outside demand is zero.
-/
theorem al16SourceOutsideDemand_eq_zero_of_cutoff_eq_zero
    (mu : Measure (AL16SourceStudent College))
    {P : AL16Cutoff College} {c : College}
    (hzero : al16CutoffValue P c = 0) :
    al16SourceOutsideDemand mu P = 0 := by
  have hsubset :
      al16OutsideChoiceSet al16SourceChoice P ⊆
        (∅ : Set (AL16SourceStudent College)) := by
    intro theta htheta
    change al16SourceChoice P theta = none at htheta
    have hsemantics := al16SourceChoice_semantics P theta
    rw [htheta] at hsemantics
    have hscore_nonneg : 0 ≤ al16ScoreValue al16SourceScore theta c :=
      (al16SourceScore theta c).property.1
    exact False.elim ((not_lt_of_ge hscore_nonneg) (by simpa [hzero] using hsemantics c))
  have hmeasure_zero : mu (al16OutsideChoiceSet al16SourceChoice P) = 0 := by
    exact measure_mono_null hsubset (by simp)
  rw [al16SourceOutsideDemand, measureReal_def, hmeasure_zero]
  rfl

/--
If total capacity is strictly below the unit source mass, Definition 2 market
clearing must fill every college exactly. Otherwise an underfilled college has
zero cutoff, zero outside demand, and the unit-mass partition contradicts total
capacity below one. Source use: Proposition 7,
`docs/source_microsoft_2013.txt:1807-1812`.
-/
theorem al16SourceMarketClearing_exactFill_of_capacity_sum_lt_one
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    {P : AL16Cutoff College}
    (hP : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P)
    (hcapacity_sum_lt_one : (∑ c : College, capacity c) < 1) :
    ∀ c : College, al16SourceAggregateDemand mu P c = capacity c := by
  intro c
  by_cases hpos : 0 < al16CutoffValue P c
  · exact hP.2 c hpos
  · have hzero : al16CutoffValue P c = 0 :=
      le_antisymm (le_of_not_gt hpos) (P c).property.1
    have houtside_zero : al16SourceOutsideDemand mu P = 0 :=
      al16SourceOutsideDemand_eq_zero_of_cutoff_eq_zero mu hzero
    have hpartition :
        al16SourceOutsideDemand mu P +
            ∑ d : College, al16SourceAggregateDemand mu P d = 1 := by
      simpa [al16SourceOutsideDemand, al16SourceAggregateDemand] using
        (al16UnitMassPartition_of_measure_choice
          mu al16SourceChoice al16SourceChoice_fiber_measurable P)
    have hdemand_sum_eq_one :
        (∑ d : College, al16SourceAggregateDemand mu P d) = 1 := by
      nlinarith
    have hdemand_sum_le_capacity :
        (∑ d : College, al16SourceAggregateDemand mu P d) ≤
          ∑ d : College, capacity d := by
      exact Finset.sum_le_sum fun d _ => hP.1 d
    have hunit_le_capacity : (1 : ℝ) ≤ ∑ d : College, capacity d := by
      rw [← hdemand_sum_eq_one]
      exact hdemand_sum_le_capacity
    exact False.elim ((not_lt_of_ge hunit_le_capacity) hcapacity_sum_lt_one)

/-- Source-specific equality between a clearing cutoff and the `sup` of two clearing cutoffs. -/
theorem al16SourceAggregateDemand_eq_sup_of_marketClearing
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    {P Q : AL16Cutoff College}
    (hP : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P)
    (hQ : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Q) :
    ∀ c : College,
      al16SourceAggregateDemand mu P c =
        al16SourceAggregateDemand mu (P ⊔ Q) c :=
  al16AggregateDemand_eq_sup_of_probability_measure_choice_primitives
    mu (al16SourceAggregateDemand mu) (al16SourceOutsideDemand mu) capacity
    al16SourceScore al16SourcePrefers al16SourceChoice
    (fun _ _ => rfl) (fun _ => rfl) al16SourceChoice_fiber_measurable
    al16SourceChoice_semantics
    (al16RankPrefers_total al16SourceRank al16SourceRank_injective)
    hP hQ

/-- Source-specific binary `sup` closure for market-clearing cutoffs. -/
theorem al16SourceMarketClearing_sup_closed
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    {P Q : AL16Cutoff College}
    (hP : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P)
    (hQ : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Q) :
    al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity (P ⊔ Q) :=
  al16SourceMarketClearing_sup_closed_of_demand_primitives
    (al16SourceAggregateDemand mu) (al16SourceOutsideDemand mu) capacity
    (fun R => by
      simpa [al16SourceOutsideDemand, al16SourceAggregateDemand] using
        (al16UnitMassPartition_of_measure_choice
          mu al16SourceChoice al16SourceChoice_fiber_measurable R))
    (fun P Q =>
      by
        simpa [sup_comm] using
          al16Outside_le_sup_of_choice_semantics
            (al16SourceOutsideDemand mu) mu.real al16SourceScore
            al16SourcePrefers al16SourceChoice
            (fun {A B} hAB => al16MeasureMass_mono mu hAB)
            (fun _ => rfl) al16SourceChoice_semantics Q P)
    (fun P Q c hPQ =>
      al16AggregateDemand_le_sup_of_choice_semantics
        (al16SourceAggregateDemand mu) mu.real al16SourceScore
        al16SourcePrefers al16SourceChoice
        (fun {A B} hAB => al16MeasureMass_mono mu hAB)
        (fun _ _ => rfl) al16SourceChoice_semantics
        (al16RankPrefers_total al16SourceRank al16SourceRank_injective) hPQ)
    hP hQ

/-- Source-specific binary `inf` closure for market-clearing cutoffs. -/
theorem al16SourceMarketClearing_inf_closed
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    {P Q : AL16Cutoff College}
    (hP : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P)
    (hQ : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Q) :
    al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity (P ⊓ Q) :=
  al16SourceMarketClearing_inf_closed_of_demand_primitives
    (al16SourceAggregateDemand mu) (al16SourceOutsideDemand mu) capacity
    (fun R => by
      simpa [al16SourceOutsideDemand, al16SourceAggregateDemand] using
        (al16UnitMassPartition_of_measure_choice
          mu al16SourceChoice al16SourceChoice_fiber_measurable R))
    (fun P Q =>
      by
        simpa [sup_comm] using
          al16Outside_le_sup_of_choice_semantics
            (al16SourceOutsideDemand mu) mu.real al16SourceScore
            al16SourcePrefers al16SourceChoice
            (fun {A B} hAB => al16MeasureMass_mono mu hAB)
            (fun _ => rfl) al16SourceChoice_semantics Q P)
    (fun P Q c hPQ =>
      al16AggregateDemand_le_sup_of_choice_semantics
        (al16SourceAggregateDemand mu) mu.real al16SourceScore
        al16SourcePrefers al16SourceChoice
        (fun {A B} hAB => al16MeasureMass_mono mu hAB)
        (fun _ _ => rfl) al16SourceChoice_semantics
        (al16RankPrefers_total al16SourceRank al16SourceRank_injective) hPQ)
    (fun P Q =>
      al16Outside_inf_le_of_choice_semantics
        (al16SourceOutsideDemand mu) mu.real al16SourceScore
        al16SourcePrefers al16SourceChoice
        (fun {A B} hAB => al16MeasureMass_mono mu hAB)
        (fun _ => rfl) al16SourceChoice_semantics P Q)
    (fun P Q c hPQ =>
      al16AggregateDemand_inf_le_of_choice_semantics
        (al16SourceAggregateDemand mu) mu.real al16SourceScore
        al16SourcePrefers al16SourceChoice
        (fun {A B} hAB => al16MeasureMass_mono mu hAB)
        (fun _ _ => rfl) al16SourceChoice_semantics
        (al16RankPrefers_total al16SourceRank al16SourceRank_injective) hPQ)
    hP hQ

/--
Theorem 1 part (1), cutoff form: the full-support slab condition rules out two
distinct source market-clearing cutoff vectors.
-/
theorem al16SourceMarketClearing_unique_of_fullSupport
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hfull : al16SourceFullSupportCutoffSlabs mu) :
    ∀ P Q : AL16Cutoff College,
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P ->
        al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Q ->
          P = Q := by
  classical
  intro P Q hP hQ
  let bot : AL16Cutoff College := P ⊓ Q
  let top : AL16Cutoff College := P ⊔ Q
  have hbot : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity bot := by
    simpa [bot] using al16SourceMarketClearing_inf_closed mu capacity hP hQ
  have htop : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity top := by
    simpa [top] using al16SourceMarketClearing_sup_closed mu capacity hP hQ
  have hbot_le_top : ∀ c : College,
      al16CutoffValue bot c ≤ al16CutoffValue top c := by
    intro c
    change min ((P c : Set.Icc (0 : ℝ) 1) : ℝ) ((Q c : Set.Icc (0 : ℝ) 1) : ℝ) ≤
      max ((P c : Set.Icc (0 : ℝ) 1) : ℝ) ((Q c : Set.Icc (0 : ℝ) 1) : ℝ)
    exact (min_le_left _ _).trans (le_max_left _ _)
  let Cplus : Finset College :=
    Finset.univ.filter fun c => al16CutoffValue bot c < al16CutoffValue top c
  by_cases hCplus : Cplus.Nonempty
  · have hwidth : ∀ c : College, c ∈ Cplus ->
        al16CutoffValue bot c < al16CutoffValue top c := by
      intro c hc
      exact (Finset.mem_filter.mp hc).2
    rcases hfull Cplus bot top hCplus hwidth with ⟨rank, hprior, hslab_pos⟩
    let outcomes : Finset (Option College) := Cplus.image fun c => some c
    let B : Set (AL16SourceStudent College) :=
      (al16SourceChoice bot) ⁻¹' (outcomes : Set (Option College))
    let T : Set (AL16SourceStudent College) :=
      (al16SourceChoice top) ⁻¹' (outcomes : Set (Option College))
    have hchoice_mass_eq :
        mu.real B = mu.real T := by
      have hsumB :
          (∑ o ∈ outcomes,
              mu.real ((al16SourceChoice bot) ⁻¹' ({o} : Set (Option College)))) =
            mu.real B := by
        simpa [B] using
          (sum_measureReal_preimage_singleton (μ := mu) outcomes
            (f := al16SourceChoice bot)
            (by
              intro o ho
              rcases Finset.mem_image.mp ho with ⟨c, _hc, rfl⟩
              exact al16SourceChoice_fiber_measurable bot (some c)))
      have hsumT :
          (∑ o ∈ outcomes,
              mu.real ((al16SourceChoice top) ⁻¹' ({o} : Set (Option College)))) =
            mu.real T := by
        simpa [T] using
          (sum_measureReal_preimage_singleton (μ := mu) outcomes
            (f := al16SourceChoice top)
            (by
              intro o ho
              rcases Finset.mem_image.mp ho with ⟨c, _hc, rfl⟩
              exact al16SourceChoice_fiber_measurable top (some c)))
      have hdemand_eq :
          ∀ c : College,
            al16SourceAggregateDemand mu bot c = al16SourceAggregateDemand mu top c :=
        al16SourceAggregateDemand_eq_of_marketClearing mu capacity hbot htop
      have hsum_eq :
          (∑ o ∈ outcomes,
              mu.real ((al16SourceChoice bot) ⁻¹' ({o} : Set (Option College)))) =
            (∑ o ∈ outcomes,
              mu.real ((al16SourceChoice top) ⁻¹' ({o} : Set (Option College)))) := by
        refine Finset.sum_congr rfl ?_
        intro o ho
        rcases Finset.mem_image.mp ho with ⟨c, _hc, rfl⟩
        simpa [al16SourceAggregateDemand, al16DemandChoiceSet] using hdemand_eq c
      rw [← hsumB, ← hsumT]
      exact hsum_eq
    have hT_meas : MeasurableSet T := by
      have hT_eq :
          T =
            ⋃ o ∈ outcomes,
              (al16SourceChoice top) ⁻¹' ({o} : Set (Option College)) := by
        ext theta
        simp [T]
      rw [hT_eq]
      exact Finset.measurableSet_biUnion outcomes
        (fun o ho => by
          rcases Finset.mem_image.mp ho with ⟨c, _hc, rfl⟩
          exact al16SourceChoice_fiber_measurable top (some c))
    have hT_subset_B : T ⊆ B := by
      intro theta htheta
      change al16SourceChoice top theta ∈ outcomes at htheta
      rcases Finset.mem_image.mp htheta with ⟨c, hc, hsome⟩
      have htop_choice : al16SourceChoice top theta = some c := hsome.symm
      have htop_semantics := al16SourceChoice_semantics top theta
      rw [htop_choice] at htop_semantics
      have hc_affordable_bot :
          al16CutoffValue bot c ≤ al16ScoreValue al16SourceScore theta c :=
        (hbot_le_top c).trans htop_semantics.1
      cases hbot_choice : al16SourceChoice bot theta with
      | none =>
          have hbot_semantics := al16SourceChoice_semantics bot theta
          rw [hbot_choice] at hbot_semantics
          exact False.elim ((not_lt_of_ge hc_affordable_bot) (hbot_semantics c))
      | some d =>
          by_cases hd : d ∈ Cplus
          · change al16SourceChoice bot theta ∈ outcomes
            rw [hbot_choice]
            exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
          · have hbot_semantics := al16SourceChoice_semantics bot theta
            rw [hbot_choice] at hbot_semantics
            have hnot_lt :
                ¬ al16CutoffValue bot d < al16CutoffValue top d := by
              intro hlt
              exact hd (by simp [Cplus, hlt])
            have htop_le_bot_d :
                al16CutoffValue top d ≤ al16CutoffValue bot d :=
              le_of_not_gt hnot_lt
            have hd_affordable_top :
                al16CutoffValue top d ≤ al16ScoreValue al16SourceScore theta d :=
              htop_le_bot_d.trans hbot_semantics.1
            have hnot_d_pref_c := htop_semantics.2 d hd_affordable_top
            have hnot_c_pref_d := hbot_semantics.2 c hc_affordable_bot
            rcases al16RankPrefers_total al16SourceRank al16SourceRank_injective
                theta c d with hcd | hcd_pref | hdc_pref
            · subst d
              exact False.elim (hd hc)
            · exact False.elim (hnot_c_pref_d hcd_pref)
            · exact False.elim (hnot_d_pref_c hdc_pref)
    have hdiff_zero : mu.real (B \ T) = 0 := by
      rw [measureReal_diff hT_subset_B hT_meas, hchoice_mass_eq]
      exact sub_self _
    obtain ⟨c0, hc0⟩ := hCplus
    have hslab_subset : al16SourceCutoffSlab Cplus rank bot top ⊆ B \ T := by
      intro theta htheta
      constructor
      · change al16SourceChoice bot theta ∈ outcomes
        have hc0_affordable :
            al16CutoffValue bot c0 ≤ al16ScoreValue al16SourceScore theta c0 :=
          (htheta.2 c0 hc0).1
        cases hbot_choice : al16SourceChoice bot theta with
        | none =>
            have hbot_semantics := al16SourceChoice_semantics bot theta
            rw [hbot_choice] at hbot_semantics
            exact False.elim ((not_lt_of_ge hc0_affordable) (hbot_semantics c0))
        | some d =>
            by_cases hd : d ∈ Cplus
            · exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
            · have hbot_semantics := al16SourceChoice_semantics bot theta
              rw [hbot_choice] at hbot_semantics
              have hpref :
                  al16SourcePrefers theta (some c0) (some d) := by
                have hrank_lt := hprior c0 d hc0 hd
                change al16SourceRank theta c0 < al16SourceRank theta d
                simpa [al16SourceRank, htheta.1] using hrank_lt
              exact False.elim ((hbot_semantics.2 c0 hc0_affordable) hpref)
      · intro hthetaT
        change al16SourceChoice top theta ∈ outcomes at hthetaT
        rcases Finset.mem_image.mp hthetaT with ⟨c, hc, hsome⟩
        have htop_choice : al16SourceChoice top theta = some c := hsome.symm
        have htop_semantics := al16SourceChoice_semantics top theta
        rw [htop_choice] at htop_semantics
        exact (not_lt_of_ge htop_semantics.1) ((htheta.2 c hc).2)
    have hslab_le_zero :
        mu.real (al16SourceCutoffSlab Cplus rank bot top) ≤ 0 := by
      have hle := measureReal_mono hslab_subset (measure_ne_top mu _)
      simpa [hdiff_zero] using hle
    exact False.elim ((not_lt_of_ge hslab_le_zero) hslab_pos)
  · have hCempty : Cplus = ∅ := Finset.not_nonempty_iff_eq_empty.mp hCplus
    funext c
    apply Subtype.ext
    have hnot_lt : ¬ al16CutoffValue bot c < al16CutoffValue top c := by
      intro hlt
      have hc : c ∈ Cplus := by
        simp [Cplus, hlt]
      simpa [hCempty] using hc
    have htop_le_bot : al16CutoffValue top c ≤ al16CutoffValue bot c :=
      le_of_not_gt hnot_lt
    have hbot_top :
        al16CutoffValue bot c = al16CutoffValue top c :=
      le_antisymm (hbot_le_top c) htop_le_bot
    have hminmax :
        min ((P c : Set.Icc (0 : ℝ) 1) : ℝ) ((Q c : Set.Icc (0 : ℝ) 1) : ℝ) =
          max ((P c : Set.Icc (0 : ℝ) 1) : ℝ) ((Q c : Set.Icc (0 : ℝ) 1) : ℝ) := by
      simpa [bot, top, al16CutoffValue] using hbot_top
    apply le_antisymm
    · calc
        ((P c : Set.Icc (0 : ℝ) 1) : ℝ) ≤
            max ((P c : Set.Icc (0 : ℝ) 1) : ℝ)
              ((Q c : Set.Icc (0 : ℝ) 1) : ℝ) := le_max_left _ _
        _ = min ((P c : Set.Icc (0 : ℝ) 1) : ℝ)
              ((Q c : Set.Icc (0 : ℝ) 1) : ℝ) := hminmax.symm
        _ ≤ ((Q c : Set.Icc (0 : ℝ) 1) : ℝ) := min_le_right _ _
    · calc
        ((Q c : Set.Icc (0 : ℝ) 1) : ℝ) ≤
            max ((P c : Set.Icc (0 : ℝ) 1) : ℝ)
              ((Q c : Set.Icc (0 : ℝ) 1) : ℝ) := le_max_right _ _
        _ = min ((P c : Set.Icc (0 : ℝ) 1) : ℝ)
              ((Q c : Set.Icc (0 : ℝ) 1) : ℝ) := hminmax.symm
        _ ≤ ((P c : Set.Icc (0 : ℝ) 1) : ℝ) := min_le_left _ _

/-- An underfilled stable college has zero marginal cutoff. -/
theorem al16SourceMatchingCutoff_eq_zero_of_stable_underfilled
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (matching : AL16SourceStudent College -> Option College)
    (hstable : al16SourceStableMatching mu capacity matching)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hstrict : al16SourceStrictPreferences mu)
    {c : College}
    (hunder :
      mu.real (al16SourceMatchingCollegeSet matching c) < capacity c) :
    al16CutoffValue (al16SourceMatchingCutoff matching) c = 0 := by
  have hP : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity
      (al16SourceMatchingCutoff matching) :=
    al16SourceMatchingCutoff_marketClearing_of_stable
      mu capacity matching hstable hcapacity_pos hstrict
  have hchoice := al16SourceChoice_matchingCutoff_eq_of_stable
    mu capacity matching hstable hcapacity_pos hstrict
  have hchoiceSet :
      al16DemandChoiceSet al16SourceChoice (al16SourceMatchingCutoff matching) c =
        al16SourceMatchingCollegeSet matching c := by
    ext theta
    change al16SourceChoice (al16SourceMatchingCutoff matching) theta = some c ↔
      matching theta = some c
    rw [hchoice theta]
  apply le_antisymm
  · apply le_of_not_gt
    intro hpositive
    have hfill := hP.2 c hpositive
    change mu.real
        (al16DemandChoiceSet al16SourceChoice (al16SourceMatchingCutoff matching) c) =
      capacity c at hfill
    rw [hchoiceSet] at hfill
    exact (ne_of_lt hunder) hfill
  · exact (al16SourceMatchingCutoff matching c).property.1

/--
The first clause of Theorem A2 for the literal source carrier: every pair of
stable matchings assigns the same probability mass to each college.  The proof
uses Lemma 1 to move each stable matching to its marginal clearing cutoff, then
applies the equal-demand step from the Theorem A1 proof.
-/
theorem al16SourceStableMatching_college_mass_eq
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (matching matching' : AL16SourceStudent College -> Option College)
    (hstable : al16SourceStableMatching mu capacity matching)
    (hstable' : al16SourceStableMatching mu capacity matching')
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hstrict : al16SourceStrictPreferences mu) :
    ∀ c : College,
      mu.real (al16SourceMatchingCollegeSet matching c) =
        mu.real (al16SourceMatchingCollegeSet matching' c) := by
  let P := al16SourceMatchingCutoff matching
  let Q := al16SourceMatchingCutoff matching'
  have hP : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P :=
    al16SourceMatchingCutoff_marketClearing_of_stable
      mu capacity matching hstable hcapacity_pos hstrict
  have hQ : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Q :=
    al16SourceMatchingCutoff_marketClearing_of_stable
      mu capacity matching' hstable' hcapacity_pos hstrict
  have hdemand_eq :=
    al16SourceAggregateDemand_eq_of_marketClearing mu capacity hP hQ
  have hchoice :=
    al16SourceChoice_matchingCutoff_eq_of_stable
      mu capacity matching hstable hcapacity_pos hstrict
  have hchoice' :=
    al16SourceChoice_matchingCutoff_eq_of_stable
      mu capacity matching' hstable' hcapacity_pos hstrict
  intro c
  have hset :
      al16DemandChoiceSet al16SourceChoice P c =
        al16SourceMatchingCollegeSet matching c := by
    ext theta
    change al16SourceChoice P theta = some c ↔ matching theta = some c
    rw [hchoice theta]
  have hset' :
      al16DemandChoiceSet al16SourceChoice Q c =
        al16SourceMatchingCollegeSet matching' c := by
    ext theta
    change al16SourceChoice Q theta = some c ↔ matching' theta = some c
    rw [hchoice' theta]
  change mu.real (al16SourceMatchingCollegeSet matching c) =
    mu.real (al16SourceMatchingCollegeSet matching' c)
  rw [← hset, ← hset']
  exact hdemand_eq c

/--
The unmatched-mass clause following Theorem A2 for the literal source carrier:
every pair of stable matchings leaves the same probability mass unmatched.
This is derived from the finite partition into the outside option and college
fibers, together with the equal-demand step used in Theorem A2's first clause.
-/
theorem al16SourceStableMatching_unmatched_mass_eq
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (matching matching' : AL16SourceStudent College -> Option College)
    (hstable : al16SourceStableMatching mu capacity matching)
    (hstable' : al16SourceStableMatching mu capacity matching')
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hstrict : al16SourceStrictPreferences mu) :
    mu.real (al16SourceMatchingUnmatchedSet matching) =
      mu.real (al16SourceMatchingUnmatchedSet matching') := by
  let P := al16SourceMatchingCutoff matching
  let Q := al16SourceMatchingCutoff matching'
  have hP : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P :=
    al16SourceMatchingCutoff_marketClearing_of_stable
      mu capacity matching hstable hcapacity_pos hstrict
  have hQ : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Q :=
    al16SourceMatchingCutoff_marketClearing_of_stable
      mu capacity matching' hstable' hcapacity_pos hstrict
  have hdemand_eq :
      ∀ c : College,
        al16SourceAggregateDemand mu P c =
          al16SourceAggregateDemand mu Q c :=
    al16SourceAggregateDemand_eq_of_marketClearing mu capacity hP hQ
  have hsum_eq :
      (∑ c : College, al16SourceAggregateDemand mu P c) =
        ∑ c : College, al16SourceAggregateDemand mu Q c := by
    exact Finset.sum_congr rfl (fun c _ => hdemand_eq c)
  have hpartitionP :
      al16SourceOutsideDemand mu P +
          ∑ c : College, al16SourceAggregateDemand mu P c = 1 := by
    simpa [al16SourceOutsideDemand, al16SourceAggregateDemand] using
      (al16UnitMassPartition_of_measure_choice
        mu al16SourceChoice al16SourceChoice_fiber_measurable P)
  have hpartitionQ :
      al16SourceOutsideDemand mu Q +
          ∑ c : College, al16SourceAggregateDemand mu Q c = 1 := by
    simpa [al16SourceOutsideDemand, al16SourceAggregateDemand] using
      (al16UnitMassPartition_of_measure_choice
        mu al16SourceChoice al16SourceChoice_fiber_measurable Q)
  have houtside_eq : al16SourceOutsideDemand mu P = al16SourceOutsideDemand mu Q := by
    nlinarith
  have hchoice :=
    al16SourceChoice_matchingCutoff_eq_of_stable
      mu capacity matching hstable hcapacity_pos hstrict
  have hchoice' :=
    al16SourceChoice_matchingCutoff_eq_of_stable
      mu capacity matching' hstable' hcapacity_pos hstrict
  have houtside_set :
      al16OutsideChoiceSet al16SourceChoice P =
        al16SourceMatchingUnmatchedSet matching := by
    ext theta
    change al16SourceChoice P theta = none ↔ matching theta = none
    rw [hchoice theta]
  have houtside_set' :
      al16OutsideChoiceSet al16SourceChoice Q =
        al16SourceMatchingUnmatchedSet matching' := by
    ext theta
    change al16SourceChoice Q theta = none ↔ matching' theta = none
    rw [hchoice' theta]
  simpa [al16SourceOutsideDemand, houtside_set, houtside_set'] using houtside_eq

/--
The second clause of Theorem A2 for the literal source carrier: if a college is
underfilled in one stable matching, then its assigned set agrees with its
assigned set in any other stable matching up to zero measure.
-/
theorem al16SourceStableMatching_underfilled_college_sets_ae_eq
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (matching matching' : AL16SourceStudent College -> Option College)
    (hstable : al16SourceStableMatching mu capacity matching)
    (hstable' : al16SourceStableMatching mu capacity matching')
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hstrict : al16SourceStrictPreferences mu)
    {c : College}
    (hunder :
      mu.real (al16SourceMatchingCollegeSet matching c) < capacity c) :
    mu.real
        (al16SourceMatchingCollegeSet matching c \
          al16SourceMatchingCollegeSet matching' c) = 0 ∧
      mu.real
        (al16SourceMatchingCollegeSet matching' c \
          al16SourceMatchingCollegeSet matching c) = 0 := by
  let P := al16SourceMatchingCutoff matching
  let Q := al16SourceMatchingCutoff matching'
  let R := P ⊔ Q
  let A := al16SourceMatchingCollegeSet matching c
  let B := al16SourceMatchingCollegeSet matching' c
  let U := al16DemandChoiceSet al16SourceChoice R c
  have hP : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P :=
    al16SourceMatchingCutoff_marketClearing_of_stable
      mu capacity matching hstable hcapacity_pos hstrict
  have hQ : al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity Q :=
    al16SourceMatchingCutoff_marketClearing_of_stable
      mu capacity matching' hstable' hcapacity_pos hstrict
  have hchoice :=
    al16SourceChoice_matchingCutoff_eq_of_stable
      mu capacity matching hstable hcapacity_pos hstrict
  have hchoice' :=
    al16SourceChoice_matchingCutoff_eq_of_stable
      mu capacity matching' hstable' hcapacity_pos hstrict
  have hmass_eq :=
    al16SourceStableMatching_college_mass_eq
      mu capacity matching matching' hstable hstable' hcapacity_pos hstrict c
  have hunder' :
      mu.real (al16SourceMatchingCollegeSet matching' c) < capacity c := by
    rw [← hmass_eq]
    exact hunder
  have hP_zero : al16CutoffValue P c = 0 :=
    al16SourceMatchingCutoff_eq_zero_of_stable_underfilled
      mu capacity matching hstable hcapacity_pos hstrict hunder
  have hQ_zero : al16CutoffValue Q c = 0 :=
    al16SourceMatchingCutoff_eq_zero_of_stable_underfilled
      mu capacity matching' hstable' hcapacity_pos hstrict hunder'
  have hA_meas : MeasurableSet A := hstable.1.1 c
  have hB_meas : MeasurableSet B := hstable'.1.1 c
  have hA_choice :
      al16DemandChoiceSet al16SourceChoice P c = A := by
    ext theta
    change al16SourceChoice P theta = some c ↔ matching theta = some c
    rw [hchoice theta]
  have hB_choice :
      al16DemandChoiceSet al16SourceChoice Q c = B := by
    ext theta
    change al16SourceChoice Q theta = some c ↔ matching' theta = some c
    rw [hchoice' theta]
  have hA_subset_U : A ⊆ U := by
    intro theta htheta
    change matching theta = some c at htheta
    have hchoiceP : al16SourceChoice P theta = some c := by
      rw [hchoice theta, htheta]
    have hQP : al16CutoffValue Q c ≤ al16CutoffValue P c := by
      rw [hP_zero, hQ_zero]
    have hsup := al16Choice_sup_eq_of_choice_eq
      al16SourceScore al16SourcePrefers al16SourceChoice al16SourceChoice_semantics
      (al16RankPrefers_total al16SourceRank al16SourceRank_injective)
      (P := Q) (Q := P) (theta := theta) (c := c) hQP hchoiceP
    change al16SourceChoice R theta = some c
    simpa [R, sup_comm] using hsup
  have hB_subset_U : B ⊆ U := by
    intro theta htheta
    change matching' theta = some c at htheta
    have hchoiceQ : al16SourceChoice Q theta = some c := by
      rw [hchoice' theta, htheta]
    have hPQ : al16CutoffValue P c ≤ al16CutoffValue Q c := by
      rw [hP_zero, hQ_zero]
    exact al16Choice_sup_eq_of_choice_eq
      al16SourceScore al16SourcePrefers al16SourceChoice al16SourceChoice_semantics
      (al16RankPrefers_total al16SourceRank al16SourceRank_injective)
      (P := P) (Q := Q) (theta := theta) (c := c) hPQ hchoiceQ
  have hA_mass_eq_U : mu.real A = mu.real U := by
    rw [← hA_choice]
    change al16SourceAggregateDemand mu P c = al16SourceAggregateDemand mu R c
    simpa [R] using
      al16SourceAggregateDemand_eq_sup_of_marketClearing mu capacity hP hQ c
  have hB_mass_eq_U : mu.real B = mu.real U := by
    rw [← hB_choice]
    change al16SourceAggregateDemand mu Q c = al16SourceAggregateDemand mu R c
    simpa [R, sup_comm] using
      al16SourceAggregateDemand_eq_sup_of_marketClearing mu capacity hQ hP c
  have hU_diff_A_zero : mu.real (U \ A) = 0 := by
    rw [measureReal_diff hA_subset_U hA_meas, hA_mass_eq_U]
    exact sub_self _
  have hU_diff_B_zero : mu.real (U \ B) = 0 := by
    rw [measureReal_diff hB_subset_U hB_meas, hB_mass_eq_U]
    exact sub_self _
  have hA_diff_B_subset : A \ B ⊆ U \ B := by
    intro theta htheta
    exact ⟨hA_subset_U htheta.1, htheta.2⟩
  have hB_diff_A_subset : B \ A ⊆ U \ A := by
    intro theta htheta
    exact ⟨hB_subset_U htheta.1, htheta.2⟩
  constructor
  · apply le_antisymm
    · have hle := measureReal_mono hA_diff_B_subset (measure_ne_top mu _)
      rw [hU_diff_B_zero] at hle
      exact hle
    · positivity
  · apply le_antisymm
    · have hle := measureReal_mono hB_diff_A_subset (measure_ne_top mu _)
      rw [hU_diff_A_zero] at hle
      exact hle
    · positivity

/--
Theorem A.1's lattice conclusion for the literal source carrier after the
separate source existence proof has supplied a nonempty clearing set. All
measure, ranking, choice, and aggregate-demand continuity facts are derived
above from the literal primitives.
-/
theorem al16SourceMarketClearing_completeLattice_of_concrete_continuum_primitives
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hnonempty : ∃ P : AL16Cutoff College,
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P) :
    CompleteLatticeOn (al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity)
      al16CutoffLe :=
  al16SourceMarketClearing_completeLattice_of_probability_measure_ranked_choice_primitives
    mu (al16SourceAggregateDemand mu) (al16SourceOutsideDemand mu) capacity
    al16SourceScore al16SourceRank (fun _ _ => rfl) (fun _ => rfl)
    al16SourceScore_measurable al16SourceRank_measurable al16SourceRank_injective
    (fun P Q hPQ c =>
      al16SourceAggregateDemand_tendsto_of_coordinatewiseTendsto
        mu hstrict P Q hPQ c)
    hnonempty

/--
The conditional A1 assembly lemma used before the source nonempty-clearing
argument is supplied. The unconditional source theorem is in
`ContinuumExistence.lean`.
-/
theorem al16TheoremA1_of_concrete_continuum_primitives_of_nonempty
    (mu : Measure (AL16SourceStudent College)) [IsProbabilityMeasure mu]
    (capacity : College -> ℝ)
    (hstrict : al16SourceStrictPreferences mu)
    (hnonempty :
      ∃ P : AL16Cutoff College,
        al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P) :
    (∃ P : AL16Cutoff College,
      al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity P) ∧
      CompleteLatticeOn (al16SourceMarketClearing (al16SourceAggregateDemand mu) capacity)
        al16CutoffLe :=
  ⟨hnonempty,
    al16SourceMarketClearing_completeLattice_of_concrete_continuum_primitives
      mu capacity hstrict hnonempty⟩

end AL16SupplyDemandMatching
