import PG23MonocultureMatching.ConcreteCutoffProofs
import Mathlib.Tactic

/-!
# PG23 Concrete Stability and Clearing

This module proves the paper's literal Supply and Demand Lemma for the raw
real-score carrier.  The proof uses PG23's exact-fill and open-preference-set
matching conditions directly; it does not identify them with AL16's distinct
weak-capacity/right-continuity definition.

Source anchors: `source_tex/model.tex:12-20,22-44`.
-/

namespace PG23MonocultureMatching

open MeasureTheory Set
open AL16SupplyDemandMatching

universe v

variable {College : Type v} [Fintype College] [Nonempty College]

/-- A college is preferred to the favorite affordable choice exactly when it
and every weakly better-ranked college are unaffordable. -/
theorem pg23SourcePrefers_choice_iff
    (P : College -> ℝ) (theta : PG23ApplicantType College) (c : College) :
    pg23SourcePrefers theta (some c) (pg23SourceChoice P theta) ↔
      ∀ d : College, pg23SourceRank theta d ≤ pg23SourceRank theta c ->
        pg23SourceScore theta d < P d := by
  have hsem := pg23SourceChoice_semantics (College := College) P theta
  cases hchoice : pg23SourceChoice P theta with
  | none =>
      rw [hchoice] at hsem
      constructor
      · intro _ d _
        exact hsem d
      · intro _
        simp [pg23SourcePrefers, al16RankPrefers]
  | some a =>
      rw [hchoice] at hsem
      constructor
      · intro hpreferred d hd
        by_contra hnot
        have haffordable : P d ≤ pg23SourceScore theta d := le_of_not_gt hnot
        have hnotpreferred := hsem.2 d haffordable
        apply hnotpreferred
        change pg23SourceRank theta d < pg23SourceRank theta a
        exact hd.trans_lt (by
          simpa [pg23SourcePrefers, al16RankPrefers, hchoice] using hpreferred)
      · intro h
        change pg23SourceRank theta c < pg23SourceRank theta a
        by_contra hnot
        have ha_le_c : pg23SourceRank theta a ≤ pg23SourceRank theta c :=
          le_of_not_gt hnot
        exact (not_lt_of_ge hsem.1) (h a ha_le_c)

/-- The source openness condition holds for every literal cutoff-demand matching. -/
theorem pg23SourceChoice_preferredCollegeSet_open
    (P : College -> ℝ) (c : College) : by
    letI : TopologicalSpace (PG23Ranking College) := ⊥
    letI : DiscreteTopology (PG23Ranking College) := discreteTopology_bot _
    exact IsOpen {theta : PG23ApplicantType College |
      pg23SourcePrefers theta (some c) (pg23SourceChoice P theta)} := by
  letI : TopologicalSpace (PG23Ranking College) := ⊥
  letI : DiscreteTopology (PG23Ranking College) := discreteTopology_bot _
  rw [isOpen_iff_mem_nhds]
  intro theta htheta
  change pg23SourcePrefers theta (some c) (pg23SourceChoice P theta) at htheta
  rw [pg23SourcePrefers_choice_iff] at htheta
  let U : Set (PG23ApplicantType College) :=
    {z | z.1 = theta.1} ∩
      ⋂ d : College,
        if pg23SourceRank theta d ≤ pg23SourceRank theta c then
          {z | pg23SourceScore z d < P d}
        else Set.univ
  have hopenRank : IsOpen {z : PG23ApplicantType College | z.1 = theta.1} := by
    have hsingleton : IsOpen ({theta.1} : Set (PG23Ranking College)) :=
      isOpen_discrete _
    exact hsingleton.preimage continuous_fst
  have hopenScore (d : College) :
      IsOpen {z : PG23ApplicantType College | pg23SourceScore z d < P d} := by
    change IsOpen {z : PG23ApplicantType College | z.2 d < P d}
    exact isOpen_lt (by fun_prop) continuous_const
  have hopenU : IsOpen U := by
    apply hopenRank.inter
    apply isOpen_iInter_of_finite
    intro d
    split_ifs
    · exact hopenScore d
    · exact isOpen_univ
  have hthetaU : theta ∈ U := by
    constructor
    · rfl
    · rw [Set.mem_iInter]
      intro d
      split_ifs with hd
      · exact htheta d hd
      · exact Set.mem_univ _
  apply Filter.mem_of_superset (hopenU.mem_nhds hthetaU)
  intro z hz
  change pg23SourcePrefers z (some c) (pg23SourceChoice P z)
  rw [pg23SourcePrefers_choice_iff]
  intro d hd
  have hrank : pg23SourceRank theta d ≤ pg23SourceRank theta c := by
    change (theta.1 d).val ≤ (theta.1 c).val
    change (z.1 d).val ≤ (z.1 c).val at hd
    rw [hz.1] at hd
    exact hd
  have hzd := Set.mem_iInter.mp hz.2 d
  simpa [hrank] using hzd

/-- Every literal exact-clearing cutoff induces a PG23-stable matching. -/
theorem pg23SourceChoice_stable_of_marketClearing
    (typeLaw : Measure (PG23ApplicantType College)) (capacity : College -> ℝ)
    (P : College -> ℝ)
    (hP : pg23SourceMarketClearing
      (pg23SourceAggregateDemand typeLaw) capacity P) :
    pg23SourceStableMatching typeLaw capacity (pg23SourceChoice P) := by
  constructor
  · unfold pg23SourceMatchingFeasible
    letI : TopologicalSpace (PG23Ranking College) := ⊥
    letI : DiscreteTopology (PG23Ranking College) := discreteTopology_bot _
    refine ⟨?_, ?_, ?_⟩
    · intro c
      exact hP c
    · intro c
      exact pg23SourceChoice_fiber_measurable P (some c)
    · intro c
      exact pg23SourceChoice_preferredCollegeSet_open P c
  · intro theta c hblocks
    rcases hblocks with ⟨hpreferred, theta', htheta', hlower⟩
    have htheta_lt : pg23SourceScore theta c < P c :=
      (pg23SourcePrefers_choice_iff P theta c).mp hpreferred c le_rfl
    have hsem := pg23SourceChoice_semantics (College := College) P theta'
    rw [htheta'] at hsem
    have hcutoff_le : P c ≤ pg23SourceScore theta' c := hsem.1
    exact (not_lt_of_ge (htheta_lt.trans_le hcutoff_le).le) hlower

/-- Scores of applicants assigned to one college by a raw PG23 matching. -/
def pg23SourceAssignedScoreSet (matching : PG23Matching College) (c : College) : Set ℝ :=
  (fun theta : PG23ApplicantType College => pg23SourceScore theta c) ''
    pg23MatchingCollegeSet matching c

/-- The raw marginal-score cutoff of a source matching. -/
noncomputable def pg23SourceMatchingCutoff
    (matching : PG23Matching College) : College -> ℝ :=
  fun c => sInf (pg23SourceAssignedScoreSet matching c)

/-- Exact fill below unit total mass leaves at least one unmatched applicant type. -/
theorem pg23SourceStableMatching_unmatched_exists
    (typeLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure typeLaw]
    (capacity : College -> ℝ) (matching : PG23Matching College)
    (hcapacity_sum : (∑ c : College, capacity c) < 1)
    (hstable : pg23SourceStableMatching typeLaw capacity matching) :
    ∃ theta : PG23ApplicantType College, matching theta = none := by
  classical
  have hfiber (o : Option College) :
      MeasurableSet (matching ⁻¹' ({o} : Set (Option College))) := by
    cases o with
    | none =>
        have hset : matching ⁻¹' ({none} : Set (Option College)) =
            (⋃ c : College, pg23MatchingCollegeSet matching c)ᶜ := by
          ext theta
          cases htheta : matching theta <;> simp [htheta, pg23MatchingCollegeSet]
        rw [hset]
        apply MeasurableSet.compl
        apply MeasurableSet.iUnion
        intro c
        exact hstable.1.2.1 c
    | some c =>
        have hset : matching ⁻¹' ({some c} : Set (Option College)) =
            pg23MatchingCollegeSet matching c := by
          ext theta
          simp [pg23MatchingCollegeSet]
        rw [hset]
        exact hstable.1.2.1 c
  have hpartition := MeasureTheory.sum_measureReal_preimage_singleton
    (μ := typeLaw) (Finset.univ : Finset (Option College))
    (f := matching) (fun o _ => hfiber o)
  have hmass : typeLaw.real (matching ⁻¹' ({none} : Set (Option College))) +
      ∑ c : College, capacity c = 1 := by
    calc
      typeLaw.real (matching ⁻¹' ({none} : Set (Option College))) +
          ∑ c : College, capacity c =
          typeLaw.real (matching ⁻¹' ({none} : Set (Option College))) +
            ∑ c : College,
              typeLaw.real (matching ⁻¹' ({some c} : Set (Option College))) := by
        congr 1
        apply Finset.sum_congr rfl
        intro c _
        simpa [pg23MatchingCollegeSet] using (hstable.1.1 c).symm
      _ = 1 := by simpa [Fintype.sum_option] using hpartition
  have hnone_pos : 0 < typeLaw.real
      (matching ⁻¹' ({none} : Set (Option College))) := by
    linarith
  have hnonempty : (matching ⁻¹' ({none} : Set (Option College))).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, measureReal_empty] at hnone_pos
    exact (lt_irrefl 0) hnone_pos
  rcases hnonempty with ⟨theta, htheta⟩
  exact ⟨theta, htheta⟩

/-- Positive exact fill makes each college's assigned-score set nonempty. -/
theorem pg23SourceAssignedScoreSet_nonempty
    (typeLaw : Measure (PG23ApplicantType College))
    (capacity : College -> ℝ) (matching : PG23Matching College)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hstable : pg23SourceStableMatching typeLaw capacity matching)
    (c : College) : (pg23SourceAssignedScoreSet matching c).Nonempty := by
  have hfiber : (pg23MatchingCollegeSet matching c).Nonempty := by
    by_contra hempty
    have hempty' := Set.not_nonempty_iff_eq_empty.mp hempty
    have hfill := hstable.1.1 c
    rw [hempty', measureReal_empty] at hfill
    linarith [hcapacity_pos c]
  rcases hfiber with ⟨theta, htheta⟩
  exact ⟨pg23SourceScore theta c, theta, htheta, rfl⟩

/-- An unmatched type supplies a lower bound for every assigned-score set in a stable matching. -/
theorem pg23SourceAssignedScoreSet_bddBelow_of_unmatched
    (typeLaw : Measure (PG23ApplicantType College))
    (capacity : College -> ℝ) (matching : PG23Matching College)
    (hstable : pg23SourceStableMatching typeLaw capacity matching)
    (theta0 : PG23ApplicantType College) (htheta0 : matching theta0 = none)
    (c : College) : BddBelow (pg23SourceAssignedScoreSet matching c) := by
  refine ⟨pg23SourceScore theta0 c, ?_⟩
  rintro _ ⟨theta', htheta', rfl⟩
  by_contra hnotle
  apply hstable.2 theta0 c
  refine ⟨?_, theta', ?_, lt_of_not_ge hnotle⟩
  · simp [pg23SourcePrefers, al16RankPrefers, htheta0]
  · simpa [pg23MatchingCollegeSet] using htheta'

/-- An assigned applicant's score weakly exceeds the marginal-score cutoff. -/
theorem pg23SourceMatchingCutoff_le_score_of_assigned
    (matching : PG23Matching College) (theta : PG23ApplicantType College) (c : College)
    (hbdd : BddBelow (pg23SourceAssignedScoreSet matching c))
    (hmatching : matching theta = some c) :
    pg23SourceMatchingCutoff matching c ≤ pg23SourceScore theta c := by
  unfold pg23SourceMatchingCutoff
  apply csInf_le hbdd
  exact ⟨theta, by simpa [pg23MatchingCollegeSet] using hmatching, rfl⟩

/-- Openness upgrades no blocking to a strict score gap below the marginal cutoff. -/
theorem pg23SourceStableMatching_preferred_score_lt_matchingCutoff
    (typeLaw : Measure (PG23ApplicantType College))
    (capacity : College -> ℝ) (matching : PG23Matching College)
    (hassigned_nonempty : ∀ c : College,
      (pg23SourceAssignedScoreSet matching c).Nonempty)
    (hstable : pg23SourceStableMatching typeLaw capacity matching)
    (theta : PG23ApplicantType College) (c : College)
    (hpreferred : pg23SourcePrefers theta (some c) (matching theta)) :
    pg23SourceScore theta c < pg23SourceMatchingCutoff matching c := by
  classical
  letI : TopologicalSpace (PG23Ranking College) := ⊥
  letI : DiscreteTopology (PG23Ranking College) := discreteTopology_bot _
  let perturb : ℝ -> PG23ApplicantType College :=
    fun x => ⟨theta.1, Function.update theta.2 c x⟩
  have hscore_continuous : Continuous
      (fun x : ℝ => Function.update theta.2 c x) := by
    apply continuous_pi
    intro d
    by_cases hdc : d = c
    · subst d
      simpa using (continuous_id : Continuous (fun x : ℝ => x))
    · simpa [Function.update_of_ne hdc] using
        (continuous_const : Continuous (fun _x : ℝ => theta.2 d))
  have hperturb_continuous : Continuous perturb :=
    continuous_const.prodMk hscore_continuous
  have hopen : IsOpen {z : PG23ApplicantType College |
      pg23SourcePrefers z (some c) (matching z)} := hstable.1.2.2 c
  have hopen_preimage : IsOpen (perturb ⁻¹' {z : PG23ApplicantType College |
      pg23SourcePrefers z (some c) (matching z)}) :=
    hopen.preimage hperturb_continuous
  have hperturb_self : perturb (pg23SourceScore theta c) = theta := by
    apply Prod.ext
    · rfl
    · funext d
      by_cases hdc : d = c
      · subst d
        simp [perturb, pg23SourceScore]
      · simp [perturb, Function.update_of_ne hdc]
  have hxmem : pg23SourceScore theta c ∈
      perturb ⁻¹' {z : PG23ApplicantType College |
        pg23SourcePrefers z (some c) (matching z)} := by
    change pg23SourcePrefers (perturb (pg23SourceScore theta c)) (some c)
      (matching (perturb (pg23SourceScore theta c)))
    rw [hperturb_self]
    exact hpreferred
  rcases Metric.mem_nhds_iff.mp (hopen_preimage.mem_nhds hxmem) with
    ⟨ε, hε, hball⟩
  let y : ℝ := pg23SourceScore theta c + ε / 2
  have hxy : pg23SourceScore theta c < y := by
    dsimp [y]
    linarith
  have hyball : y ∈ Metric.ball (pg23SourceScore theta c) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [y]
    rw [abs_of_nonneg]
    · linarith
    · linarith
  have hypreferred : pg23SourcePrefers (perturb y) (some c) (matching (perturb y)) := by
    exact hball hyball
  have hy_lower : ∀ b ∈ pg23SourceAssignedScoreSet matching c, y ≤ b := by
    rintro _ ⟨theta', htheta', rfl⟩
    by_contra hnotle
    apply hstable.2 (perturb y) c
    refine ⟨hypreferred, theta', ?_, ?_⟩
    · simpa [pg23MatchingCollegeSet] using htheta'
    · simpa [perturb, pg23SourceScore] using (lt_of_not_ge hnotle)
  exact hxy.trans_le (le_csInf (hassigned_nonempty c) hy_lower)

/-- Every source-stable matching is pointwise its marginal-cutoff demand matching. -/
theorem pg23SourceChoice_matchingCutoff_eq_of_stable
    (typeLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure typeLaw]
    (capacity : College -> ℝ) (matching : PG23Matching College)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hcapacity_sum : (∑ c : College, capacity c) < 1)
    (hstable : pg23SourceStableMatching typeLaw capacity matching) :
    ∀ theta : PG23ApplicantType College,
      pg23SourceChoice (pg23SourceMatchingCutoff matching) theta = matching theta := by
  obtain ⟨theta0, htheta0⟩ :=
    pg23SourceStableMatching_unmatched_exists
      typeLaw capacity matching hcapacity_sum hstable
  have hnonempty (c : College) :
      (pg23SourceAssignedScoreSet matching c).Nonempty :=
    pg23SourceAssignedScoreSet_nonempty
      typeLaw capacity matching hcapacity_pos hstable c
  have hbdd (c : College) : BddBelow (pg23SourceAssignedScoreSet matching c) :=
    pg23SourceAssignedScoreSet_bddBelow_of_unmatched
      typeLaw capacity matching hstable theta0 htheta0 c
  have hpreferred_gap (theta : PG23ApplicantType College) (c : College)
      (hpreferred : pg23SourcePrefers theta (some c) (matching theta)) :
      pg23SourceScore theta c < pg23SourceMatchingCutoff matching c :=
    pg23SourceStableMatching_preferred_score_lt_matchingCutoff
      typeLaw capacity matching hnonempty hstable theta c hpreferred
  intro theta
  cases hmatching : matching theta with
  | none =>
      cases hchoice : pg23SourceChoice (pg23SourceMatchingCutoff matching) theta with
      | none => simpa [hmatching] using hchoice
      | some c =>
          have hsem := pg23SourceChoice_semantics (College := College)
            (pg23SourceMatchingCutoff matching) theta
          rw [hchoice] at hsem
          have hpreferred : pg23SourcePrefers theta (some c) (matching theta) := by
            simp [pg23SourcePrefers, al16RankPrefers, hmatching]
          exact False.elim ((not_lt_of_ge hsem.1)
            (hpreferred_gap theta c hpreferred))
  | some a =>
      have haffordable : pg23SourceMatchingCutoff matching a ≤
          pg23SourceScore theta a :=
        pg23SourceMatchingCutoff_le_score_of_assigned
          matching theta a (hbdd a) hmatching
      cases hchoice : pg23SourceChoice (pg23SourceMatchingCutoff matching) theta with
      | none =>
          have hsem := pg23SourceChoice_semantics (College := College)
            (pg23SourceMatchingCutoff matching) theta
          rw [hchoice] at hsem
          exact False.elim ((not_lt_of_ge haffordable) (hsem a))
      | some d =>
          by_cases hda : d = a
          · subst d
            simpa [hmatching] using hchoice
          · have hsem := pg23SourceChoice_semantics (College := College)
              (pg23SourceMatchingCutoff matching) theta
            rw [hchoice] at hsem
            have htotal := al16RankPrefers_total pg23SourceRank
              pg23SourceRank_injective theta d a
            have hd_preferred : pg23SourcePrefers theta (some d) (some a) := by
              rcases htotal with hEq | hda_pref | had_pref
              · exact False.elim (hda hEq)
              · exact hda_pref
              · exact False.elim ((hsem.2 a haffordable) had_pref)
            have hgap := hpreferred_gap theta d (by
              simpa [hmatching] using hd_preferred)
            exact False.elim ((not_lt_of_ge hsem.1) hgap)

/-- The marginal cutoff of a source-stable matching clears every college exactly. -/
theorem pg23SourceMatchingCutoff_marketClearing_of_stable
    (typeLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure typeLaw]
    (capacity : College -> ℝ) (matching : PG23Matching College)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hcapacity_sum : (∑ c : College, capacity c) < 1)
    (hstable : pg23SourceStableMatching typeLaw capacity matching) :
    pg23SourceMarketClearing (pg23SourceAggregateDemand typeLaw) capacity
      (pg23SourceMatchingCutoff matching) := by
  have hchoice := pg23SourceChoice_matchingCutoff_eq_of_stable
    typeLaw capacity matching hcapacity_pos hcapacity_sum hstable
  intro c
  calc
    pg23SourceAggregateDemand typeLaw (pg23SourceMatchingCutoff matching) c =
        typeLaw.real (pg23MatchingCollegeSet matching c) := by
      unfold pg23SourceAggregateDemand
      congr 1
      ext theta
      simp only [pg23MatchingCollegeSet, Set.mem_setOf_eq]
      rw [hchoice theta]
    _ = capacity c := hstable.1.1 c

/--
PG23's literal Supply and Demand Lemma, proved from the paper's positive seats
and subunit total-seat mass assumptions.
-/
theorem pg23SupplyDemandLemma_of_primitives
    (typeLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure typeLaw]
    (capacity : College -> ℝ)
    (hcapacity_pos : ∀ c : College, 0 < capacity c)
    (hcapacity_sum : (∑ c : College, capacity c) < 1) :
    pg23SupplyDemandLemmaStatement typeLaw capacity := by
  intro matching
  constructor
  · intro hstable
    refine ⟨pg23SourceMatchingCutoff matching,
      pg23SourceMatchingCutoff_marketClearing_of_stable
        typeLaw capacity matching hcapacity_pos hcapacity_sum hstable, ?_⟩
    funext theta
    exact (pg23SourceChoice_matchingCutoff_eq_of_stable
      typeLaw capacity matching hcapacity_pos hcapacity_sum hstable theta).symm
  · rintro ⟨P, hP, rfl⟩
    exact pg23SourceChoice_stable_of_marketClearing typeLaw capacity P hP

private theorem equalCapacity_pos (S : ℝ) (hS : 0 < S) :
    ∀ c : College, 0 < S / (Fintype.card College : ℝ) := by
  intro c
  apply div_pos hS
  exact_mod_cast Fintype.card_pos

private theorem equalCapacity_sum (S : ℝ) :
    (∑ _c : College, S / (Fintype.card College : ℝ)) = S := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Source Lemma 1 for the literal monoculture law and equal capacities. -/
theorem pg23MonocultureSupplyDemandLemma_of_primitives
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    pg23MonocultureSupplyDemandLemmaStatement valueLaw noiseLaw
      (fun _ : College => S / (Fintype.card College : ℝ)) := by
  letI : IsProbabilityMeasure
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  apply pg23SupplyDemandLemma_of_primitives
  · exact equalCapacity_pos S hS.1
  · simpa [equalCapacity_sum (College := College) S] using hS.2

/-- Source Lemma 1 for the literal polyculture law and equal capacities. -/
theorem pg23PolycultureSupplyDemandLemma_of_primitives
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    pg23PolycultureSupplyDemandLemmaStatement valueLaw noiseLaw
      (fun _ : College => S / (Fintype.card College : ℝ)) := by
  letI : IsProbabilityMeasure
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23PolycultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  apply pg23SupplyDemandLemma_of_primitives
  · exact equalCapacity_pos S hS.1
  · simpa [equalCapacity_sum (College := College) S] using hS.2

/-- Source Lemma 2 for monoculture, including uniqueness among all raw clearing cutoffs. -/
theorem pg23MonocultureEqualCutoffsLemma_of_primitives
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    pg23MonocultureEqualCutoffsLemmaStatement valueLaw noiseLaw
      (fun _ : College => S / (Fintype.card College : ℝ)) := by
  unfold pg23MonocultureEqualCutoffsLemmaStatement pg23EqualCutoffsLemmaStatement
  rcases pg23MonocultureSourceMarketClearing_exists_constant
      valueLaw noiseLaw hlevel S hS
      (fun _ : College => S / (Fintype.card College : ℝ)) (fun _ => rfl) with
    ⟨P, hP, p, hp⟩
  refine ⟨P, hP, ?_, p, hp⟩
  intro Q hQ
  exact pg23MonocultureSourceMarketClearing_unique
    valueLaw noiseLaw hvalue hnoise hlevel S hS Q P hQ hP

/-- Source Lemma 2 for polyculture, including uniqueness among all raw clearing cutoffs. -/
theorem pg23PolycultureEqualCutoffsLemma_of_primitives
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    pg23PolycultureEqualCutoffsLemmaStatement valueLaw noiseLaw
      (fun _ : College => S / (Fintype.card College : ℝ)) := by
  unfold pg23PolycultureEqualCutoffsLemmaStatement pg23EqualCutoffsLemmaStatement
  rcases pg23PolycultureSourceMarketClearing_exists_constant
      valueLaw noiseLaw hlevel S hS
      (fun _ : College => S / (Fintype.card College : ℝ)) (fun _ => rfl) with
    ⟨P, hP, p, hp⟩
  refine ⟨P, hP, ?_, p, hp⟩
  intro Q hQ
  exact pg23PolycultureSourceMarketClearing_unique
    valueLaw noiseLaw hvalue hnoise hlevel S hS Q P hQ hP

end PG23MonocultureMatching
