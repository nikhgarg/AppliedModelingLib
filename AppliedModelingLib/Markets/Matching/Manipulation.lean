import AppliedModelingLib.Markets.Matching.DeferredAcceptance

/-!
# Comparative Matching Lemmas

This module contains finite matching lemmas for comparing an arbitrary
individually rational assignment with the proposer-optimal deferred-acceptance
outcome.
-/

namespace AppliedModelingLib
namespace Matching

variable {M W : Type*}

/-- Men whose value strictly increases from `baseline` to `comparison`. -/
noncomputable def strictlyImprovedMen [Fintype M] [DecidableEq M]
    (val_m : M → W → ℝ) (baseline comparison : Assignment M W) : Finset M :=
  Finset.univ.filter fun m =>
    valM val_m m (baseline.m_match m) < valM val_m m (comparison.m_match m)

/-- Women matched in `mu` to one of the listed men. -/
def matchedWomenOfMen [DecidableEq W]
    (mu : Assignment M W) (men : Finset M) : Finset W :=
  men.biUnion fun m => (mu.m_match m).toFinset

/-- Women whose value strictly increases from `baseline` to `comparison`. -/
noncomputable def strictlyImprovedWomen [Fintype W] [DecidableEq W]
    (val_w : W → M → ℝ) (baseline comparison : Assignment M W) : Finset W :=
  strictlyImprovedMen val_w baseline.swap comparison.swap

/-- Men matched in `mu` to one of the listed women. -/
def matchedMenOfWomen [DecidableEq M]
    (mu : Assignment M W) (women : Finset W) : Finset M :=
  matchedWomenOfMen mu.swap women

/-- Membership in `matchedWomenOfMen` is witnessed by a selected matched man. -/
theorem mem_matchedWomenOfMen_iff [DecidableEq W]
    (mu : Assignment M W) (men : Finset M) (w : W) :
    w ∈ matchedWomenOfMen mu men ↔
      ∃ m ∈ men, mu.m_match m = some w := by
  simp [matchedWomenOfMen]

/-- The image of a set of men under an assignment has no more members than the set. -/
theorem card_matchedWomenOfMen_le [DecidableEq W]
    (mu : Assignment M W) (men : Finset M) :
    (matchedWomenOfMen mu men).card ≤ men.card := by
  unfold matchedWomenOfMen
  calc
    (men.biUnion fun m => (mu.m_match m).toFinset).card ≤
        ∑ m ∈ men, (mu.m_match m).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ men, 1 := by
      gcongr with m hm
      cases mu.m_match m <;> simp
    _ = men.card := by simp

/--
If each selected man is matched, their matched-woman image has the same
cardinality as the selected men.
-/
theorem card_matchedWomenOfMen_eq_card_of_all_matched [DecidableEq M] [DecidableEq W]
    (mu : Assignment M W) (men : Finset M)
    (hmatched : ∀ m ∈ men, ∃ w, mu.m_match m = some w) :
    (matchedWomenOfMen mu men).card = men.card := by
  classical
  have hdisjoint : (men : Set M).PairwiseDisjoint fun m => (mu.m_match m).toFinset := by
    intro m hm m' hm' hne
    apply Finset.disjoint_left.2
    intro w hmw hmw'
    have hmm : mu.m_match m = some w := by
      simpa using hmw
    have hmm' : mu.m_match m' = some w := by
      simpa using hmw'
    have hwm : mu.w_match w = some m := (mu.consistent_m m w).1 hmm
    have hwm' : mu.w_match w = some m' := (mu.consistent_m m' w).1 hmm'
    exact hne (Option.some.inj (hwm.symm.trans hwm'))
  unfold matchedWomenOfMen
  rw [Finset.card_biUnion hdisjoint]
  calc
    (∑ x ∈ men, (mu.m_match x).toFinset.card) = ∑ _x ∈ men, 1 := by
      apply Finset.sum_congr rfl
      intro m hm
      rcases hmatched m hm with ⟨w, hmw⟩
      simp [hmw]
    _ = men.card := by simp

/--
If a set's matched-woman image has the same cardinality as the set, every
selected man is matched.
-/
theorem all_matched_of_card_matchedWomenOfMen_eq_card [DecidableEq M] [DecidableEq W]
    (mu : Assignment M W) (men : Finset M)
    (hcard : (matchedWomenOfMen mu men).card = men.card) :
    ∀ m ∈ men, ∃ w, mu.m_match m = some w := by
  intro m hm
  cases hmatch : mu.m_match m with
  | some w => exact ⟨w, rfl⟩
  | none =>
      have himage : matchedWomenOfMen mu men = matchedWomenOfMen mu (men.erase m) := by
        ext w
        simp only [mem_matchedWomenOfMen_iff]
        constructor
        · rintro ⟨m', hm', hm'w⟩
          by_cases hEq : m' = m
          · subst m'
            simp [hmatch] at hm'w
          · exact ⟨m', Finset.mem_erase.mpr ⟨hEq, hm'⟩, hm'w⟩
        · rintro ⟨m', hm', hm'w⟩
          exact ⟨m', (Finset.mem_erase.mp hm').2, hm'w⟩
      have hle : (matchedWomenOfMen mu (men.erase m)).card ≤ (men.erase m).card :=
        card_matchedWomenOfMen_le mu (men.erase m)
      have hlt : (men.erase m).card < men.card := Finset.card_erase_lt_of_mem hm
      have hle' : men.card ≤ (men.erase m).card := by
        calc
          men.card = (matchedWomenOfMen mu men).card := hcard.symm
          _ = (matchedWomenOfMen mu (men.erase m)).card := congrArg Finset.card himage
          _ ≤ (men.erase m).card := hle
      exact False.elim (by omega)

/--
If the matched-woman images of the strictly improved men differ, a woman is
matched to an improved man only in the comparison assignment.
-/
theorem exists_new_matchedWoman_of_matchedWomenOfMen_ne
    [Fintype M] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (baseline comparison : Assignment M W)
    (hbaselineIR : ∀ m, 0 ≤ valM val_m m (baseline.m_match m))
    (himage :
      matchedWomenOfMen comparison (strictlyImprovedMen val_m baseline comparison) ≠
      matchedWomenOfMen baseline (strictlyImprovedMen val_m baseline comparison)) :
    ∃ w,
      w ∈ matchedWomenOfMen comparison
        (strictlyImprovedMen val_m baseline comparison) ∧
      w ∉ matchedWomenOfMen baseline
        (strictlyImprovedMen val_m baseline comparison) := by
  classical
  let improved := strictlyImprovedMen val_m baseline comparison
  have hcomparisonMatched : ∀ m ∈ improved, ∃ w, comparison.m_match m = some w := by
    intro m hm
    have himproved : valM val_m m (baseline.m_match m) <
        valM val_m m (comparison.m_match m) := by
      simpa [improved, strictlyImprovedMen] using hm
    cases hcomparison : comparison.m_match m with
    | none =>
        have : valM val_m m (baseline.m_match m) < 0 := by
          simpa [valM, hcomparison] using himproved
        linarith [hbaselineIR m]
    | some w => exact ⟨w, rfl⟩
  let comparisonWomen := matchedWomenOfMen comparison improved
  let baselineWomen := matchedWomenOfMen baseline improved
  by_contra hnoNew
  push Not at hnoNew
  have hsubset : comparisonWomen ⊆ baselineWomen := by
    intro w hw
    exact hnoNew w hw
  have hcomparisonCard : comparisonWomen.card = improved.card := by
    exact card_matchedWomenOfMen_eq_card_of_all_matched comparison improved
      hcomparisonMatched
  have hbaselineCard : baselineWomen.card ≤ improved.card := by
    exact card_matchedWomenOfMen_le baseline improved
  have hbaselineLeComparison : baselineWomen.card ≤ comparisonWomen.card := by
    rw [hcomparisonCard]
    exact hbaselineCard
  have heq : comparisonWomen = baselineWomen :=
    Finset.eq_of_subset_of_card_le hsubset hbaselineLeComparison
  exact himage (by simpa [comparisonWomen, baselineWomen, improved] using heq)

/--
If a woman is matched under an individually rational assignment to a man who
strictly improves on the proposer-optimal outcome, but is not the
proposer-optimal partner of any strictly improved man, then the assignment has
a blocking pair.  This is the set-discrepancy branch of the standard
comparative matching argument.
-/
theorem exists_blocking_pair_of_strictly_improved_men_new_matched_woman
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozeroM : MenNoOutsideTie val_m)
    (hnozeroW : WomenNoOutsideTie val_w)
    (tau : Assignment M W)
    (htauIR : (∀ m, 0 ≤ valM val_m m (tau.m_match m)) ∧
      ∀ w, 0 ≤ valW val_w w (tau.w_match w))
    {witness : W}
    (hwitness : witness ∈ matchedWomenOfMen tau (strictlyImprovedMen val_m
      (deferredAcceptance val_m val_w) tau))
    (hnotWitness : witness ∉ matchedWomenOfMen (deferredAcceptance val_m val_w)
      (strictlyImprovedMen val_m (deferredAcceptance val_m val_w) tau)) :
    ∃ m w,
      m ∉ strictlyImprovedMen val_m (deferredAcceptance val_m val_w) tau ∧
      w ∈ matchedWomenOfMen tau
        (strictlyImprovedMen val_m (deferredAcceptance val_m val_w) tau) ∧
      valM val_m m (tau.m_match m) < val_m m w ∧
      valW val_w w (tau.w_match w) < val_w w m := by
  classical
  let da := deferredAcceptance val_m val_w
  let improved := strictlyImprovedMen val_m da tau
  rcases (mem_matchedWomenOfMen_iff tau improved witness).1 hwitness with
    ⟨m0, hm0Improved, hm0Tau⟩
  have hm0Improved' : valM val_m m0 (da.m_match m0) <
      valM val_m m0 (tau.m_match m0) := by
    simpa [improved, strictlyImprovedMen] using hm0Improved
  have hm0TauPos : 0 < val_m m0 witness := by
    have hnonneg : 0 ≤ val_m m0 witness := by
      simpa [valM, hm0Tau] using htauIR.1 m0
    have hdaNonneg : 0 ≤ valM val_m m0 (da.m_match m0) := by
      exact (da_produces_stable_matching val_m val_w).1 m0
    have hda_lt : valM val_m m0 (da.m_match m0) < val_m m0 witness := by
      simpa [valM, hm0Tau] using hm0Improved'
    linarith
  have hwitnessDa : ∃ m, da.w_match witness = some m := by
    cases hda : da.w_match witness with
    | some m => exact ⟨m, rfl⟩
    | none =>
        have hm0Blocks : valM val_m m0 (da.m_match m0) < val_m m0 witness := by
          simpa [valM, hm0Tau] using hm0Improved'
        have hTauW : tau.w_match witness = some m0 :=
          (tau.consistent_m m0 witness).1 hm0Tau
        have hwitnessPos : 0 < val_w witness m0 := by
          have hnonneg : 0 ≤ val_w witness m0 := by
            simpa [valW, hTauW] using htauIR.2 witness
          exact lt_of_le_of_ne hnonneg (Ne.symm (hnozeroW witness m0))
        have hwitnessBlocks : valW val_w witness (da.w_match witness) <
            val_w witness m0 := by
          simpa [valW, hda] using hwitnessPos
        exact False.elim ((da_produces_stable_matching val_m val_w).2.2
          m0 witness hm0Blocks hwitnessBlocks)
  rcases hwitnessDa with ⟨m, hdaWitness⟩
  have hmNotImproved : m ∉ improved := by
    intro hmImproved
    have hdaM : da.m_match m = some witness :=
      (da.consistent_m m witness).2 hdaWitness
    exact hnotWitness ((mem_matchedWomenOfMen_iff da improved witness).2
      ⟨m, hmImproved, hdaM⟩)
  have hwitnessPref : val_w witness m0 < val_w witness m := by
    have hnotBlocks : ¬ (valW val_w witness (da.w_match witness) <
      val_w witness m0) := by
      intro hblocks
      exact (da_produces_stable_matching val_m val_w).2.2 m0 witness
        (by simpa [valM, hm0Tau] using hm0Improved') hblocks
    have hle : val_w witness m0 ≤ val_w witness m := by
      simpa [valW, hdaWitness] using le_of_not_gt hnotBlocks
    have hTauW : tau.w_match witness = some m0 :=
      (tau.consistent_m m0 witness).1 hm0Tau
    have hm0Nonneg : 0 ≤ val_w witness m0 := by
      simpa [valW, hTauW] using htauIR.2 witness
    have hmNonneg : 0 ≤ val_w witness m := by
      simpa [da, valW, hdaWitness] using
        (da_produces_stable_matching val_m val_w).2.1 witness
    have hne : val_w witness m0 ≠ val_w witness m := by
      intro heq
      have hsame : m0 = m := hstrictW witness m0 m hm0Nonneg hmNonneg heq
      subst m
      have : valM val_m m0 (da.m_match m0) =
          valM val_m m0 (tau.m_match m0) := by
        have hdaM : da.m_match m0 = some witness :=
          (da.consistent_m m0 witness).2 hdaWitness
        simp [valM, hdaM, hm0Tau]
      exact (ne_of_lt hm0Improved') this
    exact lt_of_le_of_ne hle hne
  have hmPref : valM val_m m (tau.m_match m) < val_m m witness := by
    have hnotImproved' : ¬ (valM val_m m (da.m_match m) <
        valM val_m m (tau.m_match m)) := by
      simpa [improved, strictlyImprovedMen] using hmNotImproved
    have hdaM : da.m_match m = some witness :=
      (da.consistent_m m witness).2 hdaWitness
    have hle : valM val_m m (tau.m_match m) ≤ val_m m witness := by
      simpa [valM, hdaM] using le_of_not_gt hnotImproved'
    have htauNonneg : 0 ≤ valM val_m m (tau.m_match m) := htauIR.1 m
    have hdaNonneg : 0 ≤ val_m m witness := by
      simpa [da, valM, hdaM] using
        (da_produces_stable_matching val_m val_w).1 m
    have hne : valM val_m m (tau.m_match m) ≠ val_m m witness := by
      intro heq
      cases htau : tau.m_match m with
      | none =>
          have hzero : val_m m witness = 0 := by
            exact (by simpa [valM, htau] using heq.symm)
          exact hnozeroM m witness hzero
      | some wTau =>
          have hsame : wTau = witness := hstrictM m wTau witness
            (by simpa [valM, htau] using htauNonneg) hdaNonneg
            (by simpa [valM, htau] using heq)
          have hTauM : tau.m_match m = some witness := by
            simpa [htau, hsame]
          have hTauW : tau.w_match witness = some m :=
            (tau.consistent_m m witness).1 hTauM
          have hTauW0 : tau.w_match witness = some m0 :=
            (tau.consistent_m m0 witness).1 hm0Tau
          have hm0eqm : m0 = m := Option.some.inj (hTauW0.symm.trans hTauW)
          subst m
          exact (ne_of_lt hm0Improved')
            (by simpa [valM, hm0Tau, hdaM] using heq)
    exact lt_of_le_of_ne hle hne
  refine ⟨m, witness, ?_, ?_, hmPref, ?_⟩
  · simpa [improved] using hmNotImproved
  · simpa [improved] using hwitness
  · have hTauW : tau.w_match witness = some m0 :=
      (tau.consistent_m m0 witness).1 hm0Tau
    simpa [valW, hTauW] using hwitnessPref

/--
When the matched-woman images of the strictly improved men differ, the
comparison assignment has a blocking pair with a man who did not improve.
-/
theorem exists_blocking_pair_of_strictly_improved_men_of_matchedWomenOfMen_ne
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozeroM : MenNoOutsideTie val_m)
    (hnozeroW : WomenNoOutsideTie val_w)
    (tau : Assignment M W)
    (htauIR : (∀ m, 0 ≤ valM val_m m (tau.m_match m)) ∧
      ∀ w, 0 ≤ valW val_w w (tau.w_match w))
    (himage :
      matchedWomenOfMen tau (strictlyImprovedMen val_m
        (deferredAcceptance val_m val_w) tau) ≠
      matchedWomenOfMen (deferredAcceptance val_m val_w)
        (strictlyImprovedMen val_m (deferredAcceptance val_m val_w) tau)) :
    ∃ m w,
      m ∉ strictlyImprovedMen val_m (deferredAcceptance val_m val_w) tau ∧
      w ∈ matchedWomenOfMen tau
        (strictlyImprovedMen val_m (deferredAcceptance val_m val_w) tau) ∧
      valM val_m m (tau.m_match m) < val_m m w ∧
      valW val_w w (tau.w_match w) < val_w w m := by
  obtain ⟨witness, hwitness, hnotWitness⟩ :=
    exists_new_matchedWoman_of_matchedWomenOfMen_ne val_m
      (deferredAcceptance val_m val_w) tau
      (da_produces_stable_matching val_m val_w).1 himage
  exact exists_blocking_pair_of_strictly_improved_men_new_matched_woman
    val_m val_w hstrictM hstrictW hnozeroM hnozeroW tau htauIR
    hwitness hnotWitness

/--
The women-side form of
`exists_blocking_pair_of_strictly_improved_men_of_matchedWomenOfMen_ne`.
-/
theorem exists_blocking_pair_of_strictly_improved_women_of_matchedMenOfWomen_ne
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozeroM : MenNoOutsideTie val_m)
    (hnozeroW : WomenNoOutsideTie val_w)
    (tau : Assignment M W)
    (htauIR : (∀ m, 0 ≤ valM val_m m (tau.m_match m)) ∧
      ∀ w, 0 ≤ valW val_w w (tau.w_match w))
    (himage :
      matchedMenOfWomen tau (strictlyImprovedWomen val_w
        (womenDeferredAcceptance val_m val_w) tau) ≠
      matchedMenOfWomen (womenDeferredAcceptance val_m val_w)
        (strictlyImprovedWomen val_w (womenDeferredAcceptance val_m val_w) tau)) :
    ∃ m w,
      w ∉ strictlyImprovedWomen val_w (womenDeferredAcceptance val_m val_w) tau ∧
      m ∈ matchedMenOfWomen tau
        (strictlyImprovedWomen val_w (womenDeferredAcceptance val_m val_w) tau) ∧
      valM val_m m (tau.m_match m) < val_m m w ∧
      valW val_w w (tau.w_match w) < val_w w m := by
  have htauIRSwap : (∀ w, 0 ≤ valM val_w w (tau.swap.m_match w)) ∧
      ∀ m, 0 ≤ valW val_m m (tau.swap.w_match m) := by
    constructor
    · intro w
      simpa [Assignment.swap, valM, valW] using htauIR.2 w
    · intro m
      simpa [Assignment.swap, valM, valW] using htauIR.1 m
  have himageSwap :
      matchedWomenOfMen tau.swap (strictlyImprovedMen val_w
        (deferredAcceptance val_w val_m) tau.swap) ≠
      matchedWomenOfMen (deferredAcceptance val_w val_m)
        (strictlyImprovedMen val_w (deferredAcceptance val_w val_m) tau.swap) := by
    simpa [matchedMenOfWomen, strictlyImprovedWomen, womenDeferredAcceptance,
      Assignment.swap_swap] using himage
  obtain ⟨w, m, hw, hm, hwPref, hmPref⟩ :=
    exists_blocking_pair_of_strictly_improved_men_of_matchedWomenOfMen_ne
      val_w val_m hstrictW hstrictM hnozeroW hnozeroM tau.swap htauIRSwap himageSwap
  refine ⟨m, w, ?_, ?_, ?_, ?_⟩
  · simpa [strictlyImprovedWomen, womenDeferredAcceptance, Assignment.swap_swap] using hw
  · simpa [matchedMenOfWomen, strictlyImprovedWomen, womenDeferredAcceptance,
      Assignment.swap_swap] using hm
  · simpa [Assignment.swap, valM, valW] using hmPref
  · simpa [Assignment.swap, valM, valW] using hwPref

/--
If a man strictly prefers a woman to his deferred-acceptance partner, then he
has exhausted that woman's proposal opportunity by the terminal state.
-/
theorem not_mem_deferredAcceptanceState_proposals_of_lt_final_match
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {m : M} {w : W}
    (hbetter : valM val_m m ((deferredAcceptance val_m val_w).m_match m) < val_m m w) :
    w ∉ (deferredAcceptanceState val_m val_w).m_proposals m := by
  let s := deferredAcceptanceState val_m val_w
  have hinv : DAInvariants val_m val_w s := by
    exact deferredAcceptanceState_satisfies_invariants_closed val_m val_w
  have hterm : ¬ ∃ m, IsActiveMan val_m s m := by
    exact deferredAcceptanceState_terminated val_m val_w
  have hstable : IsStable val_m val_w (deferredAcceptance val_m val_w) :=
    da_produces_stable_matching val_m val_w
  intro hmem
  cases hmatch : s.m_match m with
  | none =>
      have hvalue : valM val_m m ((deferredAcceptance val_m val_w).m_match m) = 0 := by
        simpa [deferredAcceptance, s, hmatch, valM]
      have hpos : 0 < val_m m w := by linarith
      exact hterm ⟨m, hmatch, w, hmem, le_of_lt hpos⟩
  | some current =>
      have hcurrentNotMem : current ∉ s.m_proposals m := by
        exact hinv.2.2.1 m current hmatch
      have hnonneg : 0 ≤ val_m m w := by
        have hfinal : 0 ≤ valM val_m m ((deferredAcceptance val_m val_w).m_match m) :=
          hstable.1 m
        have : 0 < val_m m w := by linarith
        exact le_of_lt this
      have hle : val_m m w ≤ val_m m current := by
        exact hinv.2.2.2.2 m current w hcurrentNotMem hmem hnonneg
      have hvalue : valM val_m m ((deferredAcceptance val_m val_w).m_match m) =
          val_m m current := by
        simpa [deferredAcceptance, s, hmatch, valM]
      linarith

/--
Any woman strictly above a man's final deferred-acceptance partner is proposed
to at a concrete, pre-terminal step.
-/
theorem exists_deferredAcceptance_proposal_removal_before_of_lt_final_match
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {m : M} {w : W}
    (hbetter : valM val_m m ((deferredAcceptance val_m val_w).m_match m) < val_m m w) :
    ∃ t, t < Fintype.card M * Fintype.card W ∧
      w ∈ (daStateAfterSteps val_m val_w t).m_proposals m ∧
      w ∉ (daStateAfterSteps val_m val_w (t + 1)).m_proposals m := by
  have hnot : w ∉ (deferredAcceptanceState val_m val_w).m_proposals m :=
    not_mem_deferredAcceptanceState_proposals_of_lt_final_match val_m val_w hbetter
  rw [deferredAcceptanceState_eq_daStateAfterSteps] at hnot
  exact exists_proposal_removal_step_before_of_not_mem_daStateAfterSteps
    val_m val_w hnot

/-- At most one proposer-woman pair is removed by a single DA step. -/
theorem proposal_removal_unique_at_daStep
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (s : DAState M W)
    {m₁ m₂ : M} {w₁ w₂ : W}
    (hmem₁ : w₁ ∈ s.m_proposals m₁)
    (hnot₁ : w₁ ∉ (daStep val_m val_w s).m_proposals m₁)
    (hmem₂ : w₂ ∈ s.m_proposals m₂)
    (hnot₂ : w₂ ∉ (daStep val_m val_w s).m_proposals m₂) :
    m₁ = m₂ ∧ w₁ = w₂ := by
  have hactive : ∃ m, IsActiveMan val_m s m := by
    exact ⟨m₁, (proposal_removed_at_daStep val_m val_w s hmem₁ hnot₁).1⟩
  let chosenM := daStepChosenMan val_m s hactive
  let chosenW := daStepChosenWoman val_m s hactive
  have hprops : (daStep val_m val_w s).m_proposals =
      removeProposal s chosenM chosenW := by
    simpa [chosenM, chosenW] using
      daStep_m_proposals_eq_removeProposal_of_active val_m val_w s hactive
  have hchosen₁ : m₁ = chosenM ∧ w₁ = chosenW := by
    have hnot : w₁ ∉ removeProposal s chosenM chosenW m₁ := by
      simpa [hprops] using hnot₁
    rcases not_mem_of_not_mem_removeProposal s hnot with hnotOld | hchosen
    · exact False.elim (hnotOld hmem₁)
    · exact hchosen
  have hchosen₂ : m₂ = chosenM ∧ w₂ = chosenW := by
    have hnot : w₂ ∉ removeProposal s chosenM chosenW m₂ := by
      simpa [hprops] using hnot₂
    rcases not_mem_of_not_mem_removeProposal s hnot with hnotOld | hchosen
    · exact False.elim (hnotOld hmem₂)
    · exact hchosen
  exact ⟨hchosen₁.1.trans hchosen₂.1.symm, hchosen₁.2.trans hchosen₂.2.symm⟩

/--
The pre-terminal steps at which a selected man proposes to a selected woman.
-/
noncomputable def proposalRemovalTimes
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (men : Finset M) (women : Finset W) : Finset ℕ :=
  (Finset.range (Fintype.card M * Fintype.card W)).filter fun t =>
    ∃ m ∈ men, ∃ w ∈ women,
      w ∈ (daStateAfterSteps val_m val_w t).m_proposals m ∧
      w ∉ (daStateAfterSteps val_m val_w (t + 1)).m_proposals m

/-- Membership in `proposalRemovalTimes` expands to the corresponding DA event. -/
theorem mem_proposalRemovalTimes_iff
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (men : Finset M) (women : Finset W) (t : ℕ) :
    t ∈ proposalRemovalTimes val_m val_w men women ↔
      t < Fintype.card M * Fintype.card W ∧
      ∃ m ∈ men, ∃ w ∈ women,
        w ∈ (daStateAfterSteps val_m val_w t).m_proposals m ∧
        w ∉ (daStateAfterSteps val_m val_w (t + 1)).m_proposals m := by
  simp [proposalRemovalTimes]

/-- A nonempty finite family of selected DA proposal events has a latest step. -/
theorem exists_maximal_proposalRemovalTime
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (men : Finset M) (women : Finset W)
    (hne : (proposalRemovalTimes val_m val_w men women).Nonempty) :
    ∃ t,
      t ∈ proposalRemovalTimes val_m val_w men women ∧
      ∀ t', t' ∈ proposalRemovalTimes val_m val_w men women → t' ≤ t := by
  let times := proposalRemovalTimes val_m val_w men women
  refine ⟨times.max' (by simpa [times] using hne), ?_, ?_⟩
  · exact Finset.max'_mem times (by simpa [times] using hne)
  · intro t' ht'
    exact Finset.le_max' times t' ht'

/-- A selected terminal DA match supplies a selected proposal-removal event. -/
theorem proposalRemovalTimes_nonempty_of_final_match
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (men : Finset M) (women : Finset W) {m : M} {w : W}
    (hm : m ∈ men) (hw : w ∈ women)
    (hfinal : (deferredAcceptance val_m val_w).m_match m = some w) :
    (proposalRemovalTimes val_m val_w men women).Nonempty := by
  have hnotFinal : w ∉ (deferredAcceptanceState val_m val_w).m_proposals m := by
    have hinv := deferredAcceptanceState_satisfies_invariants_closed val_m val_w
    exact hinv.2.2.1 m w (by simpa [deferredAcceptance] using hfinal)
  rw [deferredAcceptanceState_eq_daStateAfterSteps] at hnotFinal
  obtain ⟨t, ht, hmem, hnot⟩ :=
    exists_proposal_removal_step_before_of_not_mem_daStateAfterSteps val_m val_w hnotFinal
  refine ⟨t, (mem_proposalRemovalTimes_iff val_m val_w men women t).2 ?_⟩
  exact ⟨ht, m, hm, w, hw, hmem, hnot⟩

/--
After a woman's prior rejection of an acceptable man, a later distinct current
holder is strictly preferred to that man.
-/
theorem woman_prefers_current_of_prior_proposal_removal
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {earlier later : ℕ} {m0 m : M} {w : W}
    (hle : earlier + 1 ≤ later)
    (hnot : w ∉ (daStateAfterSteps val_m val_w (earlier + 1)).m_proposals m0)
    (hcurrent : (daStateAfterSteps val_m val_w later).w_match w = some m)
    (hne : m0 ≠ m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hpositive : 0 < val_w w m0) :
    val_w w m0 < val_w w m := by
  have hinv := daStateAfterSteps_satisfies_invariants val_m val_w later
  have hnotLater : w ∉ (daStateAfterSteps val_m val_w later).m_proposals m0 := by
    exact not_mem_daStateAfterSteps_of_not_mem_of_le val_m val_w hle hnot
  have hnotMatch : (daStateAfterSteps val_m val_w later).m_match m0 ≠ some w := by
    intro hm0
    have hw0 : (daStateAfterSteps val_m val_w later).w_match w = some m0 :=
      ((daStateAfterSteps val_m val_w later).consistent m0 w).1 hm0
    exact hne (Option.some.inj (hw0.symm.trans hcurrent))
  obtain hneg | ⟨m', hm', hle'⟩ :=
    hinv.2.2.2.1 w m0 hnotLater hnotMatch
  · linarith
  · have hmEq : m' = m := Option.some.inj (hm'.symm.trans hcurrent)
    subst m'
    have hcurrentNonneg : 0 ≤ val_w w m := by
      exact hinv.2.1 w m hcurrent
    have hneq : val_w w m0 ≠ val_w w m := by
      intro heq
      exact hne (hstrictW w m0 m hpositive.le hcurrentNonneg heq)
    exact lt_of_le_of_ne hle' hneq

/--
If a man is active at a pre-terminal state and has a terminal partner, the
proposal to that terminal partner occurs no earlier than the active state.
-/
theorem exists_proposal_removal_time_ge_of_active_of_final_match
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {t : ℕ} {m : M} {w : W}
    (ht : t < Fintype.card M * Fintype.card W)
    (hactive : IsActiveMan val_m (daStateAfterSteps val_m val_w t) m)
    (hfinal : (deferredAcceptance val_m val_w).m_match m = some w) :
    ∃ t', t ≤ t' ∧ t' < Fintype.card M * Fintype.card W ∧
      w ∈ (daStateAfterSteps val_m val_w t').m_proposals m ∧
      w ∉ (daStateAfterSteps val_m val_w (t' + 1)).m_proposals m := by
  have hnotFinal : w ∉ (deferredAcceptanceState val_m val_w).m_proposals m := by
    have hinv := deferredAcceptanceState_satisfies_invariants_closed val_m val_w
    exact hinv.2.2.1 m w (by simpa [deferredAcceptance] using hfinal)
  rw [deferredAcceptanceState_eq_daStateAfterSteps] at hnotFinal
  obtain ⟨t', ht', hmem, hnot⟩ :=
    exists_proposal_removal_step_before_of_not_mem_daStateAfterSteps val_m val_w hnotFinal
  refine ⟨t', ?_, ht', hmem, hnot⟩
  by_contra hlt
  have hle : t' + 1 ≤ t := Nat.succ_le_iff.mpr (Nat.lt_of_not_ge hlt)
  have hnotAtT : w ∉ (daStateAfterSteps val_m val_w t).m_proposals m :=
    not_mem_daStateAfterSteps_of_not_mem_of_le val_m val_w hle hnot
  have hneAtT : (daStateAfterSteps val_m val_w t).m_match m ≠ some w := by
    simpa [hactive.1]
  have hnotMatch : (deferredAcceptanceState val_m val_w).m_match m ≠ some w :=
    m_match_ne_deferredAcceptanceState_of_not_mem_after_steps
      val_m val_w (Nat.le_of_lt ht) hnotAtT hneAtT
  exact hnotMatch (by simpa [deferredAcceptance] using hfinal)

/-- A proposal to a man's eventual deferred-acceptance partner is accepted. -/
theorem proposal_to_final_match_is_accepted
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {t : ℕ} {m : M} {w : W}
    (ht : t < Fintype.card M * Fintype.card W)
    (hmem : w ∈ (daStateAfterSteps val_m val_w t).m_proposals m)
    (hnot : w ∉ (daStateAfterSteps val_m val_w (t + 1)).m_proposals m)
    (hfinal : (deferredAcceptance val_m val_w).m_match m = some w) :
    (daStateAfterSteps val_m val_w (t + 1)).w_match w = some m := by
  let s := daStateAfterSteps val_m val_w t
  have hactiveM : IsActiveMan val_m s m := by
    exact (proposal_removed_at_daStateAfterSteps_succ val_m val_w t hmem hnot).1
  have hactive : ∃ m, IsActiveMan val_m s m := ⟨m, hactiveM⟩
  let chosenM := daStepChosenMan val_m s hactive
  let chosenW := daStepChosenWoman val_m s hactive
  have hprops : (daStep val_m val_w s).m_proposals =
      removeProposal s chosenM chosenW := by
    simpa [chosenM, chosenW] using
      daStep_m_proposals_eq_removeProposal_of_active val_m val_w s hactive
  have hchosen : m = chosenM ∧ w = chosenW := by
    have hnot' : w ∉ removeProposal s chosenM chosenW m := by
      simpa [s, hprops, daStateAfterSteps_succ] using hnot
    rcases not_mem_of_not_mem_removeProposal s hnot' with hnotOld | hchosen
    · exact False.elim (hnotOld (by simpa [s] using hmem))
    · exact hchosen
  by_cases hacc : daStepChosenAccepts val_m val_w s hactive
  · have hafter : (daStep val_m val_w s).w_match chosenW = some chosenM :=
      daStep_w_match_chosen_of_accepts val_m val_w s hactive hacc
    simpa [s, hchosen.1, hchosen.2, daStateAfterSteps_succ] using hafter
  · have hafterM : (daStep val_m val_w s).m_match m = none := by
      have hself := daStep_m_match_eq_self_of_not_accepts val_m val_w s hactive hacc
      simpa [s, hactiveM.1] using congrFun hself m
    have hnotAfter : w ∉ (daStateAfterSteps val_m val_w (t + 1)).m_proposals m := hnot
    have hnoneAfter : (daStateAfterSteps val_m val_w (t + 1)).m_match m ≠ some w := by
      dsimp [s] at hafterM
      rw [daStateAfterSteps_succ, hafterM]
      simp
    have hnotFinal : (deferredAcceptanceState val_m val_w).m_match m ≠ some w :=
      m_match_ne_deferredAcceptanceState_of_not_mem_after_steps
        val_m val_w (Nat.succ_le_of_lt ht) hnotAfter hnoneAfter
    exact False.elim (hnotFinal (by simpa [deferredAcceptance] using hfinal))

/--
When a proposal to a man's terminal partner displaces a distinct current
holder, that holder becomes unmatched in the next DA state.
-/
theorem prior_holder_unmatched_after_proposal_to_final_match
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    {t : ℕ} {m holder : M} {w : W}
    (ht : t < Fintype.card M * Fintype.card W)
    (hmem : w ∈ (daStateAfterSteps val_m val_w t).m_proposals m)
    (hnot : w ∉ (daStateAfterSteps val_m val_w (t + 1)).m_proposals m)
    (hfinal : (deferredAcceptance val_m val_w).m_match m = some w)
    (hbefore : (daStateAfterSteps val_m val_w t).w_match w = some holder)
    (hne : holder ≠ m) :
    (daStateAfterSteps val_m val_w (t + 1)).m_match holder = none := by
  let s := daStateAfterSteps val_m val_w t
  have hactiveM : IsActiveMan val_m s m := by
    exact (proposal_removed_at_daStateAfterSteps_succ val_m val_w t hmem hnot).1
  have hactive : ∃ m, IsActiveMan val_m s m := ⟨m, hactiveM⟩
  let chosenM := daStepChosenMan val_m s hactive
  let chosenW := daStepChosenWoman val_m s hactive
  have hprops : (daStep val_m val_w s).m_proposals =
      removeProposal s chosenM chosenW := by
    simpa [chosenM, chosenW] using
      daStep_m_proposals_eq_removeProposal_of_active val_m val_w s hactive
  have hchosen : m = chosenM ∧ w = chosenW := by
    have hnot' : w ∉ removeProposal s chosenM chosenW m := by
      simpa [s, hprops, daStateAfterSteps_succ] using hnot
    rcases not_mem_of_not_mem_removeProposal s hnot' with hnotOld | hchosen
    · exact False.elim (hnotOld (by simpa [s] using hmem))
    · exact hchosen
  have hacc : daStepChosenAccepts val_m val_w s hactive := by
    by_contra hacc
    have hafterM : (daStep val_m val_w s).m_match m = none := by
      have hself := daStep_m_match_eq_self_of_not_accepts val_m val_w s hactive hacc
      simpa [s, hactiveM.1] using congrFun hself m
    have hnoneAfter : (daStateAfterSteps val_m val_w (t + 1)).m_match m ≠ some w := by
      dsimp [s] at hafterM
      rw [daStateAfterSteps_succ, hafterM]
      simp
    have hnotFinal : (deferredAcceptanceState val_m val_w).m_match m ≠ some w :=
      m_match_ne_deferredAcceptanceState_of_not_mem_after_steps
        val_m val_w (Nat.succ_le_of_lt ht) hnot hnoneAfter
    exact hnotFinal (by simpa [deferredAcceptance] using hfinal)
  have hupdate := daStep_m_match_eq_update_of_accepts val_m val_w s hactive hacc
  have hholderNe : holder ≠ chosenM := by
    intro heq
    exact hne (heq.trans hchosen.1.symm)
  have hbeforeS : s.w_match chosenW = some holder := by
    have hbefore' : s.w_match w = some holder := by
      simpa [s] using hbefore
    rw [← hchosen.2]
    exact hbefore'
  have hresult : (daStep val_m val_w s).m_match holder = none := by
    rw [hupdate]
    change (if holder = chosenM then some chosenW else
      if s.w_match chosenW = some holder then none else s.m_match holder) = none
    simp [hholderNe, hbeforeS]
  simpa [s, daStateAfterSteps_succ] using hresult

/--
An individually rational assignment that strictly improves a nonempty set of
men over their proposer-optimal partners has a blocking pair whose man is not
strictly improved and whose woman is matched to a strictly improved man.
-/
theorem exists_blocking_pair_of_nonempty_strictly_improved_men
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozeroM : MenNoOutsideTie val_m)
    (hnozeroW : WomenNoOutsideTie val_w)
    (tau : Assignment M W)
    (htauIR : (∀ m, 0 ≤ valM val_m m (tau.m_match m)) ∧
      ∀ w, 0 ≤ valW val_w w (tau.w_match w))
    (hnonempty : (strictlyImprovedMen val_m (deferredAcceptance val_m val_w) tau).Nonempty) :
    ∃ m w,
      m ∉ strictlyImprovedMen val_m (deferredAcceptance val_m val_w) tau ∧
      w ∈ matchedWomenOfMen tau
        (strictlyImprovedMen val_m (deferredAcceptance val_m val_w) tau) ∧
      valM val_m m (tau.m_match m) < val_m m w ∧
      valW val_w w (tau.w_match w) < val_w w m := by
  let da := deferredAcceptance val_m val_w
  let improved := strictlyImprovedMen val_m da tau
  let tauWomen := matchedWomenOfMen tau improved
  let daWomen := matchedWomenOfMen da improved
  by_cases himage : tauWomen = daWomen
  · have hTauMatched : ∀ m ∈ improved, ∃ w, tau.m_match m = some w := by
      intro m hm
      have hlt : valM val_m m (da.m_match m) < valM val_m m (tau.m_match m) := by
        simpa [improved, strictlyImprovedMen] using hm
      cases ht : tau.m_match m with
      | none =>
          have hIR : 0 ≤ valM val_m m (da.m_match m) := by
            exact (da_produces_stable_matching val_m val_w).1 m
          have hlt' : valM val_m m (da.m_match m) < 0 := by
            simpa [valM, ht] using hlt
          linarith
      | some w => exact ⟨w, rfl⟩
    have hTauCard : tauWomen.card = improved.card := by
      exact card_matchedWomenOfMen_eq_card_of_all_matched tau improved hTauMatched
    have hDaCard : daWomen.card = improved.card := by simpa [himage] using hTauCard
    have hDaMatched : ∀ m ∈ improved, ∃ w, da.m_match m = some w := by
      exact all_matched_of_card_matchedWomenOfMen_eq_card da improved hDaCard
    have htimeNonempty : (proposalRemovalTimes val_m val_w improved daWomen).Nonempty := by
      rcases hnonempty with ⟨m, hm⟩
      rcases hDaMatched m (by simpa [improved] using hm) with ⟨w, hfinal⟩
      apply proposalRemovalTimes_nonempty_of_final_match val_m val_w improved daWomen
      · simpa [improved] using hm
      · exact (mem_matchedWomenOfMen_iff da improved w).2
          ⟨m, by simpa [improved] using hm, hfinal⟩
      · simpa [da] using hfinal
    obtain ⟨t, ht, htmax⟩ :=
      exists_maximal_proposalRemovalTime val_m val_w improved daWomen htimeNonempty
    rcases (mem_proposalRemovalTimes_iff val_m val_w improved daWomen t).1 ht with
      ⟨htlt, a, ha, w, hw, hmem, hnot⟩
    have hactiveA : IsActiveMan val_m (daStateAfterSteps val_m val_w t) a := by
      exact (proposal_removed_at_daStateAfterSteps_succ val_m val_w t hmem hnot).1
    rcases hDaMatched a ha with ⟨wFinal, hfinalA⟩
    obtain ⟨tFinal, htFinalGe, htFinalLt, hmemFinal, hnotFinal⟩ :=
      exists_proposal_removal_time_ge_of_active_of_final_match
        val_m val_w htlt hactiveA (by simpa [da] using hfinalA)
    have htFinalEvent : tFinal ∈ proposalRemovalTimes val_m val_w improved daWomen := by
      apply (mem_proposalRemovalTimes_iff val_m val_w improved daWomen tFinal).2
      refine ⟨htFinalLt, a, ha, wFinal, ?_, hmemFinal, hnotFinal⟩
      exact (mem_matchedWomenOfMen_iff da improved wFinal).2 ⟨a, ha, hfinalA⟩
    have htFinalLe : tFinal ≤ t := htmax tFinal htFinalEvent
    have htFinalEq : tFinal = t := le_antisymm htFinalLe htFinalGe
    subst tFinal
    have hpair := proposal_removal_unique_at_daStep val_m val_w
      (daStateAfterSteps val_m val_w t) hmem
      (by simpa [daStateAfterSteps_succ] using hnot) hmemFinal
      (by simpa [daStateAfterSteps_succ] using hnotFinal)
    have hwFinal : wFinal = w := hpair.2.symm
    have hfinalAw : da.m_match a = some w := by simpa [hwFinal] using hfinalA
    have hwTau : w ∈ tauWomen := by simpa [himage] using hw
    rcases (mem_matchedWomenOfMen_iff tau improved w).1 hwTau with
      ⟨m0, hm0, htauM0⟩
    have hm0Improved : valM val_m m0 (da.m_match m0) <
        valM val_m m0 (tau.m_match m0) := by
      simpa [improved, strictlyImprovedMen] using hm0
    have hm0Better : valM val_m m0 (da.m_match m0) < val_m m0 w := by
      simpa [valM, htauM0] using hm0Improved
    obtain ⟨t0, ht0Lt, hmem0, hnot0⟩ :=
      exists_deferredAcceptance_proposal_removal_before_of_lt_final_match
        val_m val_w (by simpa [da] using hm0Better)
    have ht0Event : t0 ∈ proposalRemovalTimes val_m val_w improved daWomen := by
      apply (mem_proposalRemovalTimes_iff val_m val_w improved daWomen t0).2
      exact ⟨ht0Lt, m0, hm0, w, hw, hmem0, hnot0⟩
    have ht0Le : t0 ≤ t := htmax t0 ht0Event
    have ht0Strict : t0 < t := by
      apply lt_of_le_of_ne ht0Le
      intro ht0Eq
      subst t0
      have hpair0 := proposal_removal_unique_at_daStep val_m val_w
        (daStateAfterSteps val_m val_w t) hmem0
        (by simpa [daStateAfterSteps_succ] using hnot0) hmem
        (by simpa [daStateAfterSteps_succ] using hnot)
      have hm0Eq : m0 = a := hpair0.1
      subst m0
      have : valM val_m a (da.m_match a) =
          valM val_m a (tau.m_match a) := by
        simp [valM, hfinalAw, htauM0]
      exact (ne_of_lt hm0Improved) this
    have hafterA : (daStateAfterSteps val_m val_w (t + 1)).w_match w = some a :=
      proposal_to_final_match_is_accepted val_m val_w htlt hmem hnot
        (by simpa [da] using hfinalAw)
    have htauW : tau.w_match w = some m0 :=
      (tau.consistent_m m0 w).1 htauM0
    have hm0Nonneg : 0 ≤ val_w w m0 := by
      simpa [valW, htauW] using htauIR.2 w
    have hm0Pos : 0 < val_w w m0 :=
      lt_of_le_of_ne hm0Nonneg (Ne.symm (hnozeroW w m0))
    have ht0SuccLe : t0 + 1 ≤ t := Nat.succ_le_iff.mpr ht0Strict
    have hnot0AtT : w ∉ (daStateAfterSteps val_m val_w t).m_proposals m0 :=
      not_mem_daStateAfterSteps_of_not_mem_of_le val_m val_w ht0SuccLe hnot0
    have hcurrentExists : ∃ current,
        (daStateAfterSteps val_m val_w t).w_match w = some current := by
      cases hcurrent : (daStateAfterSteps val_m val_w t).w_match w with
      | some current => exact ⟨current, rfl⟩
      | none =>
          have hnotMatch : (daStateAfterSteps val_m val_w t).m_match m0 ≠ some w := by
            intro hm0Match
            have := ((daStateAfterSteps val_m val_w t).consistent m0 w).1 hm0Match
            simp [hcurrent] at this
          have hinv := daStateAfterSteps_satisfies_invariants val_m val_w t
          obtain hneg | ⟨m', hm', _⟩ := hinv.2.2.2.1 w m0 hnot0AtT hnotMatch
          · linarith
          · simp [hcurrent] at hm'
    rcases hcurrentExists with ⟨current, hcurrent⟩
    have hcurrentNeA : current ≠ a := by
      intro heq
      subst current
      have hmatchA : (daStateAfterSteps val_m val_w t).m_match a = some w :=
        ((daStateAfterSteps val_m val_w t).consistent a w).2 hcurrent
      have hnoneA := (proposal_removed_at_daStateAfterSteps_succ val_m val_w t hmem hnot).1.1
      rw [hmatchA] at hnoneA
      simp at hnoneA
    have hcurrentAfterNone :
        (daStateAfterSteps val_m val_w (t + 1)).m_match current = none :=
      prior_holder_unmatched_after_proposal_to_final_match
        val_m val_w htlt hmem hnot (by simpa [da] using hfinalAw)
        hcurrent hcurrentNeA
    have hcurrentNotImproved : current ∉ improved := by
      intro hcurrentImproved
      rcases hDaMatched current hcurrentImproved with ⟨wCurrentFinal, hcurrentFinal⟩
      have hcurrentFinalNonneg : 0 ≤ val_m current wCurrentFinal := by
        have hstable := da_produces_stable_matching val_m val_w
        simpa [da, valM, hcurrentFinal] using hstable.1 current
      have hcurrentFinalPos : 0 < val_m current wCurrentFinal :=
        lt_of_le_of_ne hcurrentFinalNonneg
          (Ne.symm (hnozeroM current wCurrentFinal))
      have hcurrentFinalRemaining :
          wCurrentFinal ∈ (daStateAfterSteps val_m val_w (t + 1)).m_proposals current := by
        by_contra hnotRemaining
        have hnone : (daStateAfterSteps val_m val_w (t + 1)).m_match current ≠
            some wCurrentFinal := by
          rw [hcurrentAfterNone]
          simp
        have hnotFinal : (deferredAcceptanceState val_m val_w).m_match current ≠
            some wCurrentFinal :=
          m_match_ne_deferredAcceptanceState_of_not_mem_after_steps
            val_m val_w (Nat.succ_le_of_lt htlt) hnotRemaining hnone
        exact hnotFinal (by simpa [da] using hcurrentFinal)
      have hcurrentActiveAfter : IsActiveMan val_m
          (daStateAfterSteps val_m val_w (t + 1)) current :=
        ⟨hcurrentAfterNone, wCurrentFinal, hcurrentFinalRemaining,
          le_of_lt hcurrentFinalPos⟩
      by_cases hafterLt : t + 1 < Fintype.card M * Fintype.card W
      · obtain ⟨tCurrent, htCurrentGe, htCurrentLt, hmemCurrent, hnotCurrent⟩ :=
          exists_proposal_removal_time_ge_of_active_of_final_match val_m val_w
            hafterLt hcurrentActiveAfter (by simpa [da] using hcurrentFinal)
        have htCurrentEvent :
            tCurrent ∈ proposalRemovalTimes val_m val_w improved daWomen := by
          apply (mem_proposalRemovalTimes_iff val_m val_w improved daWomen tCurrent).2
          refine ⟨htCurrentLt, current, hcurrentImproved, wCurrentFinal, ?_,
            hmemCurrent, hnotCurrent⟩
          exact (mem_matchedWomenOfMen_iff da improved wCurrentFinal).2
            ⟨current, hcurrentImproved, hcurrentFinal⟩
        have htCurrentLe : tCurrent ≤ t := htmax tCurrent htCurrentEvent
        omega
      · have hle : t + 1 ≤ Fintype.card M * Fintype.card W :=
          Nat.succ_le_of_lt htlt
        have hge : Fintype.card M * Fintype.card W ≤ t + 1 :=
          Nat.le_of_not_gt hafterLt
        have heq : t + 1 = Fintype.card M * Fintype.card W := le_antisymm hle hge
        have hactiveFinal : IsActiveMan val_m (deferredAcceptanceState val_m val_w) current := by
          simpa [deferredAcceptanceState_eq_daStateAfterSteps, heq] using hcurrentActiveAfter
        exact (deferredAcceptanceState_terminated val_m val_w) ⟨current, hactiveFinal⟩
    have hcurrentMatch :
        (daStateAfterSteps val_m val_w t).m_match current = some w :=
      ((daStateAfterSteps val_m val_w t).consistent current w).2 hcurrent
    have hcurrentWSpent :
        w ∉ (daStateAfterSteps val_m val_w t).m_proposals current := by
      exact (daStateAfterSteps_satisfies_invariants val_m val_w t).2.2.1
        current w hcurrentMatch
    have hcurrentWNonneg : 0 ≤ val_m current w := by
      exact (daStateAfterSteps_satisfies_invariants val_m val_w t).1
        current w hcurrentMatch
    have hcurrentFinalBelow :
        valM val_m current (da.m_match current) < val_m current w := by
      cases hcurrentFinal : da.m_match current with
      | none =>
          have hpos : 0 < val_m current w :=
            lt_of_le_of_ne hcurrentWNonneg (Ne.symm (hnozeroM current w))
          simpa [valM, hcurrentFinal] using hpos
      | some wCurrentFinal =>
          have hcurrentFinalNonneg : 0 ≤ val_m current wCurrentFinal := by
            have hstable := da_produces_stable_matching val_m val_w
            simpa [da, valM, hcurrentFinal] using hstable.1 current
          have hcurrentFinalNe : wCurrentFinal ≠ w := by
            intro heq
            subst wCurrentFinal
            have hdaWCurrent : da.w_match w = some current :=
              (da.consistent_m current w).1 hcurrentFinal
            have hdaWA : da.w_match w = some a :=
              (da.consistent_m a w).1 hfinalAw
            exact hcurrentNeA (Option.some.inj (hdaWCurrent.symm.trans hdaWA))
          have hcurrentFinalAtT :
              wCurrentFinal ∈ (daStateAfterSteps val_m val_w t).m_proposals current := by
            by_contra hnotCurrentFinal
            have hneAtT :
                (daStateAfterSteps val_m val_w t).m_match current ≠ some wCurrentFinal := by
              rw [hcurrentMatch]
              exact fun heq => hcurrentFinalNe (Option.some.inj heq.symm)
            have hnotFinal :
                (deferredAcceptanceState val_m val_w).m_match current ≠ some wCurrentFinal :=
              m_match_ne_deferredAcceptanceState_of_not_mem_after_steps
                val_m val_w (Nat.le_of_lt htlt) hnotCurrentFinal hneAtT
            exact hnotFinal (by simpa [da, deferredAcceptance] using hcurrentFinal)
          have hle : val_m current wCurrentFinal ≤ val_m current w := by
            exact (daStateAfterSteps_satisfies_invariants val_m val_w t).2.2.2.2
              current w wCurrentFinal hcurrentWSpent hcurrentFinalAtT hcurrentFinalNonneg
          have hlt : val_m current wCurrentFinal < val_m current w := by
            exact lt_of_le_of_ne hle
              (fun heq => hcurrentFinalNe (hstrictM current wCurrentFinal w
                hcurrentFinalNonneg hcurrentWNonneg heq))
          simpa [valM, hcurrentFinal] using hlt
    have hcurrentNotImproved' : ¬ (valM val_m current (da.m_match current) <
        valM val_m current (tau.m_match current)) := by
      simpa [improved, strictlyImprovedMen] using hcurrentNotImproved
    have hcurrentTauLe : valM val_m current (tau.m_match current) ≤
        valM val_m current (da.m_match current) :=
      le_of_not_gt hcurrentNotImproved'
    have hcurrentPref : valM val_m current (tau.m_match current) < val_m current w :=
      lt_of_le_of_lt hcurrentTauLe hcurrentFinalBelow
    have hm0NeCurrent : m0 ≠ current := by
      intro heq
      subst current
      exact hcurrentNotImproved hm0
    have hwomanPref : val_w w m0 < val_w w current := by
      exact woman_prefers_current_of_prior_proposal_removal val_m val_w
        ht0SuccLe hnot0 hcurrent hm0NeCurrent hstrictW hm0Pos
    refine ⟨current, w, ?_, ?_, hcurrentPref, ?_⟩
    · simpa [improved] using hcurrentNotImproved
    · simpa [tauWomen, improved] using hwTau
    · simpa [valW, htauW] using hwomanPref
  · have himage' :
      matchedWomenOfMen tau (strictlyImprovedMen val_m
        (deferredAcceptance val_m val_w) tau) ≠
      matchedWomenOfMen (deferredAcceptance val_m val_w)
        (strictlyImprovedMen val_m (deferredAcceptance val_m val_w) tau) := by
      simpa [tauWomen, daWomen, improved, da] using himage
    exact exists_blocking_pair_of_strictly_improved_men_of_matchedWomenOfMen_ne
      val_m val_w hstrictM hstrictW hnozeroM hnozeroW tau htauIR himage'

/-- The women-side form of the full comparative matching blocking lemma. -/
theorem exists_blocking_pair_of_nonempty_strictly_improved_women
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile val_w)
    (hnozeroM : MenNoOutsideTie val_m)
    (hnozeroW : WomenNoOutsideTie val_w)
    (tau : Assignment M W)
    (htauIR : (∀ m, 0 ≤ valM val_m m (tau.m_match m)) ∧
      ∀ w, 0 ≤ valW val_w w (tau.w_match w))
    (hnonempty : (strictlyImprovedWomen val_w
      (womenDeferredAcceptance val_m val_w) tau).Nonempty) :
    ∃ m w,
      w ∉ strictlyImprovedWomen val_w (womenDeferredAcceptance val_m val_w) tau ∧
      m ∈ matchedMenOfWomen tau
        (strictlyImprovedWomen val_w (womenDeferredAcceptance val_m val_w) tau) ∧
      valM val_m m (tau.m_match m) < val_m m w ∧
      valW val_w w (tau.w_match w) < val_w w m := by
  have htauIRSwap : (∀ w, 0 ≤ valM val_w w (tau.swap.m_match w)) ∧
      ∀ m, 0 ≤ valW val_m m (tau.swap.w_match m) := by
    constructor
    · intro w
      simpa [Assignment.swap, valM, valW] using htauIR.2 w
    · intro m
      simpa [Assignment.swap, valM, valW] using htauIR.1 m
  have hnonemptySwap : (strictlyImprovedMen val_w
      (deferredAcceptance val_w val_m) tau.swap).Nonempty := by
    simpa [strictlyImprovedWomen, womenDeferredAcceptance, Assignment.swap_swap] using hnonempty
  obtain ⟨w, m, hw, hm, hwPref, hmPref⟩ :=
    exists_blocking_pair_of_nonempty_strictly_improved_men
      val_w val_m hstrictW hstrictM hnozeroW hnozeroM tau.swap htauIRSwap hnonemptySwap
  refine ⟨m, w, ?_, ?_, ?_, ?_⟩
  · simpa [strictlyImprovedWomen, womenDeferredAcceptance, Assignment.swap_swap] using hw
  · simpa [matchedMenOfWomen, strictlyImprovedWomen, womenDeferredAcceptance,
      Assignment.swap_swap] using hm
  · simpa [Assignment.swap, valM, valW] using hmPref
  · simpa [Assignment.swap, valM, valW] using hwPref

/--
Changing one woman's reported values cannot strictly improve her true outcome
when the original profile has a unique stable assignment.
-/
theorem woman_not_strictly_improved_by_unilateral_report_of_unique_stable
    [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (base_w altered_w : W → M → ℝ) (target : W)
    (hstrictM : MenAcceptableStrictPreferenceProfile val_m)
    (hstrictW : WomenAcceptableStrictPreferenceProfile base_w)
    (hnozeroM : MenNoOutsideTie val_m)
    (hnozeroW : WomenNoOutsideTie base_w)
    (hunchanged : ∀ w, w ≠ target → altered_w w = base_w w)
    (mu tau : Assignment M W)
    (hmu : IsStable val_m base_w mu)
    (hunique : ∀ nu, IsStable val_m base_w nu → nu = mu)
    (htau : IsStable val_m altered_w tau) :
    valW base_w target (tau.w_match target) ≤ valW base_w target (mu.w_match target) := by
  by_contra hnot
  have hprofit : valW base_w target (mu.w_match target) <
      valW base_w target (tau.w_match target) := lt_of_not_ge hnot
  have hmuEqWomenDA : mu = womenDeferredAcceptance val_m base_w := by
    exact (hunique (womenDeferredAcceptance val_m base_w)
      (womenDeferredAcceptance_stable val_m base_w)).symm
  have htauBaseIR : (∀ m, 0 ≤ valM val_m m (tau.m_match m)) ∧
      ∀ w, 0 ≤ valW base_w w (tau.w_match w) := by
    constructor
    · exact htau.1
    · intro w
      by_cases hw : w = target
      · subst w
        exact le_trans (hmu.2.1 target) (le_of_lt hprofit)
      · have hIR := htau.2.1 w
        simpa [valW, hunchanged w hw] using hIR
  have htargetImproved : target ∈ strictlyImprovedWomen base_w
      (womenDeferredAcceptance val_m base_w) tau := by
    simpa [strictlyImprovedWomen, strictlyImprovedMen, womenDeferredAcceptance,
      Assignment.swap, valM, valW, hmuEqWomenDA] using hprofit
  obtain ⟨m, w, hwNotImproved, hmMatched, hmPref, hwPref⟩ :=
    exists_blocking_pair_of_nonempty_strictly_improved_women
      val_m base_w hstrictM hstrictW hnozeroM hnozeroW tau htauBaseIR
      ⟨target, htargetImproved⟩
  have hwNe : w ≠ target := by
    intro hw
    subst w
    exact hwNotImproved htargetImproved
  have hwPrefAltered : valW altered_w w (tau.w_match w) < altered_w w m := by
    simpa [valW, hunchanged w hwNe] using hwPref
  exact htau.2.2 m w hmPref hwPrefAltered

end Matching
end AppliedModelingLib
