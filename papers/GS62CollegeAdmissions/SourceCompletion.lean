import GS62CollegeAdmissions.MainTheorems
import GS62CollegeAdmissions.Examples

/-!
# Remaining source-shaped Gale--Shapley statements

This module supplies the source definitions and the marriage-side results that
are stated in the 1962 article but were absent from the original GS62 paper
folder.  Algorithm-specific statements are kept in `BatchedProcedure.lean`.
-/

namespace GS62CollegeAdmissions
open AppliedModelingLib.Matching

/-! ## Section 2 college-admissions model -/

/--
Strict applicant rankings, with no college tied with being unassigned.  Values
below zero give an arbitrary injective numerical extension of an applicant's
unlisted colleges; source-facing procedures filter them out before ranking.
-/
def ApplicantsStrictCollegeProfile {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ) : Prop :=
  (∀ a c c', val_applicant a c = val_applicant a c' → c = c') ∧
    ∀ a c, val_applicant a c ≠ 0

/--
Strict college rankings, with no applicant tied with an empty seat.  Values
below zero similarly extend the unlisted applicants only for a total numeric
representation; they never become mutually eligible applications.
-/
def CollegesStrictApplicantProfile {Applicants Colleges : Type*}
    (val_college : Colleges → Applicants → ℝ) : Prop :=
  (∀ c a a', val_college c a = val_college c a' → a = a') ∧
    ∀ c a, val_college c a ≠ 0

/--
The paper's finite strict college-admissions domain.  Positive values encode
names appearing on an acceptable list and negative values encode omitted
names; `0` is the outside option.
-/
def gs_strict_college_admissions_domain {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ) : Prop :=
  ApplicantsStrictCollegeProfile val_applicant ∧
    CollegesStrictApplicantProfile val_college

/-- A feasible college assignment is a consistent assignment respecting quotas. -/
def gs_feasible_college_assignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  ManyToOneAssignment.RespectsQuota quota mu

/--
Completed standard stability convention used by the reusable many-to-one API:
quotas and individual rationality hold, and there is no applicant-college pair
that prefers one another to the current assignment (including through an empty
seat).  This deliberately extends the page-10 displayed replacement-pair
condition, which is formalized separately in `SourceStability.lean`.
-/
def gs_stable_college_assignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  ManyToOne.IsStable val_applicant val_college quota mu

/--
Failure of the completed standard stability convention.  This is an internal
operational predicate, not the literal page-10 "unstable" definition.
-/
def gs_unstable_college_assignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  ¬ gs_stable_college_assignment quota val_applicant val_college mu

/-- Applicant optimality among all stable assignments in the same quota market. -/
def gs_applicant_optimal_college_assignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs_stable_college_assignment quota val_applicant val_college mu ∧
    ∀ nu, gs_stable_college_assignment quota val_applicant val_college nu →
      ∀ a, ManyToOne.valApplicant val_applicant a (nu.app_match a) ≤
        ManyToOne.valApplicant val_applicant a (mu.app_match a)

/--
Source-shaped arbitrary-quota existence theorem.  The strict-list hypothesis is
present exactly as in the paper, although existence in the reusable library is
proved for the more general weak-value encoding.
-/
theorem paper_gs62_college_admissions_stable_assignment_exists_on_strict_domain
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (_hdomain : gs_strict_college_admissions_domain val_applicant val_college) :
    ∃ mu : ManyToOneAssignment Applicants Colleges,
      gs_stable_college_assignment quota val_applicant val_college mu := by
  simpa [gs_stable_college_assignment] using
    paper_gs62_college_admissions_stable_assignment_exists
      quota val_applicant val_college

/-! ## Unequal marriage communities -/

private theorem card_right_le_left_of_right_complete
    {M W : Type*} [Fintype M] [Fintype W]
    (mu : Assignment M W)
    (hcomplete : ∀ w, ∃ m, mu.w_match w = some m) :
    Fintype.card W ≤ Fintype.card M := by
  classical
  let f : W → M := fun w => Classical.choose (hcomplete w)
  have hspec : ∀ w, mu.w_match w = some (f w) := fun w =>
    Classical.choose_spec (hcomplete w)
  have hinj : Function.Injective f := by
    intro w w' heq
    have hw : mu.m_match (f w) = some w :=
      (mu.consistent_m (f w) w).2 (hspec w)
    have hw' : mu.m_match (f w') = some w' :=
      (mu.consistent_m (f w') w').2 (hspec w')
    rw [heq] at hw
    exact Option.some.inj (hw.symm.trans hw')
  exact Fintype.card_le_of_injective f hinj

private theorem card_left_le_right_of_left_complete
    {M W : Type*} [Fintype M] [Fintype W]
    (mu : Assignment M W)
    (hcomplete : ∀ m, ∃ w, mu.m_match m = some w) :
    Fintype.card M ≤ Fintype.card W := by
  simpa using card_right_le_left_of_right_complete mu.swap hcomplete

/-- In an all-acceptable stable market, every member of the smaller left side is matched. -/
theorem stable_left_complete_of_card_le_all_pairs_acceptable
    {M W : Type*} [Fintype M] [Fintype W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W)
    (hcard : Fintype.card M ≤ Fintype.card W)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hstable : IsStable val_m val_w mu) :
    ∀ m, ∃ w, mu.m_match m = some w := by
  classical
  intro m
  by_cases hm : ∃ w, mu.m_match m = some w
  · exact hm
  · have hmnone : mu.m_match m = none := by
      cases h : mu.m_match m with
      | none => rfl
      | some w => exact False.elim (hm ⟨w, h⟩)
    have hnotRightComplete : ¬ ∀ w, ∃ m', mu.w_match w = some m' := by
      intro hright
      have hrightCard := card_right_le_left_of_right_complete mu hright
      have hcardEq : Fintype.card M = Fintype.card W :=
        Nat.le_antisymm hcard hrightCard
      have hleft := Assignment.m_complete_of_w_complete_of_card_eq
        mu hcardEq hright
      exact hm (hleft m)
    push Not at hnotRightComplete
    rcases hnotRightComplete with ⟨w, hw⟩
    have hwnone : mu.w_match w = none := by
      cases h : mu.w_match w with
      | none => rfl
      | some m' => exact False.elim (hw m' h)
    have hmb : valM val_m m (mu.m_match m) < val_m m w := by
      simpa [valM, hmnone] using hacceptable.1 m w
    have hwb : valW val_w w (mu.w_match w) < val_w w m := by
      simpa [valW, hwnone] using hacceptable.2 w m
    exact False.elim (hstable.2.2 m w hmb hwb)

/-- In an all-acceptable stable market, every member of the smaller right side is matched. -/
theorem stable_right_complete_of_card_le_all_pairs_acceptable
    {M W : Type*} [Fintype M] [Fintype W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W)
    (hcard : Fintype.card W ≤ Fintype.card M)
    (hacceptable : AllPairsAcceptable val_m val_w)
    (hstable : IsStable val_m val_w mu) :
    ∀ w, ∃ m, mu.w_match w = some m := by
  have hswap : IsStable val_w val_m mu.swap :=
    (isStable_swap_iff val_m val_w mu).2 hstable
  simpa [Assignment.swap] using
    stable_left_complete_of_card_le_all_pairs_acceptable
      val_w val_m mu.swap hcard ⟨hacceptable.2, hacceptable.1⟩ hswap

/--
The paper's unequal-side conclusion: DA is stable, fully matches the smaller
side, and (when cardinalities differ) leaves someone on the larger side
unmatched.
-/
theorem paper_gs62_unequal_sides_deferred_acceptance
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hacceptable : AllPairsAcceptable val_m val_w) :
    IsStable val_m val_w (deferredAcceptance val_m val_w) ∧
      (Fintype.card M < Fintype.card W →
        (∀ m, ∃ w, (deferredAcceptance val_m val_w).m_match m = some w) ∧
        ∃ w, (deferredAcceptance val_m val_w).w_match w = none) ∧
      (Fintype.card W < Fintype.card M →
        (∀ w, ∃ m, (deferredAcceptance val_m val_w).w_match w = some m) ∧
        ∃ m, (deferredAcceptance val_m val_w).m_match m = none) := by
  classical
  let mu := deferredAcceptance val_m val_w
  have hstable : IsStable val_m val_w mu :=
    da_produces_stable_matching val_m val_w
  refine ⟨hstable, ?_, ?_⟩
  · intro hlt
    have hleft := stable_left_complete_of_card_le_all_pairs_acceptable
      val_m val_w mu (Nat.le_of_lt hlt) hacceptable hstable
    refine ⟨hleft, ?_⟩
    by_contra hno
    push Not at hno
    have hright : ∀ w, ∃ m, mu.w_match w = some m := by
      intro w
      cases hw : mu.w_match w with
      | none => exact False.elim (hno w hw)
      | some m => exact ⟨m, rfl⟩
    exact (Nat.not_le_of_lt hlt) (card_right_le_left_of_right_complete mu hright)
  · intro hlt
    have hright := stable_right_complete_of_card_le_all_pairs_acceptable
      val_m val_w mu (Nat.le_of_lt hlt) hacceptable hstable
    refine ⟨hright, ?_⟩
    by_contra hno
    push Not at hno
    have hleft : ∀ m, ∃ w, mu.m_match m = some w := by
      intro m
      cases hm : mu.m_match m with
      | none => exact False.elim (hno m hm)
      | some w => exact ⟨w, rfl⟩
    exact (Nat.not_le_of_lt hlt) (card_left_le_right_of_left_complete mu hleft)

/-! ## Receiver-proposing optimality and uniqueness -/

/-- Receiver-proposing DA is stable and receiver-optimal on the strict source domain. -/
theorem paper_gs62_receiver_proposing_stable_and_optimal
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hdomain : gs_strict_marriage_domain val_m val_w) :
    IsStable val_m val_w (womenDeferredAcceptance val_m val_w) ∧
      ∀ mu, IsStable val_m val_w mu → ∀ w,
        valW val_w w (mu.w_match w) ≤
          valW val_w w ((womenDeferredAcceptance val_m val_w).w_match w) := by
  exact ⟨womenDeferredAcceptance_stable val_m val_w,
    womenDeferredAcceptance_is_women_optimal_of_strict_preferences
      val_m val_w hdomain.1 hdomain.2.1 hdomain.2.2⟩

/--
The proposing-side and receiving-side DA outcomes agree exactly iff the stable
marriage is unique.
-/
theorem paper_gs62_two_da_outcomes_agree_iff_unique_stable_marriage
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : gs_strict_marriage_domain val_m val_w) :
    deferredAcceptance val_m val_w = womenDeferredAcceptance val_m val_w ↔
      ∃! mu : Assignment M W, IsStable val_m val_w mu := by
  classical
  rcases hdomain with ⟨hstrictM, hstrictW, hacceptable⟩
  constructor
  · intro heq
    refine ⟨deferredAcceptance val_m val_w,
      da_produces_stable_matching val_m val_w, ?_⟩
    intro mu hmu
    have hmuComplete := stable_complete_of_card_eq_all_pairs_acceptable
      val_m val_w mu hcard hacceptable hmu
    have hdaComplete := deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
      val_m val_w hcard hacceptable
    apply assignment_eq_of_complete_same_man_values_of_strict
      val_m hstrictM hmuComplete.1 hdaComplete.1
    intro m
    apply le_antisymm
    · exact da_is_men_optimal_of_strict_preferences
        val_m val_w hstrictM hstrictW hacceptable mu hmu m
    · rw [heq]
      exact womenDeferredAcceptance_is_men_pessimal_of_strict_preferences
        val_m val_w hcard hstrictM hstrictW hacceptable mu hmu m
  · rintro ⟨mu, hstable, hunique⟩
    calc
      deferredAcceptance val_m val_w = mu :=
        hunique (deferredAcceptance val_m val_w)
          (da_produces_stable_matching val_m val_w)
      _ = womenDeferredAcceptance val_m val_w :=
        (hunique (womenDeferredAcceptance val_m val_w)
          (womenDeferredAcceptance_stable val_m val_w)).symm

end GS62CollegeAdmissions
