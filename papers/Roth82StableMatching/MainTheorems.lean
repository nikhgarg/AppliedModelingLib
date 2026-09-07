import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import AppliedModelingLib.Markets.Matching.Basic
import AppliedModelingLib.Markets.Matching.DeferredAcceptance

/-!
# Paper-Facing Theorems: The Economics of Matching: Stability and Incentives (Roth 1982)

This file contains foundational stable matching definitions, closed
source-domain endpoints, and compatibility certificate wrappers for the Roth
1982 paper. The source paper's Theorem 3 is an
impossibility result; the DA truthfulness wrapper below corresponds to the
one-sided incentive statement in Theorem 5, not to source Theorem 3.
-/

namespace Roth82StableMatching
open AppliedModelingLib.Matching


/-! ## 1) Paper-Facing Definitions: 2023 Matching -/

/-- Paper Definition: Utility of a match. $u_m(w) = v_m(w)$, $u_m(\emptyset) = 0$. -/
def paper_matching_valM {M W : Type*} (val_m : M → W → ℝ) (m : M) (w : Option W) : ℝ :=
  match w with
  | none => 0
  | some w' => val_m m w'

theorem paper_matching_valM_eq {M W : Type*} (val_m : M → W → ℝ) (m : M) (w : Option W) :
  paper_matching_valM val_m m w = valM val_m m w := by rfl

/-- Paper Definition: Utility of a match. $u_w(m) = v_w(m)$, $u_w(\emptyset) = 0$. -/
def paper_matching_valW {M W : Type*} (val_w : W → M → ℝ) (w : W) (m : Option M) : ℝ :=
  match m with
  | none => 0
  | some m' => val_w w m'

theorem paper_matching_valW_eq {M W : Type*} (val_w : W → M → ℝ) (w : W) (m : Option M) :
  paper_matching_valW val_w w m = valW val_w w m := by rfl

/-- Paper Definition: A matching is stable if it is individually rational and has no blocking pairs.
    IR: $0 \le u_m(\mu(m))$ and $0 \le u_w(\mu(w))$.
    No blocking pair: there is no $(m, w)$ such that $u_m(\mu(m)) < v_m(w)$ and $u_w(\mu(w)) < v_w(m)$. -/
def paper_is_stable {M W : Type*} (val_m : M → W → ℝ) (val_w : W → M → ℝ) (mu : Assignment M W) : Prop :=
  (∀ m, 0 ≤ paper_matching_valM val_m m (mu.m_match m)) ∧
  (∀ w, 0 ≤ paper_matching_valW val_w w (mu.w_match w)) ∧
  (∀ m w, paper_matching_valM val_m m (mu.m_match m) < val_m m w →
          paper_matching_valW val_w w (mu.w_match w) < val_w w m → False)

theorem paper_is_stable_eq {M W : Type*} (val_m : M → W → ℝ) (val_w : W → M → ℝ) (mu : Assignment M W) :
  paper_is_stable val_m val_w mu ↔ IsStable val_m val_w mu := by rfl

/-- Paper Definition: A stable matching $\mu$ is men-optimal if every man prefers his partner in $\mu$ to his partner in any other stable matching. -/
def paper_is_men_optimal {M W : Type*} (val_m : M → W → ℝ) (val_w : W → M → ℝ) (mu : Assignment M W) : Prop :=
  paper_is_stable val_m val_w mu ∧
  ∀ mu', paper_is_stable val_m val_w mu' →
    ∀ m, paper_matching_valM val_m m (mu'.m_match m) ≤ paper_matching_valM val_m m (mu.m_match m)

/-- Paper Definition: A stable matching is women-optimal if every woman weakly
prefers her partner in it to her partner in any other stable matching. -/
def paper_is_women_optimal {M W : Type*} (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  paper_is_stable val_m val_w mu ∧
  ∀ mu', paper_is_stable val_m val_w mu' →
    ∀ w, paper_matching_valW val_w w (mu'.w_match w) ≤
      paper_matching_valW val_w w (mu.w_match w)

/--
Paper-domain assumption for the strict marriage problem: every agent has a
strict ranking over the opposite side, and every potential pair is acceptable
relative to the outside option used in the Lean encoding.
-/
def paper_strict_marriage_domain {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  (∀ m w w', val_m m w = val_m m w' → w = w') ∧
    (∀ w m m', val_w w m = val_w w m' → m = m') ∧
    (∀ m w, 0 < val_m m w) ∧
    (∀ w m, 0 < val_w w m)

/-- Source-domain strict rankings, without assumptions about the outside option. -/
def paper_strict_preference_profile {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  (∀ m w w', val_m m w = val_m m w' → w = w') ∧
    (∀ w m m', val_w w m = val_w w m' → m = m')

/-- Paper Definition: Truth-telling is a dominant strategy for men in the men-proposing DA algorithm.
    No man can improve his match by misreporting his preferences, assuming others report truthfully. -/
def paper_truthful_for_men {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M) (report_m : W → ℝ),
    paper_matching_valM val_m m ((mechanism (Function.update val_m m report_m) val_w).m_match m) ≤
    paper_matching_valM val_m m ((mechanism val_m val_w).m_match m)

/-- Paper Definition: Truth-telling is dominant for women in a direct matching procedure. -/
def paper_truthful_for_women {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ) (w : W) (report_w : M → ℝ),
    paper_matching_valW val_w w ((mechanism val_m (Function.update val_w w report_w)).w_match w) ≤
    paper_matching_valW val_w w ((mechanism val_m val_w).w_match w)

/-- A stable procedure on strict reported preference profiles. -/
def paper_stable_matching_procedure_on_strict_profiles
    {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ val_m val_w, paper_strict_preference_profile val_m val_w →
    paper_is_stable val_m val_w (mechanism val_m val_w)

/-- Men-side dominant truthfulness when true and reported profiles are strict. -/
def paper_truthful_for_men_on_strict_profiles
    {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    paper_strict_preference_profile val_m val_w →
      ∀ (m : M) (report_m : W → ℝ),
        paper_strict_preference_profile (Function.update val_m m report_m) val_w →
          paper_matching_valM val_m m
              ((mechanism (Function.update val_m m report_m) val_w).m_match m) ≤
            paper_matching_valM val_m m ((mechanism val_m val_w).m_match m)

/-- Women-side dominant truthfulness when true and reported profiles are strict. -/
def paper_truthful_for_women_on_strict_profiles
    {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    paper_strict_preference_profile val_m val_w →
      ∀ (w : W) (report_w : M → ℝ),
        paper_strict_preference_profile val_m (Function.update val_w w report_w) →
          paper_matching_valW val_w w
              ((mechanism val_m (Function.update val_w w report_w)).w_match w) ≤
            paper_matching_valW val_w w ((mechanism val_m val_w).w_match w)

/-- A stable procedure on the source's complete strict marriage domain. -/
def paper_stable_matching_procedure_on_strict_marriage_domain
    {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ val_m val_w, paper_strict_marriage_domain val_m val_w →
    paper_is_stable val_m val_w (mechanism val_m val_w)

/-- Men-side dominant truthfulness for legal reports in the strict marriage domain. -/
def paper_truthful_for_men_on_strict_marriage_domain
    {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    paper_strict_marriage_domain val_m val_w →
      ∀ (m : M) (report_m : W → ℝ),
        paper_strict_marriage_domain (Function.update val_m m report_m) val_w →
          paper_matching_valM val_m m
              ((mechanism (Function.update val_m m report_m) val_w).m_match m) ≤
            paper_matching_valM val_m m ((mechanism val_m val_w).m_match m)

/-- Women-side dominant truthfulness for legal reports in the strict marriage domain. -/
def paper_truthful_for_women_on_strict_marriage_domain
    {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    paper_strict_marriage_domain val_m val_w →
      ∀ (w : W) (report_w : M → ℝ),
        paper_strict_marriage_domain val_m (Function.update val_w w report_w) →
          paper_matching_valW val_w w
              ((mechanism val_m (Function.update val_w w report_w)).w_match w) ≤
            paper_matching_valW val_w w ((mechanism val_m val_w).w_match w)

/-- Paper Definition: a man has a profitable unilateral misreport. -/
def paper_profitable_man_misreport {M W : Type*} [DecidableEq M]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W)
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M) (report_m : W → ℝ) :
    Prop :=
  paper_matching_valM val_m m ((mechanism val_m val_w).m_match m) <
    paper_matching_valM val_m m
      ((mechanism (Function.update val_m m report_m) val_w).m_match m)

/-- Paper Definition: a woman has a profitable unilateral misreport. -/
def paper_profitable_woman_misreport {M W : Type*} [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W)
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (w : W) (report_w : M → ℝ) :
    Prop :=
  paper_matching_valW val_w w ((mechanism val_m val_w).w_match w) <
    paper_matching_valW val_w w
      ((mechanism val_m (Function.update val_w w report_w)).w_match w)

/-- A report ranks the given optional man-side partner first. -/
def paper_man_report_ranks_partner_first {W : Type*} (report_m : W → ℝ)
    (partner : Option W) : Prop :=
  match partner with
  | none => ∀ w, report_m w ≤ 0
  | some wstar => ∀ w, report_m w ≤ report_m wstar

/-- A man weakly prefers his partner in `nu` to his partner in `mu`. -/
def paper_man_weakly_prefers_outcome {M W : Type*} (val_m : M → W → ℝ)
    (m : M) (nu mu : Assignment M W) : Prop :=
  paper_matching_valM val_m m (mu.m_match m) ≤
    paper_matching_valM val_m m (nu.m_match m)

/-- A woman weakly prefers her partner in `nu` to her partner in `mu`. -/
def paper_woman_weakly_prefers_outcome {M W : Type*} (val_w : W → M → ℝ)
    (w : W) (nu mu : Assignment M W) : Prop :=
  paper_matching_valW val_w w (mu.w_match w) ≤
    paper_matching_valW val_w w (nu.w_match w)

/-- A man is a top choice for woman `w` under the true preference profile. -/
def paper_is_top_choice_for_woman {M W : Type*} (val_w : W → M → ℝ)
    (w : W) (mstar : M) : Prop :=
  ∀ m, val_w w m ≤ val_w w mstar

/-- A man is the unique first choice for woman `w` under the true preference profile. -/
def paper_is_strict_top_choice_for_woman {M W : Type*} (val_w : W → M → ℝ)
    (w : W) (mstar : M) : Prop :=
  ∀ m, m ≠ mstar → val_w w m < val_w w mstar

/--
A woman's report preserves her true first choice if every true strict top choice
is still ranked uniquely first in the report.
-/
def paper_woman_report_preserves_first_choice {M W : Type*}
    (val_w : W → M → ℝ) (w : W) (report_w : M → ℝ) : Prop :=
  ∀ mstar, paper_is_strict_top_choice_for_woman val_w w mstar →
    ∀ m, m ≠ mstar → report_w m < report_w mstar

/-- A nonempty finite strict preference list has a unique first choice. -/
theorem paper_exists_strict_top_choice_for_woman
    {M W : Type*} [Fintype M] [Nonempty M]
    (val_w : W → M → ℝ)
    (hstrictW : ∀ w m m', val_w w m = val_w w m' → m = m')
    (w : W) :
    ∃ mstar, paper_is_strict_top_choice_for_woman val_w w mstar := by
  classical
  obtain ⟨mstar, _hmstar_mem, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset M)
      (fun m => val_w w m) (Finset.univ_nonempty)
  refine ⟨mstar, ?_⟩
  intro m hm
  have hle : val_w w m ≤ val_w w mstar :=
    hmax m (Finset.mem_univ m)
  exact lt_of_le_of_ne hle (by
    intro heq
    exact hm (hstrictW w m mstar heq))

/--
Given an arbitrary report, raise `mstar` above every reported alternative while
leaving all other scores unchanged. This is the local report transformation
needed for Corollary 5.1's source reading.
-/
noncomputable def paper_raise_first_choice_report
    {M : Type*} [Fintype M] [DecidableEq M]
    (mstar : M) (report_w : M → ℝ) : M → ℝ :=
  let vals := (Finset.univ : Finset M).image report_w
  let hvals : vals.Nonempty :=
    ⟨report_w mstar, Finset.mem_image.mpr ⟨mstar, Finset.mem_univ mstar, rfl⟩⟩
  fun m => if m = mstar then max (vals.max' hvals) 0 + 1 else report_w m

theorem paper_raise_first_choice_report_self
    {M : Type*} [Fintype M] [DecidableEq M]
    (mstar : M) (report_w : M → ℝ) :
    paper_raise_first_choice_report mstar report_w mstar =
      max
        (((Finset.univ : Finset M).image report_w).max'
          ⟨report_w mstar, Finset.mem_image.mpr
            ⟨mstar, Finset.mem_univ mstar, rfl⟩⟩) 0 + 1 := by
  simp [paper_raise_first_choice_report]

theorem paper_raise_first_choice_report_of_ne
    {M : Type*} [Fintype M] [DecidableEq M]
    (mstar : M) (report_w : M → ℝ) {m : M} (hm : m ≠ mstar) :
    paper_raise_first_choice_report mstar report_w m = report_w m := by
  simp [paper_raise_first_choice_report, hm]

theorem paper_raise_first_choice_report_top
    {M : Type*} [Fintype M] [DecidableEq M]
    (mstar : M) (report_w : M → ℝ) :
    ∀ m, m ≠ mstar →
      paper_raise_first_choice_report mstar report_w m <
        paper_raise_first_choice_report mstar report_w mstar := by
  intro m hm
  let vals := (Finset.univ : Finset M).image report_w
  let hvals : vals.Nonempty :=
    ⟨report_w mstar, Finset.mem_image.mpr ⟨mstar, Finset.mem_univ mstar, rfl⟩⟩
  have hmem : report_w m ∈ vals := by
    exact Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩
  have hle : report_w m ≤ vals.max' hvals := Finset.le_max' vals (report_w m) hmem
  have hleMax : report_w m ≤ max (vals.max' hvals) 0 := le_trans hle (le_max_left _ _)
  have hself :
      paper_raise_first_choice_report mstar report_w mstar =
        max (vals.max' hvals) 0 + 1 := by
    simp [paper_raise_first_choice_report, vals]
  have hmval :
      paper_raise_first_choice_report mstar report_w m = report_w m :=
    paper_raise_first_choice_report_of_ne mstar report_w hm
  rw [hself, hmval]
  linarith

theorem paper_raise_first_choice_report_top_pos
    {M : Type*} [Fintype M] [DecidableEq M]
    (mstar : M) (report_w : M → ℝ) :
    0 < paper_raise_first_choice_report mstar report_w mstar := by
  let vals := (Finset.univ : Finset M).image report_w
  let hvals : vals.Nonempty :=
    ⟨report_w mstar, Finset.mem_image.mpr ⟨mstar, Finset.mem_univ mstar, rfl⟩⟩
  have hself :
      paper_raise_first_choice_report mstar report_w mstar =
        max (vals.max' hvals) 0 + 1 := by
    simp [paper_raise_first_choice_report, vals]
  have hnonneg : (0 : ℝ) ≤ max (vals.max' hvals) 0 := le_max_right _ _
  rw [hself]
  linarith

theorem paper_raise_first_choice_report_preserves_woman_first_choice
    {M W : Type*} [Fintype M] [DecidableEq M]
    (val_w : W → M → ℝ) (w : W) (mstar : M) (report_w : M → ℝ)
    (hfirst : paper_is_strict_top_choice_for_woman val_w w mstar) :
    paper_woman_report_preserves_first_choice val_w w
      (paper_raise_first_choice_report mstar report_w) := by
  intro top htop m hm
  have htop_eq : top = mstar := by
    by_contra hne
    have hlt1 := hfirst top hne
    have hlt2 := htop mstar (fun h => hne h.symm)
    linarith
  subst top
  exact paper_raise_first_choice_report_top mstar report_w m hm

/-- Raising one alternative above a strict report preserves strictness. -/
theorem paper_raise_first_choice_report_strict
    {M : Type*} [Fintype M] [DecidableEq M]
    (mstar : M) (report_w : M → ℝ)
    (hstrict : ∀ m m', report_w m = report_w m' → m = m') :
    ∀ m m',
      paper_raise_first_choice_report mstar report_w m =
          paper_raise_first_choice_report mstar report_w m' →
        m = m' := by
  intro m m' heq
  by_cases hm : m = mstar
  · subst m
    by_cases hm' : m' = mstar
    · exact hm'.symm
    · have hlt := paper_raise_first_choice_report_top mstar report_w m' hm'
      linarith
  · by_cases hm' : m' = mstar
    · subst m'
      have hlt := paper_raise_first_choice_report_top mstar report_w m hm
      linarith
    · apply hstrict m m'
      rw [paper_raise_first_choice_report_of_ne mstar report_w hm,
        paper_raise_first_choice_report_of_ne mstar report_w hm'] at heq
      exact heq

/-- Raising one alternative above a positive report preserves positivity. -/
theorem paper_raise_first_choice_report_pos
    {M : Type*} [Fintype M] [DecidableEq M]
    (mstar : M) (report_w : M → ℝ) (hpos : ∀ m, 0 < report_w m) :
    ∀ m, 0 < paper_raise_first_choice_report mstar report_w m := by
  intro m
  by_cases hm : m = mstar
  · subst m
    exact paper_raise_first_choice_report_top_pos mstar report_w
  · rw [paper_raise_first_choice_report_of_ne mstar report_w hm]
    exact hpos m

/--
Replacing one woman's legal report by its raised-first-choice version preserves
the complete strict marriage domain.
-/
theorem paper_strict_marriage_domain_update_raise_first_choice_report
    {M W : Type*} [Fintype M] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (w : W)
    (mstar : M) (report_w : M → ℝ)
    (hreport :
      paper_strict_marriage_domain val_m (Function.update val_w w report_w)) :
    paper_strict_marriage_domain val_m
      (Function.update val_w w
        (paper_raise_first_choice_report mstar report_w)) := by
  rcases hreport with ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hreportStrict : ∀ m m', report_w m = report_w m' → m = m' := by
    intro m m' heq
    apply hstrictW w m m'
    simpa using heq
  have hreportPos : ∀ m, 0 < report_w m := by
    intro m
    simpa using hposW w m
  refine ⟨hstrictM, ?_, hposM, ?_⟩
  · intro i m m' heq
    by_cases hi : i = w
    · subst i
      exact paper_raise_first_choice_report_strict mstar report_w hreportStrict
        m m' (by simpa using heq)
    · exact hstrictW i m m' (by simpa [Function.update, hi] using heq)
  · intro i m
    by_cases hi : i = w
    · subst i
      simpa using paper_raise_first_choice_report_pos mstar report_w hreportPos m
    · simpa [Function.update, hi] using hposW i m

/--
A woman's report misrepresents her first choice if some reported top is not truly top.

This is the older broad API used by the first Corollary 5.1 certificate wrapper.
It is stronger than Roth's proof-language reading, where the source claim is
that the non-proposing side has no need to lie about its first choice.
-/
def paper_woman_report_misrepresents_first_choice {M W : Type*}
    (val_w : W → M → ℝ) (w : W) (report_w : M → ℝ) : Prop :=
  ∃ reportedTop, (∀ m, report_w m ≤ report_w reportedTop) ∧
    ¬ paper_is_top_choice_for_woman val_w w reportedTop

/-- No woman can profit by a report that misrepresents her first choice. -/
def paper_no_profitable_first_choice_misreport_for_women
    {M W : Type*} [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ) (w : W) (report_w : M → ℝ),
    paper_woman_report_misrepresents_first_choice val_w w report_w →
      paper_matching_valW val_w w
          ((mechanism val_m (Function.update val_w w report_w)).w_match w) ≤
        paper_matching_valW val_w w ((mechanism val_m val_w).w_match w)

/--
Source-faithful Corollary 5.1 interface: for every report available to a woman,
there is a report that preserves her true first choice and gives her a weakly
better true outcome. This captures "no incentive to misrepresent first choice"
as "misstating the first choice has no extra power."
-/
def paper_no_need_to_misrepresent_first_choice_for_women_on_strict_domain
    {M W : Type*} [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    paper_strict_marriage_domain val_m val_w →
      ∀ (w : W) (report_w : M → ℝ),
        paper_strict_marriage_domain val_m (Function.update val_w w report_w) →
        ∃ faithful_report_w : M → ℝ,
          paper_strict_marriage_domain val_m
              (Function.update val_w w faithful_report_w) ∧
            paper_woman_report_preserves_first_choice val_w w faithful_report_w ∧
            paper_matching_valW val_w w
                ((mechanism val_m
                  (Function.update val_w w report_w)).w_match w) ≤
              paper_matching_valW val_w w
                ((mechanism val_m
                  (Function.update val_w w faithful_report_w)).w_match w)

/-- A woman is the unique first choice for man `m` under the true preference profile. -/
def paper_is_strict_top_choice_for_man {M W : Type*} (val_m : M → W → ℝ)
    (m : M) (wstar : W) : Prop :=
  ∀ w, w ≠ wstar → val_m m w < val_m m wstar

/--
A man's report preserves his true first choice if every true strict top choice
is still ranked uniquely first in the report.
-/
def paper_man_report_preserves_first_choice {M W : Type*}
    (val_m : M → W → ℝ) (m : M) (report_m : W → ℝ) : Prop :=
  ∀ wstar, paper_is_strict_top_choice_for_man val_m m wstar →
    ∀ w, w ≠ wstar → report_m w < report_m wstar

/--
Role-reversed Corollary 5.1 interface: for every report available to a man
under women-proposing DA, there is a report preserving his true first choice
and giving him a weakly better true outcome.
-/
def paper_no_need_to_misrepresent_first_choice_for_men_on_strict_domain
    {M W : Type*} [DecidableEq M]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    paper_strict_marriage_domain val_m val_w →
      ∀ (m : M) (report_m : W → ℝ),
        paper_strict_marriage_domain (Function.update val_m m report_m) val_w →
        ∃ faithful_report_m : W → ℝ,
          paper_strict_marriage_domain
              (Function.update val_m m faithful_report_m) val_w ∧
            paper_man_report_preserves_first_choice val_m m faithful_report_m ∧
            paper_matching_valM val_m m
                ((mechanism
                  (Function.update val_m m report_m) val_w).m_match m) ≤
              paper_matching_valM val_m m
                ((mechanism
                  (Function.update val_m m faithful_report_m) val_w).m_match m)

/-- Paper Definition: A stable matching procedure always returns a stable matching. -/
def paper_stable_matching_procedure {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ val_m val_w, paper_is_stable val_m val_w (mechanism val_m val_w)

/-- Paper Definition: a feasible marriage-problem outcome matches every agent. -/
def paper_is_complete_matching {M W : Type*} (mu : Assignment M W) : Prop :=
  (∀ m, ∃ w, mu.m_match m = some w) ∧
    (∀ w, ∃ m, mu.w_match w = some m)

/-- Paper Definition: outcome `nu` weakly Pareto-dominates `mu`. -/
def paper_pareto_dominates {M W : Type*} (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (nu mu : Assignment M W) : Prop :=
  (∀ m, paper_matching_valM val_m m (mu.m_match m) ≤
    paper_matching_valM val_m m (nu.m_match m)) ∧
  (∀ w, paper_matching_valW val_w w (mu.w_match w) ≤
    paper_matching_valW val_w w (nu.w_match w))

/-- Paper Definition: outcome `nu` Pareto-improves on `mu` for at least one agent. -/
def paper_pareto_improves {M W : Type*} (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (nu mu : Assignment M W) : Prop :=
  paper_pareto_dominates val_m val_w nu mu ∧
    ((∃ m, paper_matching_valM val_m m (mu.m_match m) <
      paper_matching_valM val_m m (nu.m_match m)) ∨
    (∃ w, paper_matching_valW val_w w (mu.w_match w) <
      paper_matching_valW val_w w (nu.w_match w)))

/-- Paper Definition: a complete outcome is Pareto optimal among complete outcomes. -/
def paper_is_pareto_optimal {M W : Type*} (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  paper_is_complete_matching mu ∧
    ¬ ∃ nu, paper_is_complete_matching nu ∧ paper_pareto_improves val_m val_w nu mu

/-- Paper Definition: an outcome is strictly better for every man than `mu`. -/
def paper_strictly_better_for_all_men {M W : Type*} (val_m : M → W → ℝ)
    (nu mu : Assignment M W) : Prop :=
  ∀ m, paper_matching_valM val_m m (mu.m_match m) <
    paper_matching_valM val_m m (nu.m_match m)

/--
Paper Definition: Roth's weak Pareto-optimality conclusion for the men. No
feasible outcome is strictly preferred by every man to `mu`.
-/
def paper_weakly_pareto_optimal_for_men {M W : Type*} (val_m : M → W → ℝ)
    (mu : Assignment M W) : Prop :=
  ¬ ∃ nu, paper_is_complete_matching nu ∧
    paper_strictly_better_for_all_men val_m nu mu

/-- Paper Definition: an efficient matching procedure always returns a Pareto-optimal outcome. -/
def paper_efficient_matching_procedure {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ val_m val_w, paper_is_pareto_optimal val_m val_w (mechanism val_m val_w)

/-- Paper Definition: truthful revelation is dominant for every agent. -/
def paper_truthful_for_all_agents {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  paper_truthful_for_men mechanism ∧ paper_truthful_for_women mechanism

/-- A procedure ignores women's reports when only the men's reports determine the output. -/
def paper_ignores_women_reports {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ val_m val_w val_w', mechanism val_m val_w' = mechanism val_m val_w

/-- If women's reports do not affect a procedure, truth-telling is dominant for women. -/
theorem paper_truthful_for_women_of_ignores_women_reports
    {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W)
    (hignore : paper_ignores_women_reports mechanism) :
    paper_truthful_for_women mechanism := by
  intro val_m val_w w report_w
  rw [hignore val_m val_w (Function.update val_w w report_w)]

/-! ## 2) Main Theorems -/

/-- Theorem 1: The Deferred Acceptance algorithm produces a stable matching. -/
theorem paper_da_is_stable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    paper_is_stable val_m val_w (deferredAcceptance val_m val_w) := by
  rw [paper_is_stable_eq]
  exact da_produces_stable_matching val_m val_w

/--
Theorem 1: the set of stable outcomes is nonempty, using the
deferred-acceptance output.
-/
theorem paper_roth82_theorem1_stable_outcome_exists
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    ∃ mu : Assignment M W, paper_is_stable val_m val_w mu := by
  exact ⟨deferredAcceptance val_m val_w, paper_da_is_stable val_m val_w⟩

/--
Theorem 1 on Roth's equal-size strict marriage domain: deferred acceptance
produces a stable complete marriage outcome.
-/
theorem paper_roth82_theorem1_stable_complete_outcome_exists_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    ∃ mu : Assignment M W,
      paper_is_stable val_m val_w mu ∧ paper_is_complete_matching mu := by
  rcases hdomain with ⟨_hstrictM, _hstrictW, hposM, hposW⟩
  refine ⟨deferredAcceptance val_m val_w, paper_da_is_stable val_m val_w, ?_⟩
  exact deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
    val_m val_w hcard ⟨hposM, hposW⟩

/-- Theorem 2: The Men-Proposing Deferred Acceptance algorithm produces a men-optimal stable matching. -/
theorem paper_da_is_men_optimal {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaIsMenOptimalCertificate val_m val_w) :
    paper_is_men_optimal val_m val_w (deferredAcceptance val_m val_w) := by
  unfold paper_is_men_optimal
  rw [paper_is_stable_eq]
  refine ⟨da_produces_stable_matching val_m val_w, ?_⟩
  intro mu' hstable m
  rw [paper_is_stable_eq] at hstable
  exact hcert mu' hstable m

/--
Theorem 2 compatibility wrapper: the men-proposing deferred-acceptance
outcome is the men-optimal stable outcome once the men-optimality certificate
is supplied.
-/
theorem paper_roth82_theorem2_men_optimal_stable_outcome
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaIsMenOptimalCertificate val_m val_w) :
    ∃ mu : Assignment M W, paper_is_men_optimal val_m val_w mu := by
  exact ⟨deferredAcceptance val_m val_w,
    paper_da_is_men_optimal val_m val_w hcert⟩

/--
Women-proposing deferred acceptance, represented on the original `(M, W)` sides
by running deferred acceptance with the roles reversed and then swapping the
resulting assignment back.
-/
noncomputable def paper_women_deferredAcceptance
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W :=
  (deferredAcceptance (M := W) (W := M) val_w val_m).swap

/-- Certificate for the women-optimality of women-proposing deferred acceptance. -/
def DaIsWomenOptimalCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  DaIsMenOptimalCertificate (M := W) (W := M) val_w val_m

/-- Women-proposing deferred acceptance produces a stable matching. -/
theorem paper_women_da_is_stable
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    paper_is_stable val_m val_w (paper_women_deferredAcceptance val_m val_w) := by
  rw [paper_is_stable_eq, paper_women_deferredAcceptance]
  exact (isStable_swap_iff val_w val_m
    (deferredAcceptance (M := W) (W := M) val_w val_m)).2
    (da_produces_stable_matching val_w val_m)

/-- Theorem 2: The women-proposing deferred-acceptance algorithm produces a women-optimal stable matching. -/
theorem paper_da_is_women_optimal
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaIsWomenOptimalCertificate val_m val_w) :
    paper_is_women_optimal val_m val_w (paper_women_deferredAcceptance val_m val_w) := by
  unfold paper_is_women_optimal
  refine ⟨paper_women_da_is_stable val_m val_w, ?_⟩
  intro mu' hstable w
  rw [paper_is_stable_eq] at hstable
  have hswapStable : IsStable val_w val_m mu'.swap :=
    (isStable_swap_iff val_m val_w mu').2 hstable
  have hopt := hcert mu'.swap hswapStable w
  simpa [paper_matching_valW, paper_women_deferredAcceptance, valM, valW] using hopt

/--
Theorem 2 compatibility wrapper: the women-proposing
deferred-acceptance outcome is the women-optimal stable outcome once the
role-reversed optimality certificate is supplied.
-/
theorem paper_roth82_theorem2_women_optimal_stable_outcome
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaIsWomenOptimalCertificate val_m val_w) :
    ∃ mu : Assignment M W, paper_is_women_optimal val_m val_w mu := by
  exact ⟨paper_women_deferredAcceptance val_m val_w,
    paper_da_is_women_optimal val_m val_w hcert⟩

/--
Theorem 2 compatibility wrapper: both sides have an optimal stable outcome, with
the men-optimal outcome obtained by men-proposing DA and the women-optimal
outcome obtained by the role-reversed DA procedure once the certificates are
supplied.
-/
theorem paper_roth82_theorem2_optimal_stable_outcomes
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hmenOptimal : DaIsMenOptimalCertificate val_m val_w)
    (hwomenOptimal : DaIsWomenOptimalCertificate val_m val_w) :
    (∃ mu : Assignment M W, paper_is_men_optimal val_m val_w mu) ∧
      (∃ mu : Assignment M W, paper_is_women_optimal val_m val_w mu) := by
  exact ⟨paper_roth82_theorem2_men_optimal_stable_outcome
      val_m val_w hmenOptimal,
    paper_roth82_theorem2_women_optimal_stable_outcome
      val_m val_w hwomenOptimal⟩

/--
Theorem 2, men side on Roth's strict marriage domain: men-proposing deferred
acceptance returns the men-optimal stable outcome.
-/
theorem paper_da_is_men_optimal_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    paper_is_men_optimal val_m val_w (deferredAcceptance val_m val_w) := by
  rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
  exact paper_da_is_men_optimal val_m val_w
    (AppliedModelingLib.Matching.da_is_men_optimal_of_strict_preferences
      val_m val_w hstrictM hstrictW ⟨hposM, hposW⟩)

/--
Theorem 2, women side on Roth's strict marriage domain: women-proposing deferred
acceptance returns the women-optimal stable outcome.
-/
theorem paper_da_is_women_optimal_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    paper_is_women_optimal val_m val_w
      (paper_women_deferredAcceptance val_m val_w) := by
  rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
  exact paper_da_is_women_optimal val_m val_w
    (AppliedModelingLib.Matching.da_is_men_optimal_of_strict_preferences
      val_w val_m hstrictW hstrictM ⟨hposW, hposM⟩)

/--
Theorem 2 on Roth's strict marriage domain: both the men-optimal and
women-optimal stable outcomes exist.
-/
theorem paper_roth82_theorem2_optimal_stable_outcomes_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    (∃ mu : Assignment M W, paper_is_men_optimal val_m val_w mu) ∧
      (∃ mu : Assignment M W, paper_is_women_optimal val_m val_w mu) := by
  exact ⟨⟨deferredAcceptance val_m val_w,
      paper_da_is_men_optimal_on_strict_marriage_domain val_m val_w hdomain⟩,
    ⟨paper_women_deferredAcceptance val_m val_w,
      paper_da_is_women_optimal_on_strict_marriage_domain val_m val_w hdomain⟩⟩

/-! ## 3) Theorem 3 counterexample profile -/

/-- The three men and three women in Roth's Theorem 3 counterexample. -/
abbrev Theorem3Agent := Fin 3

/-- Case split helper for the finite `3`-agent counterexample. -/
private theorem theorem3Option_cases (x : Option Theorem3Agent) :
    x = none ∨ x = some 0 ∨ x = some 1 ∨ x = some 2 := by
  cases x with
  | none =>
      exact Or.inl rfl
  | some w =>
      fin_cases w
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))

/--
Theorem 3 profile `P`, men's preferences:
`m₁: w₂ > w₁ > w₃`, `m₂: w₁ > w₂ > w₃`,
`m₃: w₁ > w₂ > w₃`.
-/
def theorem3MenProfile : Theorem3Agent → Theorem3Agent → ℝ := fun m w =>
  if m.1 = 0 then
    if w.1 = 1 then 3 else if w.1 = 0 then 2 else 1
  else if m.1 = 1 then
    if w.1 = 0 then 3 else if w.1 = 1 then 2 else 1
  else
    if w.1 = 0 then 3 else if w.1 = 1 then 2 else 1

/--
Theorem 3 profile `P`, women's preferences:
`w₁: m₁ > m₃ > m₂`, `w₂: m₃ > m₁ > m₂`,
`w₃: m₁ > m₂ > m₃`.
-/
def theorem3WomenProfile : Theorem3Agent → Theorem3Agent → ℝ := fun w m =>
  if w.1 = 0 then
    if m.1 = 0 then 3 else if m.1 = 2 then 2 else 1
  else if w.1 = 1 then
    if m.1 = 2 then 3 else if m.1 = 0 then 2 else 1
  else
    if m.1 = 0 then 3 else if m.1 = 1 then 2 else 1

/-- Roth's `P'(w₁)` report: `m₁ > m₂ > m₃`. -/
def theorem3Woman0PrimeReport : Theorem3Agent → ℝ := fun m =>
  if m.1 = 0 then 3 else if m.1 = 1 then 2 else 1

/-- The profile `P'`, differing from `P` only in woman `w₁`'s report. -/
def theorem3WomenProfilePrime : Theorem3Agent → Theorem3Agent → ℝ :=
  Function.update theorem3WomenProfile 0 theorem3Woman0PrimeReport

/-- Roth's `P''(m₁)` report: `w₂ > w₃ > w₁`. -/
def theorem3Man0DoublePrimeReport : Theorem3Agent → ℝ := fun w =>
  if w.1 = 1 then 3 else if w.1 = 2 then 2 else 1

/-- The profile `P''`, differing from `P` only in man `m₁`'s report. -/
def theorem3MenProfileDoublePrime : Theorem3Agent → Theorem3Agent → ℝ :=
  Function.update theorem3MenProfile 0 theorem3Man0DoublePrimeReport

theorem theorem3_base_strict_preference_profile :
    paper_strict_preference_profile theorem3MenProfile theorem3WomenProfile := by
  constructor
  · intro m w w' h
    fin_cases m <;> fin_cases w <;> fin_cases w' <;>
      simp [theorem3MenProfile] at h ⊢
  · intro w m m' h
    fin_cases w <;> fin_cases m <;> fin_cases m' <;>
      simp [theorem3WomenProfile] at h ⊢

theorem theorem3_woman_prime_strict_preference_profile :
    paper_strict_preference_profile theorem3MenProfile theorem3WomenProfilePrime := by
  constructor
  · exact theorem3_base_strict_preference_profile.1
  · intro w m m' h
    fin_cases w <;> fin_cases m <;> fin_cases m' <;>
      simp [theorem3WomenProfilePrime, theorem3WomenProfile,
        theorem3Woman0PrimeReport] at h ⊢

theorem theorem3_man_double_prime_strict_preference_profile :
    paper_strict_preference_profile theorem3MenProfileDoublePrime theorem3WomenProfile := by
  constructor
  · intro m w w' h
    fin_cases m <;> fin_cases w <;> fin_cases w' <;>
      simp [theorem3MenProfileDoublePrime, theorem3MenProfile,
        theorem3Man0DoublePrimeReport] at h ⊢
  · exact theorem3_base_strict_preference_profile.2

theorem theorem3_base_strict_marriage_domain :
    paper_strict_marriage_domain theorem3MenProfile theorem3WomenProfile := by
  refine ⟨theorem3_base_strict_preference_profile.1,
    theorem3_base_strict_preference_profile.2, ?_, ?_⟩
  · intro m w
    fin_cases m <;> fin_cases w <;> norm_num [theorem3MenProfile]
  · intro w m
    fin_cases w <;> fin_cases m <;> norm_num [theorem3WomenProfile]

theorem theorem3_woman_prime_strict_marriage_domain :
    paper_strict_marriage_domain theorem3MenProfile theorem3WomenProfilePrime := by
  refine ⟨theorem3_woman_prime_strict_preference_profile.1,
    theorem3_woman_prime_strict_preference_profile.2, ?_, ?_⟩
  · intro m w
    fin_cases m <;> fin_cases w <;> norm_num [theorem3MenProfile]
  · intro w m
    fin_cases w <;> fin_cases m <;>
      norm_num [theorem3WomenProfilePrime, theorem3WomenProfile,
        theorem3Woman0PrimeReport]

theorem theorem3_man_double_prime_strict_marriage_domain :
    paper_strict_marriage_domain theorem3MenProfileDoublePrime theorem3WomenProfile := by
  refine ⟨theorem3_man_double_prime_strict_preference_profile.1,
    theorem3_man_double_prime_strict_preference_profile.2, ?_, ?_⟩
  · intro m w
    fin_cases m <;> fin_cases w <;>
      norm_num [theorem3MenProfileDoublePrime, theorem3MenProfile,
        theorem3Man0DoublePrimeReport]
  · intro w m
    fin_cases w <;> fin_cases m <;> norm_num [theorem3WomenProfile]

/--
Roth's stable outcome `x`:
`(m₁,w₂), (m₂,w₃), (m₃,w₁)`.
-/
def theorem3OutcomeX : Assignment Theorem3Agent Theorem3Agent where
  m_match m := if m.1 = 0 then some 1 else if m.1 = 1 then some 2 else some 0
  w_match w := if w.1 = 0 then some 2 else if w.1 = 1 then some 0 else some 1
  consistent_m := by
    intro m w
    fin_cases m <;> fin_cases w <;> decide

/--
Roth's stable outcome `y`:
`(m₁,w₁), (m₂,w₃), (m₃,w₂)`.
-/
def theorem3OutcomeY : Assignment Theorem3Agent Theorem3Agent where
  m_match m := if m.1 = 0 then some 0 else if m.1 = 1 then some 2 else some 1
  w_match w := if w.1 = 0 then some 0 else if w.1 = 1 then some 2 else some 1
  consistent_m := by
    intro m w
    fin_cases m <;> fin_cases w <;> decide

/-- In Roth's base profile `P`, the listed outcome `x` is stable. -/
theorem theorem3OutcomeX_stable_base :
    paper_is_stable theorem3MenProfile theorem3WomenProfile theorem3OutcomeX := by
  rw [paper_is_stable_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro m
    fin_cases m <;>
      norm_num [valM, theorem3OutcomeX, theorem3MenProfile]
  · intro w
    fin_cases w <;>
      norm_num [valW, theorem3OutcomeX, theorem3WomenProfile]
  · intro m w hm hw
    fin_cases m <;> fin_cases w <;>
      simp [valM, valW, theorem3OutcomeX, theorem3MenProfile,
        theorem3WomenProfile] at hm hw <;> try linarith

/-- In Roth's base profile `P`, the listed outcome `y` is stable. -/
theorem theorem3OutcomeY_stable_base :
    paper_is_stable theorem3MenProfile theorem3WomenProfile theorem3OutcomeY := by
  rw [paper_is_stable_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro m
    fin_cases m <;>
      norm_num [valM, theorem3OutcomeY, theorem3MenProfile]
  · intro w
    fin_cases w <;>
      norm_num [valW, theorem3OutcomeY, theorem3WomenProfile]
  · intro m w hm hw
    fin_cases m <;> fin_cases w <;>
      simp [valM, valW, theorem3OutcomeY, theorem3MenProfile,
        theorem3WomenProfile] at hm hw <;> try linarith

/-- In the woman-misreport profile `P'`, Roth's outcome `y` is stable. -/
theorem theorem3OutcomeY_stable_woman_prime :
    paper_is_stable theorem3MenProfile theorem3WomenProfilePrime theorem3OutcomeY := by
  rw [paper_is_stable_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro m
    fin_cases m <;>
      norm_num [valM, theorem3OutcomeY, theorem3MenProfile]
  · intro w
    fin_cases w <;>
      norm_num [valW, theorem3OutcomeY, theorem3WomenProfilePrime,
        theorem3WomenProfile, theorem3Woman0PrimeReport]
  · intro m w hm hw
    fin_cases m <;> fin_cases w <;>
      simp [valM, valW, theorem3OutcomeY, theorem3MenProfile,
        theorem3WomenProfilePrime, theorem3WomenProfile,
        theorem3Woman0PrimeReport] at hm hw <;> try linarith

/-- In the man-misreport profile `P''`, Roth's outcome `x` is stable. -/
theorem theorem3OutcomeX_stable_man_double_prime :
    paper_is_stable theorem3MenProfileDoublePrime theorem3WomenProfile theorem3OutcomeX := by
  rw [paper_is_stable_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro m
    fin_cases m <;>
      norm_num [valM, theorem3OutcomeX, theorem3MenProfileDoublePrime,
        theorem3MenProfile, theorem3Man0DoublePrimeReport]
  · intro w
    fin_cases w <;>
      norm_num [valW, theorem3OutcomeX, theorem3WomenProfile]
  · intro m w hm hw
    fin_cases m <;> fin_cases w <;>
      simp [valM, valW, theorem3OutcomeX, theorem3MenProfileDoublePrime,
        theorem3MenProfile, theorem3Man0DoublePrimeReport,
        theorem3WomenProfile] at hm hw <;> try linarith

/-- A consistent assignment cannot match two distinct men to the same woman. -/
private theorem theorem3_no_duplicate_woman
    {mu : Assignment Theorem3Agent Theorem3Agent}
    {m m' w : Theorem3Agent} (hneq : m ≠ m')
    (hm : mu.m_match m = some w) (hm' : mu.m_match m' = some w) : False := by
  have hw : mu.w_match w = some m :=
    Assignment.w_match_eq_some_of_m_match_eq_some hm
  have hw' : mu.w_match w = some m' :=
    Assignment.w_match_eq_some_of_m_match_eq_some hm'
  have hsome : some m = some m' := hw.symm.trans hw'
  cases hsome
  exact hneq rfl

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.cdot false
/-- At Roth's base profile `P`, the only stable outcomes are `x` and `y`. -/
theorem theorem3_stable_base_eq_x_or_y
    (mu : Assignment Theorem3Agent Theorem3Agent)
    (hstable : paper_is_stable theorem3MenProfile theorem3WomenProfile mu) :
    mu = theorem3OutcomeX ∨ mu = theorem3OutcomeY := by
  have hblock := hstable.2.2
  rcases theorem3Option_cases (mu.m_match 0) with hm0 | hm0 | hm0 | hm0
  · rcases theorem3Option_cases (mu.m_match 1) with hm1 | hm1 | hm1 | hm1
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 0)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      · exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 1)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      · exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 2)
          (by decide) (by simpa using hm1) (by simpa using hm2)
  · rcases theorem3Option_cases (mu.m_match 1) with hm1 | hm1 | hm1 | hm1
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        have hw : mu.w_match 1 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      · exfalso
        have hw : mu.w_match 2 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 2
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        have hw : mu.w_match 1 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm1)
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        have hw : mu.w_match 1 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 1)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      · exfalso
        have hw : mu.w_match 1 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        have hw : mu.w_match 1 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      · right
        apply Assignment.ext_of_m_match
        intro m
        fin_cases m <;> simp [theorem3OutcomeY, hm0, hm1, hm2]
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 2)
          (by decide) (by simpa using hm1) (by simpa using hm2)
  · rcases theorem3Option_cases (mu.m_match 1) with hm1 | hm1 | hm1 | hm1
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        have hw : mu.w_match 2 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 2
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      · exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 2 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 0)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      · exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 2 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm1)
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · left
        apply Assignment.ext_of_m_match
        intro m
        fin_cases m <;> simp [theorem3OutcomeX, hm0, hm1, hm2]
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 2)
          (by decide) (by simpa using hm1) (by simpa using hm2)
  · rcases theorem3Option_cases (mu.m_match 1) with hm1 | hm1 | hm1 | hm1
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm2)
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 0)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      · exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm2)
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 1)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm2)
    · rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      · exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm1)


/-- In the woman-misreport profile `P'`, `y` is the unique stable outcome. -/
theorem theorem3_stable_woman_prime_eq_y
    (mu : Assignment Theorem3Agent Theorem3Agent)
    (hstable : paper_is_stable theorem3MenProfile theorem3WomenProfilePrime mu) :
    mu = theorem3OutcomeY := by
  have hblock := hstable.2.2
  rcases theorem3Option_cases (mu.m_match 0) with hm0 | hm0 | hm0 | hm0
  ·
    rcases theorem3Option_cases (mu.m_match 1) with hm1 | hm1 | hm1 | hm1
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 0)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 1)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 2)
          (by decide) (by simpa using hm1) (by simpa using hm2)
  ·
    rcases theorem3Option_cases (mu.m_match 1) with hm1 | hm1 | hm1 | hm1
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 1 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 2 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 2
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 1 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm1)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 1 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 1)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 1 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 1 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      ·
        apply Assignment.ext_of_m_match
        intro m
        fin_cases m <;> simp [theorem3OutcomeY, hm0, hm1, hm2]
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 2)
          (by decide) (by simpa using hm1) (by simpa using hm2)
  ·
    rcases theorem3Option_cases (mu.m_match 1) with hm1 | hm1 | hm1 | hm1
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 1 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 1 = some 0 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm0)
        exact hblock 2 1
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 0)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 1 = some 0 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm0)
        exact hblock 2 1
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm1)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 1 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 2)
          (by decide) (by simpa using hm1) (by simpa using hm2)
  ·
    rcases theorem3Option_cases (mu.m_match 1) with hm1 | hm1 | hm1 | hm1
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm2)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 0)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm2)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfile, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 1)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm2)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm1)

/-- In the man-misreport profile `P''`, `x` is the unique stable outcome. -/
theorem theorem3_stable_man_double_prime_eq_x
    (mu : Assignment Theorem3Agent Theorem3Agent)
    (hstable : paper_is_stable theorem3MenProfileDoublePrime theorem3WomenProfile mu) :
    mu = theorem3OutcomeX := by
  have hblock := hstable.2.2
  rcases theorem3Option_cases (mu.m_match 0) with hm0 | hm0 | hm0 | hm0
  ·
    rcases theorem3Option_cases (mu.m_match 1) with hm1 | hm1 | hm1 | hm1
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 0)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 1)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = some 2 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm2)
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 2)
          (by decide) (by simpa using hm1) (by simpa using hm2)
  ·
    rcases theorem3Option_cases (mu.m_match 1) with hm1 | hm1 | hm1 | hm1
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 1 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 2 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 2
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 1 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm1)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 1 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 1)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 1 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 1 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 0)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 2 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 2
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 2)
          (by decide) (by simpa using hm1) (by simpa using hm2)
  ·
    rcases theorem3Option_cases (mu.m_match 1) with hm1 | hm1 | hm1 | hm1
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 2 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 2
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 2 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 0)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 2 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm1)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        apply Assignment.ext_of_m_match
        intro m
        fin_cases m <;> simp [theorem3OutcomeX, hm0, hm1, hm2]
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 1)
          (by decide) (by simpa using hm0) (by simpa using hm2)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 2)
          (by decide) (by simpa using hm1) (by simpa using hm2)
  ·
    rcases theorem3Option_cases (mu.m_match 1) with hm1 | hm1 | hm1 | hm1
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 1 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 1 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 0 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 1 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm2)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 1 = none :=
          Assignment.w_match_eq_none_of_forall_m_match_ne_some
            (by intro m; fin_cases m <;> simp [hm0, hm1, hm2])
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 0)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      ·
        exfalso
        have hw : mu.w_match 0 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 2 0
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm2)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        have hw : mu.w_match 1 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        have hw : mu.w_match 1 = some 1 :=
          Assignment.w_match_eq_some_of_m_match_eq_some (by simpa using hm1)
        exact hblock 0 1
          (by simp [paper_matching_valM, theorem3MenProfileDoublePrime, theorem3MenProfile, theorem3Man0DoublePrimeReport, hm0, hm1, hm2] <;> norm_num)
          (by simp [paper_matching_valW, theorem3WomenProfile, hw] <;> norm_num)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 1) (m' := 2) (w := 1)
          (by decide) (by simpa using hm1) (by simpa using hm2)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 2) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm2)
    ·
      rcases theorem3Option_cases (mu.m_match 2) with hm2 | hm2 | hm2 | hm2
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm1)
      ·
        exfalso
        exact theorem3_no_duplicate_woman (mu := mu) (m := 0) (m' := 1) (w := 2)
          (by decide) (by simpa using hm0) (by simpa using hm1)
set_option linter.unusedSimpArgs true
set_option linter.unusedTactic true
set_option linter.unreachableTactic true
set_option linter.unnecessarySeqFocus true
set_option linter.style.cdot true

/--
The finite stable-set behavior from Roth's Theorem 3 proof.

The paper states that at `P` the stable set is `{x,y}`, at `P'` the unique
stable outcome is `y`, and at `P''` the unique stable outcome is `x`. This
structure records exactly the behavior of a stable procedure on those three
profiles, separating the finite enumeration from the manipulation argument.
-/
structure Theorem3CounterexampleStableBehavior
    (mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent) : Prop where
  base :
    mechanism theorem3MenProfile theorem3WomenProfile = theorem3OutcomeX ∨
      mechanism theorem3MenProfile theorem3WomenProfile = theorem3OutcomeY
  woman_prime :
    mechanism theorem3MenProfile theorem3WomenProfilePrime = theorem3OutcomeY
  man_double_prime :
    mechanism theorem3MenProfileDoublePrime theorem3WomenProfile = theorem3OutcomeX

/-- A stable procedure has exactly Roth's three-profile counterexample behavior. -/
theorem theorem3_counterexample_stable_behavior_of_stable_procedure
    (mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent)
    (hstableProc : paper_stable_matching_procedure mechanism) :
    Theorem3CounterexampleStableBehavior mechanism := by
  refine ⟨?_, ?_, ?_⟩
  · exact theorem3_stable_base_eq_x_or_y
      (mechanism theorem3MenProfile theorem3WomenProfile)
      (hstableProc theorem3MenProfile theorem3WomenProfile)
  · exact theorem3_stable_woman_prime_eq_y
      (mechanism theorem3MenProfile theorem3WomenProfilePrime)
      (hstableProc theorem3MenProfile theorem3WomenProfilePrime)
  · exact theorem3_stable_man_double_prime_eq_x
      (mechanism theorem3MenProfileDoublePrime theorem3WomenProfile)
      (hstableProc theorem3MenProfileDoublePrime theorem3WomenProfile)

/-- A procedure stable on strict profiles has Roth's three-profile counterexample behavior. -/
theorem theorem3_counterexample_stable_behavior_of_stable_procedure_on_strict_profiles
    (mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent)
    (hstableProc : paper_stable_matching_procedure_on_strict_profiles mechanism) :
    Theorem3CounterexampleStableBehavior mechanism := by
  refine ⟨?_, ?_, ?_⟩
  · exact theorem3_stable_base_eq_x_or_y
      (mechanism theorem3MenProfile theorem3WomenProfile)
      (hstableProc theorem3MenProfile theorem3WomenProfile
        theorem3_base_strict_preference_profile)
  · exact theorem3_stable_woman_prime_eq_y
      (mechanism theorem3MenProfile theorem3WomenProfilePrime)
      (hstableProc theorem3MenProfile theorem3WomenProfilePrime
        theorem3_woman_prime_strict_preference_profile)
  · exact theorem3_stable_man_double_prime_eq_x
      (mechanism theorem3MenProfileDoublePrime theorem3WomenProfile)
      (hstableProc theorem3MenProfileDoublePrime theorem3WomenProfile
        theorem3_man_double_prime_strict_preference_profile)

/-- A stable procedure on the complete strict marriage domain has Roth's behavior. -/
theorem theorem3_counterexample_stable_behavior_of_stable_procedure_on_strict_marriage_domain
    (mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent)
    (hstableProc : paper_stable_matching_procedure_on_strict_marriage_domain mechanism) :
    Theorem3CounterexampleStableBehavior mechanism := by
  refine ⟨?_, ?_, ?_⟩
  · exact theorem3_stable_base_eq_x_or_y
      (mechanism theorem3MenProfile theorem3WomenProfile)
      (hstableProc theorem3MenProfile theorem3WomenProfile
        theorem3_base_strict_marriage_domain)
  · exact theorem3_stable_woman_prime_eq_y
      (mechanism theorem3MenProfile theorem3WomenProfilePrime)
      (hstableProc theorem3MenProfile theorem3WomenProfilePrime
        theorem3_woman_prime_strict_marriage_domain)
  · exact theorem3_stable_man_double_prime_eq_x
      (mechanism theorem3MenProfileDoublePrime theorem3WomenProfile)
      (hstableProc theorem3MenProfileDoublePrime theorem3WomenProfile
        theorem3_man_double_prime_strict_marriage_domain)

/--
Theorem 3 manipulation contradiction from Roth's finite counterexample.

Once a procedure has the stable-set behavior stated in the paper's counterexample,
it cannot be truthful for both sides: if it selects `x` at the base profile, `w₁`
profits by reporting `P'(w₁)`; if it selects `y`, `m₁` profits by reporting
`P''(m₁)`.
-/
theorem paper_roth82_theorem3_counterexample_blocks_two_sided_truthfulness
    (mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent)
    (hbehavior : Theorem3CounterexampleStableBehavior mechanism) :
    ¬ (paper_truthful_for_men mechanism ∧ paper_truthful_for_women mechanism) := by
  rintro ⟨hmenTruth, hwomenTruth⟩
  rcases hbehavior.base with hbase | hbase
  · have htruth := hwomenTruth theorem3MenProfile theorem3WomenProfile 0
      theorem3Woman0PrimeReport
    rw [show Function.update theorem3WomenProfile 0 theorem3Woman0PrimeReport =
        theorem3WomenProfilePrime from rfl, hbehavior.woman_prime, hbase] at htruth
    norm_num [paper_matching_valW, theorem3WomenProfile, theorem3OutcomeX,
      theorem3OutcomeY] at htruth
  · have htruth := hmenTruth theorem3MenProfile theorem3WomenProfile 0
      theorem3Man0DoublePrimeReport
    rw [show Function.update theorem3MenProfile 0 theorem3Man0DoublePrimeReport =
        theorem3MenProfileDoublePrime from rfl, hbehavior.man_double_prime, hbase] at htruth
    norm_num [paper_matching_valM, theorem3MenProfile, theorem3OutcomeX,
      theorem3OutcomeY] at htruth

/--
Theorem 3 manipulation contradiction restricted to strict true and reported
preference profiles.
-/
theorem paper_roth82_theorem3_counterexample_blocks_two_sided_truthfulness_on_strict_profiles
    (mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent)
    (hbehavior : Theorem3CounterexampleStableBehavior mechanism) :
    ¬ (paper_truthful_for_men_on_strict_profiles mechanism ∧
      paper_truthful_for_women_on_strict_profiles mechanism) := by
  rintro ⟨hmenTruth, hwomenTruth⟩
  rcases hbehavior.base with hbase | hbase
  · have htruth := hwomenTruth theorem3MenProfile theorem3WomenProfile
      theorem3_base_strict_preference_profile 0 theorem3Woman0PrimeReport
      theorem3_woman_prime_strict_preference_profile
    rw [show Function.update theorem3WomenProfile 0 theorem3Woman0PrimeReport =
        theorem3WomenProfilePrime from rfl, hbehavior.woman_prime, hbase] at htruth
    norm_num [paper_matching_valW, theorem3WomenProfile, theorem3OutcomeX,
      theorem3OutcomeY] at htruth
  · have htruth := hmenTruth theorem3MenProfile theorem3WomenProfile
      theorem3_base_strict_preference_profile 0 theorem3Man0DoublePrimeReport
      theorem3_man_double_prime_strict_preference_profile
    rw [show Function.update theorem3MenProfile 0 theorem3Man0DoublePrimeReport =
        theorem3MenProfileDoublePrime from rfl, hbehavior.man_double_prime, hbase] at htruth
    norm_num [paper_matching_valM, theorem3MenProfile, theorem3OutcomeX,
      theorem3OutcomeY] at htruth

/--
Theorem 3 contradiction on the complete strict marriage domain, including the
source requirement that every possible partner is acceptable.
-/
theorem paper_roth82_theorem3_counterexample_blocks_two_sided_truthfulness_on_strict_marriage_domain
    (mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent)
    (hbehavior : Theorem3CounterexampleStableBehavior mechanism) :
    ¬ (paper_truthful_for_men_on_strict_marriage_domain mechanism ∧
      paper_truthful_for_women_on_strict_marriage_domain mechanism) := by
  rintro ⟨hmenTruth, hwomenTruth⟩
  rcases hbehavior.base with hbase | hbase
  · have htruth := hwomenTruth theorem3MenProfile theorem3WomenProfile
      theorem3_base_strict_marriage_domain 0 theorem3Woman0PrimeReport
      theorem3_woman_prime_strict_marriage_domain
    rw [show Function.update theorem3WomenProfile 0 theorem3Woman0PrimeReport =
        theorem3WomenProfilePrime from rfl, hbehavior.woman_prime, hbase] at htruth
    norm_num [paper_matching_valW, theorem3WomenProfile, theorem3OutcomeX,
      theorem3OutcomeY] at htruth
  · have htruth := hmenTruth theorem3MenProfile theorem3WomenProfile
      theorem3_base_strict_marriage_domain 0 theorem3Man0DoublePrimeReport
      theorem3_man_double_prime_strict_marriage_domain
    rw [show Function.update theorem3MenProfile 0 theorem3Man0DoublePrimeReport =
        theorem3MenProfileDoublePrime from rfl, hbehavior.man_double_prime, hbase] at htruth
    norm_num [paper_matching_valM, theorem3MenProfile, theorem3OutcomeX,
      theorem3OutcomeY] at htruth

/--
Theorem 3 counterexample, as a direct profitable-misreport statement. At the
base profile, either woman `w₁` profits by reporting `P'(w₁)`, or man `m₁`
profits by reporting `P''(m₁)`.
-/
theorem theorem3_counterexample_has_profitable_misreport
    (mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent)
    (hbehavior : Theorem3CounterexampleStableBehavior mechanism) :
    paper_profitable_woman_misreport mechanism theorem3MenProfile theorem3WomenProfile
        0 theorem3Woman0PrimeReport ∨
      paper_profitable_man_misreport mechanism theorem3MenProfile theorem3WomenProfile
        0 theorem3Man0DoublePrimeReport := by
  rcases hbehavior.base with hbase | hbase
  · left
    rw [paper_profitable_woman_misreport,
      show Function.update theorem3WomenProfile 0 theorem3Woman0PrimeReport =
        theorem3WomenProfilePrime from rfl,
      hbehavior.woman_prime, hbase]
    norm_num [paper_matching_valW, theorem3WomenProfile, theorem3OutcomeX,
      theorem3OutcomeY]
  · right
    rw [paper_profitable_man_misreport,
      show Function.update theorem3MenProfile 0 theorem3Man0DoublePrimeReport =
        theorem3MenProfileDoublePrime from rfl,
      hbehavior.man_double_prime, hbase]
    norm_num [paper_matching_valM, theorem3MenProfile, theorem3OutcomeX,
      theorem3OutcomeY]

/--
Theorem 3 counterexample-behavior wrapper: no procedure satisfying Roth's
three-profile stable-set behavior can make truthful revelation dominant for both
men and women.
-/
theorem paper_roth82_theorem3_no_stable_truthful_procedure_from_counterexample :
    ¬ ∃ mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent,
      Theorem3CounterexampleStableBehavior mechanism ∧
        paper_truthful_for_men mechanism ∧ paper_truthful_for_women mechanism := by
  rintro ⟨mechanism, hbehavior, hmenTruth, hwomenTruth⟩
  exact paper_roth82_theorem3_counterexample_blocks_two_sided_truthfulness
    mechanism hbehavior ⟨hmenTruth, hwomenTruth⟩

/--
Theorem 3: no stable matching procedure on Roth's three-by-three counterexample
domain makes truthful revelation dominant for both men and women.
-/
theorem paper_roth82_theorem3_no_stable_truthful_procedure :
    ¬ ∃ mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent,
      paper_stable_matching_procedure mechanism ∧
        paper_truthful_for_men mechanism ∧ paper_truthful_for_women mechanism := by
  rintro ⟨mechanism, hstableProc, hmenTruth, hwomenTruth⟩
  exact paper_roth82_theorem3_counterexample_blocks_two_sided_truthfulness
    mechanism
    (theorem3_counterexample_stable_behavior_of_stable_procedure
      mechanism hstableProc)
    ⟨hmenTruth, hwomenTruth⟩

/--
Theorem 3 on the source strict-preference domain: no procedure that is stable on
strict reported profiles makes truthful revelation dominant for both sides on
strict true and reported profiles.
-/
theorem paper_roth82_theorem3_no_stable_truthful_procedure_on_strict_profiles :
    ¬ ∃ mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent,
      paper_stable_matching_procedure_on_strict_profiles mechanism ∧
        paper_truthful_for_men_on_strict_profiles mechanism ∧
          paper_truthful_for_women_on_strict_profiles mechanism := by
  rintro ⟨mechanism, hstableProc, hmenTruth, hwomenTruth⟩
  exact paper_roth82_theorem3_counterexample_blocks_two_sided_truthfulness_on_strict_profiles
    mechanism
    (theorem3_counterexample_stable_behavior_of_stable_procedure_on_strict_profiles
      mechanism hstableProc)
    ⟨hmenTruth, hwomenTruth⟩

/--
Theorem 3 on Roth's complete strict marriage domain: no stable procedure makes
truthful revelation dominant for both sides over all legal reports.
-/
theorem paper_roth82_theorem3_no_stable_truthful_procedure_on_strict_marriage_domain :
    ¬ ∃ mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent,
      paper_stable_matching_procedure_on_strict_marriage_domain mechanism ∧
        paper_truthful_for_men_on_strict_marriage_domain mechanism ∧
          paper_truthful_for_women_on_strict_marriage_domain mechanism := by
  rintro ⟨mechanism, hstableProc, hmenTruth, hwomenTruth⟩
  exact
    paper_roth82_theorem3_counterexample_blocks_two_sided_truthfulness_on_strict_marriage_domain
      mechanism
      (theorem3_counterexample_stable_behavior_of_stable_procedure_on_strict_marriage_domain
        mechanism hstableProc)
      ⟨hmenTruth, hwomenTruth⟩

/-! ## 4) Efficient strategyproof procedure -/

/--
Certificate for Roth's Theorem 4 construction.

The paper uses a fixed serial-dictatorship procedure: men choose in a fixed
order from the women not already chosen, and women's reports are ignored. The
certificate records the three properties of that construction that are needed
for the paper-facing theorem.
-/
structure Theorem4EfficientStrategyproofProcedureCertificate
    {M W : Type*} [DecidableEq M] [DecidableEq W] where
  mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W
  efficient : paper_efficient_matching_procedure mechanism
  truthful_men : paper_truthful_for_men mechanism
  ignores_women : paper_ignores_women_reports mechanism

/--
Theorem 4 compatibility serial-dictatorship wrapper: an efficient procedure
with dominant truthful revelation for every agent exists once the
serial-dictatorship certificate is supplied.
-/
theorem paper_roth82_theorem4_efficient_strategyproof_procedure_exists
    {M W : Type*} [DecidableEq M] [DecidableEq W]
    (hcert : Theorem4EfficientStrategyproofProcedureCertificate (M := M) (W := W)) :
    ∃ mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W,
      paper_efficient_matching_procedure mechanism ∧
        paper_truthful_for_all_agents mechanism := by
  refine ⟨hcert.mechanism, hcert.efficient, ?_, ?_⟩
  · exact hcert.truthful_men
  · exact paper_truthful_for_women_of_ignores_women_reports
      hcert.mechanism hcert.ignores_women

/-! ### Theorem 4 serial-dictatorship proof route -/

/-- Source-domain assumption: men have strict preferences over women. -/
def paper_men_strict_preferences {M W : Type*} (val_m : M → W → ℝ) : Prop :=
  ∀ m w w', val_m m w = val_m m w' → w = w'

/-- Two outcomes agree for every man earlier than `i` in the serial priority order. -/
def paper_priority_agree_before {n : ℕ} (i : Fin n)
    (mu nu : Assignment (Fin n) (Fin n)) : Prop :=
  ∀ j : Fin n, j < i → mu.m_match j = nu.m_match j

/--
A mechanism always returns complete matchings on the canonical finite marriage
domain `M = W = Fin n`.
-/
def paper_complete_matching_procedure_fin {n : ℕ}
    (mechanism :
      (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) →
        Assignment (Fin n) (Fin n)) : Prop :=
  ∀ val_m val_w, paper_is_complete_matching (mechanism val_m val_w)

/--
Serial-dictatorship choice property: for each man `i`, holding fixed the
partners assigned to all earlier men, the mechanism gives `i` a weakly best
available partner.
-/
def paper_serial_best_for_men {n : ℕ}
    (mechanism :
      (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) →
        Assignment (Fin n) (Fin n)) : Prop :=
  ∀ val_m val_w (i : Fin n) (mu : Assignment (Fin n) (Fin n)),
    paper_is_complete_matching mu →
      paper_priority_agree_before i mu (mechanism val_m val_w) →
        paper_matching_valM val_m i (mu.m_match i) ≤
          paper_matching_valM val_m i ((mechanism val_m val_w).m_match i)

/--
Reports by man `i` do not affect the partners assigned to earlier men. This is
the independence property used in the serial-dictatorship strategyproofness
argument.
-/
def paper_serial_prefix_independent_for_men {n : ℕ}
    (mechanism :
      (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) →
        Assignment (Fin n) (Fin n)) : Prop :=
  ∀ val_m val_w (i j : Fin n) (report_i : Fin n → ℝ),
    j < i →
      (mechanism (Function.update val_m i report_i) val_w).m_match j =
        (mechanism val_m val_w).m_match j

/-- Efficiency restricted to Roth's strict-preference marriage domain. -/
def paper_efficient_matching_procedure_on_strict_men {n : ℕ}
    (mechanism :
      (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) →
        Assignment (Fin n) (Fin n)) : Prop :=
  ∀ val_m val_w, paper_men_strict_preferences val_m →
    paper_is_pareto_optimal val_m val_w (mechanism val_m val_w)

/-- Men-side strategyproofness restricted to Roth's strict-preference domain. -/
def paper_truthful_for_men_on_strict_men {n : ℕ}
    (mechanism :
      (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) →
        Assignment (Fin n) (Fin n)) : Prop :=
  ∀ (val_m : Fin n → Fin n → ℝ) (val_w : Fin n → Fin n → ℝ),
    paper_men_strict_preferences val_m →
      ∀ (m : Fin n) (report_m : Fin n → ℝ),
        paper_matching_valM val_m m
            ((mechanism (Function.update val_m m report_m) val_w).m_match m) ≤
          paper_matching_valM val_m m ((mechanism val_m val_w).m_match m)

/--
The serial-dictatorship proof obligations used in Roth's proof of Theorem 4 on
the canonical finite marriage domain.
-/
structure Theorem4SerialDictatorshipCertificate (n : ℕ) where
  mechanism :
    (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) →
      Assignment (Fin n) (Fin n)
  complete : paper_complete_matching_procedure_fin mechanism
  serial_best : paper_serial_best_for_men mechanism
  prefix_independent : paper_serial_prefix_independent_for_men mechanism
  ignores_women : paper_ignores_women_reports mechanism

/-- Convert a complete permutation of `Fin n` into a matching assignment. -/
def paper_assignment_of_perm {n : ℕ} (p : Equiv.Perm (Fin n)) :
    Assignment (Fin n) (Fin n) where
  m_match m := some (p m)
  w_match w := some (p.symm w)
  consistent_m := by
    intro m w
    constructor
    · intro h
      injection h with hp
      subst w
      simp
    · intro h
      injection h with hp
      subst m
      simp

/-- A permutation assignment matches every agent. -/
theorem paper_assignment_of_perm_complete {n : ℕ} (p : Equiv.Perm (Fin n)) :
    paper_is_complete_matching (paper_assignment_of_perm p) := by
  constructor
  · intro m
    exact ⟨p m, rfl⟩
  · intro w
    exact ⟨p.symm w, rfl⟩

/-- Convert a complete finite assignment into its induced permutation. -/
noncomputable def paper_perm_of_complete_assignment {n : ℕ}
    (mu : Assignment (Fin n) (Fin n)) (hcomplete : paper_is_complete_matching mu) :
    Equiv.Perm (Fin n) := by
  let f : Fin n → Fin n := fun m => Classical.choose (hcomplete.1 m)
  have hf : ∀ m, mu.m_match m = some (f m) := by
    intro m
    exact Classical.choose_spec (hcomplete.1 m)
  have hinj : Function.Injective f := by
    intro m₁ m₂ h
    have hw₁ : mu.w_match (f m₁) = some m₁ :=
      (mu.consistent_m m₁ (f m₁)).1 (hf m₁)
    have hw₂ : mu.w_match (f m₁) = some m₂ := by
      rw [h]
      exact (mu.consistent_m m₂ (f m₂)).1 (hf m₂)
    have hsome : some m₁ = some m₂ := hw₁.symm.trans hw₂
    exact Option.some.inj hsome
  exact Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩

theorem paper_perm_of_complete_assignment_apply {n : ℕ}
    (mu : Assignment (Fin n) (Fin n)) (hcomplete : paper_is_complete_matching mu)
    (m : Fin n) :
    mu.m_match m = some (paper_perm_of_complete_assignment mu hcomplete m) := by
  unfold paper_perm_of_complete_assignment
  exact Classical.choose_spec (hcomplete.1 m)

theorem paper_assignment_of_perm_of_complete_assignment {n : ℕ}
    (mu : Assignment (Fin n) (Fin n)) (hcomplete : paper_is_complete_matching mu) :
    paper_assignment_of_perm (paper_perm_of_complete_assignment mu hcomplete) = mu := by
  apply Assignment.ext_of_m_match
  intro m
  exact (paper_perm_of_complete_assignment_apply mu hcomplete m).symm

/-- Permutations in `s` that maximize a real-valued score over `s`. -/
noncomputable def paper_argmax_perms {n : ℕ}
    (s : Finset (Equiv.Perm (Fin n))) (score : Equiv.Perm (Fin n) → ℝ) :
    Finset (Equiv.Perm (Fin n)) :=
  s.filter fun p => ∀ q ∈ s, score q ≤ score p

theorem paper_argmax_perms_subset {n : ℕ}
    (s : Finset (Equiv.Perm (Fin n))) (score : Equiv.Perm (Fin n) → ℝ) :
    paper_argmax_perms s score ⊆ s := by
  intro p hp
  exact (Finset.mem_filter.mp hp).1

theorem paper_argmax_perms_spec {n : ℕ}
    {s : Finset (Equiv.Perm (Fin n))} {score : Equiv.Perm (Fin n) → ℝ}
    {p : Equiv.Perm (Fin n)} (hp : p ∈ paper_argmax_perms s score) :
    ∀ q ∈ s, score q ≤ score p :=
  (Finset.mem_filter.mp hp).2

theorem paper_argmax_perms_nonempty {n : ℕ}
    (s : Finset (Equiv.Perm (Fin n))) (score : Equiv.Perm (Fin n) → ℝ)
    (hs : s.Nonempty) :
    (paper_argmax_perms s score).Nonempty := by
  classical
  rcases Finset.exists_max_image s score hs with ⟨p, hp_mem, hp_max⟩
  exact ⟨p, Finset.mem_filter.mpr ⟨hp_mem, hp_max⟩⟩

/--
After processing the first `k` priority men, keep exactly the permutations that
survive the serial-dictatorship argmax filters used so far.
-/
noncomputable def paper_serial_perm_set_aux {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) : ℕ → Finset (Equiv.Perm (Fin n))
  | 0 => Finset.univ
  | k + 1 =>
      if hk : k < n then
        paper_argmax_perms (paper_serial_perm_set_aux val_m k)
          (fun p => val_m ⟨k, hk⟩ (p ⟨k, hk⟩))
      else
        paper_serial_perm_set_aux val_m k

theorem paper_serial_perm_set_aux_nonempty {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) :
    ∀ k, (paper_serial_perm_set_aux val_m k).Nonempty := by
  intro k
  induction k with
  | zero =>
      exact ⟨Equiv.refl (Fin n), by simp [paper_serial_perm_set_aux]⟩
  | succ k ih =>
      by_cases hk : k < n
      · simpa [paper_serial_perm_set_aux, hk] using
          paper_argmax_perms_nonempty (paper_serial_perm_set_aux val_m k)
            (fun p => val_m ⟨k, hk⟩ (p ⟨k, hk⟩)) ih
      · simpa [paper_serial_perm_set_aux, hk] using ih

theorem paper_serial_perm_set_aux_succ_subset {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (k : ℕ) :
    paper_serial_perm_set_aux val_m (k + 1) ⊆
      paper_serial_perm_set_aux val_m k := by
  by_cases hk : k < n
  · intro p hp
    exact paper_argmax_perms_subset (paper_serial_perm_set_aux val_m k)
      (fun p => val_m ⟨k, hk⟩ (p ⟨k, hk⟩))
      (by simpa [paper_serial_perm_set_aux, hk] using hp)
  · intro p hp
    simpa [paper_serial_perm_set_aux, hk] using hp

theorem paper_serial_perm_set_aux_subset_of_le {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) {a b : ℕ} (h : a ≤ b) :
    paper_serial_perm_set_aux val_m b ⊆ paper_serial_perm_set_aux val_m a := by
  induction h with
  | refl =>
      intro p hp
      exact hp
  | step h ih =>
      intro p hp
      exact ih (paper_serial_perm_set_aux_succ_subset val_m _ hp)

/-- The final serial-dictatorship candidate permutations. -/
noncomputable def paper_serial_perm_set {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) : Finset (Equiv.Perm (Fin n)) :=
  paper_serial_perm_set_aux val_m n

/-- A selected serial-dictatorship permutation. -/
noncomputable def paper_serial_dictatorship_perm {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Classical.choose (paper_serial_perm_set_aux_nonempty val_m n)

theorem paper_serial_dictatorship_perm_mem {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) :
    paper_serial_dictatorship_perm val_m ∈ paper_serial_perm_set val_m := by
  exact Classical.choose_spec (paper_serial_perm_set_aux_nonempty val_m n)

theorem paper_serial_dictatorship_perm_best_at {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (i : Fin n)
    {q : Equiv.Perm (Fin n)}
    (hq : q ∈ paper_serial_perm_set_aux val_m i.val) :
    val_m i (q i) ≤ val_m i (paper_serial_dictatorship_perm val_m i) := by
  have hmem_final := paper_serial_dictatorship_perm_mem val_m
  change paper_serial_dictatorship_perm val_m ∈ paper_serial_perm_set_aux val_m n at hmem_final
  have hmem_succ :
      paper_serial_dictatorship_perm val_m ∈
        paper_serial_perm_set_aux val_m (i.val + 1) :=
    paper_serial_perm_set_aux_subset_of_le val_m
      (Nat.succ_le_iff.mpr i.isLt) hmem_final
  have hargmax :
      paper_serial_dictatorship_perm val_m ∈
        paper_argmax_perms (paper_serial_perm_set_aux val_m i.val)
          (fun p => val_m i (p i)) := by
    simpa [paper_serial_perm_set_aux, i.isLt] using hmem_succ
  exact paper_argmax_perms_spec hargmax q hq

theorem paper_serial_perm_set_aux_mem_of_agree_before {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) :
    ∀ {k : ℕ}, k ≤ n →
      ∀ {p q : Equiv.Perm (Fin n)},
        p ∈ paper_serial_perm_set_aux val_m k →
        (∀ j : Fin n, j.val < k → q j = p j) →
        q ∈ paper_serial_perm_set_aux val_m k := by
  intro k hk
  induction k with
  | zero =>
      intro p q _hp _hagree
      simp [paper_serial_perm_set_aux]
  | succ k ih =>
      intro p q hp hagree
      have hk_lt : k < n := Nat.lt_of_succ_le hk
      have hp_argmax :
          p ∈ paper_argmax_perms (paper_serial_perm_set_aux val_m k)
            (fun p => val_m ⟨k, hk_lt⟩ (p ⟨k, hk_lt⟩)) := by
        simpa [paper_serial_perm_set_aux, hk_lt] using hp
      have hp_prev : p ∈ paper_serial_perm_set_aux val_m k :=
        paper_argmax_perms_subset (paper_serial_perm_set_aux val_m k)
          (fun p => val_m ⟨k, hk_lt⟩ (p ⟨k, hk_lt⟩)) hp_argmax
      have hq_prev : q ∈ paper_serial_perm_set_aux val_m k :=
        ih (Nat.le_of_succ_le hk) hp_prev
          (by
            intro j hj
            exact hagree j (Nat.lt_trans hj (Nat.lt_succ_self k)))
      have hq_argmax :
          q ∈ paper_argmax_perms (paper_serial_perm_set_aux val_m k)
            (fun p => val_m ⟨k, hk_lt⟩ (p ⟨k, hk_lt⟩)) := by
        refine Finset.mem_filter.mpr ⟨hq_prev, ?_⟩
        intro r hr
        have hmax := paper_argmax_perms_spec hp_argmax r hr
        have hq_eq : q ⟨k, hk_lt⟩ = p ⟨k, hk_lt⟩ :=
          hagree ⟨k, hk_lt⟩ (Nat.lt_succ_self k)
        simpa [hq_eq] using hmax
      simpa [paper_serial_perm_set_aux, hk_lt] using hq_argmax

/-- The serial-dictatorship mechanism produced by the selected permutation. -/
noncomputable def paper_serial_dictatorship_mechanism {n : ℕ} :
    (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) →
      Assignment (Fin n) (Fin n) :=
  fun val_m _val_w => paper_assignment_of_perm (paper_serial_dictatorship_perm val_m)

theorem paper_serial_dictatorship_mechanism_complete {n : ℕ} :
    paper_complete_matching_procedure_fin
      (paper_serial_dictatorship_mechanism (n := n)) := by
  intro val_m val_w
  exact paper_assignment_of_perm_complete (paper_serial_dictatorship_perm val_m)

theorem paper_serial_dictatorship_mechanism_ignores_women {n : ℕ} :
    paper_ignores_women_reports
      (paper_serial_dictatorship_mechanism (n := n)) := by
  intro val_m val_w val_w'
  rfl

theorem paper_serial_dictatorship_mechanism_serial_best {n : ℕ} :
    paper_serial_best_for_men
      (paper_serial_dictatorship_mechanism (n := n)) := by
  intro val_m val_w i mu hmuComplete hagree
  let p := paper_serial_dictatorship_perm val_m
  let q := paper_perm_of_complete_assignment mu hmuComplete
  have hp_final : p ∈ paper_serial_perm_set_aux val_m n := by
    simpa [p, paper_serial_perm_set] using paper_serial_dictatorship_perm_mem val_m
  have hp_i : p ∈ paper_serial_perm_set_aux val_m i.val :=
    paper_serial_perm_set_aux_subset_of_le val_m (Nat.le_of_lt i.isLt) hp_final
  have hq_agree : ∀ j : Fin n, j.val < i.val → q j = p j := by
    intro j hj
    have hji : j < i := by
      exact_mod_cast hj
    have hmatch := hagree j hji
    have hqmatch : mu.m_match j = some (q j) := by
      exact paper_perm_of_complete_assignment_apply mu hmuComplete j
    have hpmatch :
        (paper_serial_dictatorship_mechanism val_m val_w).m_match j =
          some (p j) := rfl
    rw [hqmatch, hpmatch] at hmatch
    exact Option.some.inj hmatch
  have hq_i : q ∈ paper_serial_perm_set_aux val_m i.val :=
    paper_serial_perm_set_aux_mem_of_agree_before val_m
      (Nat.le_of_lt i.isLt) hp_i hq_agree
  have hbest := paper_serial_dictatorship_perm_best_at val_m i hq_i
  have hqmatch : mu.m_match i = some (q i) :=
    paper_perm_of_complete_assignment_apply mu hmuComplete i
  simpa [paper_serial_dictatorship_mechanism, paper_assignment_of_perm,
    paper_matching_valM, p, q, hqmatch] using hbest

theorem paper_serial_perm_set_aux_update_eq_of_le {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (i : Fin n) (report_i : Fin n → ℝ) :
    ∀ {k : ℕ}, k ≤ i.val →
      paper_serial_perm_set_aux (Function.update val_m i report_i) k =
        paper_serial_perm_set_aux val_m k := by
  intro k hk
  induction k with
  | zero =>
      simp [paper_serial_perm_set_aux]
  | succ k ih =>
      have hk_i : k < i.val := Nat.lt_of_succ_le hk
      have hk_n : k < n := Nat.lt_trans hk_i i.isLt
      have hne : (⟨k, hk_n⟩ : Fin n) ≠ i := by
        intro h
        exact (Nat.ne_of_lt hk_i) (congrArg Fin.val h)
      have ih' := ih (Nat.le_of_succ_le hk)
      simp [paper_serial_perm_set_aux, hk_n, ih', Function.update, hne]

theorem paper_serial_perm_set_aux_same_at_of_strict {n : ℕ}
    (val_m : Fin n → Fin n → ℝ)
    (hstrict : paper_men_strict_preferences val_m)
    (j : Fin n) {p q : Equiv.Perm (Fin n)}
    (hp : p ∈ paper_serial_perm_set_aux val_m (j.val + 1))
    (hq : q ∈ paper_serial_perm_set_aux val_m (j.val + 1)) :
    p j = q j := by
  have hp_argmax :
      p ∈ paper_argmax_perms (paper_serial_perm_set_aux val_m j.val)
        (fun p => val_m j (p j)) := by
    simpa [paper_serial_perm_set_aux, j.isLt] using hp
  have hq_argmax :
      q ∈ paper_argmax_perms (paper_serial_perm_set_aux val_m j.val)
        (fun p => val_m j (p j)) := by
    simpa [paper_serial_perm_set_aux, j.isLt] using hq
  have hp_prev : p ∈ paper_serial_perm_set_aux val_m j.val :=
    paper_argmax_perms_subset (paper_serial_perm_set_aux val_m j.val)
      (fun p => val_m j (p j)) hp_argmax
  have hq_prev : q ∈ paper_serial_perm_set_aux val_m j.val :=
    paper_argmax_perms_subset (paper_serial_perm_set_aux val_m j.val)
      (fun p => val_m j (p j)) hq_argmax
  have hq_le_p := paper_argmax_perms_spec hp_argmax q hq_prev
  have hp_le_q := paper_argmax_perms_spec hq_argmax p hp_prev
  exact hstrict j (p j) (q j) (le_antisymm hp_le_q hq_le_p)

theorem paper_serial_dictatorship_mechanism_prefix_independent_on_strict {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (val_w : Fin n → Fin n → ℝ)
    (hstrict : paper_men_strict_preferences val_m)
    (i j : Fin n) (report_i : Fin n → ℝ) (hji : j < i) :
    (paper_serial_dictatorship_mechanism
        (Function.update val_m i report_i) val_w).m_match j =
      (paper_serial_dictatorship_mechanism val_m val_w).m_match j := by
  let pReport := paper_serial_dictatorship_perm (Function.update val_m i report_i)
  let pTruth := paper_serial_dictatorship_perm val_m
  have hj_succ_le_i : j.val + 1 ≤ i.val := by
    exact_mod_cast hji
  have hpReport_final :
      pReport ∈ paper_serial_perm_set_aux (Function.update val_m i report_i) n := by
    simpa [pReport, paper_serial_perm_set] using
      paper_serial_dictatorship_perm_mem (Function.update val_m i report_i)
  have hpReport_update :
      pReport ∈ paper_serial_perm_set_aux
        (Function.update val_m i report_i) (j.val + 1) :=
    paper_serial_perm_set_aux_subset_of_le (Function.update val_m i report_i)
      (Nat.succ_le_iff.mpr j.isLt) hpReport_final
  have hsets :=
    paper_serial_perm_set_aux_update_eq_of_le val_m i report_i hj_succ_le_i
  have hpReport :
      pReport ∈ paper_serial_perm_set_aux val_m (j.val + 1) := by
    simpa [hsets] using hpReport_update
  have hpTruth_final : pTruth ∈ paper_serial_perm_set_aux val_m n := by
    simpa [pTruth, paper_serial_perm_set] using paper_serial_dictatorship_perm_mem val_m
  have hpTruth :
      pTruth ∈ paper_serial_perm_set_aux val_m (j.val + 1) :=
    paper_serial_perm_set_aux_subset_of_le val_m
      (Nat.succ_le_iff.mpr j.isLt) hpTruth_final
  have hsame := paper_serial_perm_set_aux_same_at_of_strict val_m hstrict j
    hpReport hpTruth
  simp [paper_serial_dictatorship_mechanism, paper_assignment_of_perm,
    pReport, pTruth, hsame]

theorem paper_serial_dictatorship_mechanism_truthful_on_strict_men {n : ℕ} :
    paper_truthful_for_men_on_strict_men
      (paper_serial_dictatorship_mechanism (n := n)) := by
  intro val_m val_w hstrict m report_m
  let y := paper_serial_dictatorship_mechanism
    (Function.update val_m m report_m) val_w
  have hyComplete : paper_is_complete_matching y :=
    paper_serial_dictatorship_mechanism_complete
      (Function.update val_m m report_m) val_w
  have hagree : paper_priority_agree_before m y
      (paper_serial_dictatorship_mechanism val_m val_w) := by
    intro j hj
    exact paper_serial_dictatorship_mechanism_prefix_independent_on_strict
      val_m val_w hstrict m j report_m hj
  simpa [y] using
    paper_serial_dictatorship_mechanism_serial_best
      val_m val_w m y hyComplete hagree

/--
The serial-dictatorship choice property implies Pareto efficiency on strict
men-preference profiles.
-/
theorem paper_serial_best_for_men_efficient_on_strict_men {n : ℕ}
    (mechanism :
      (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) →
        Assignment (Fin n) (Fin n))
    (hcomplete : paper_complete_matching_procedure_fin mechanism)
    (hserial : paper_serial_best_for_men mechanism) :
    paper_efficient_matching_procedure_on_strict_men mechanism := by
  intro val_m val_w hstrict
  let x := mechanism val_m val_w
  refine ⟨hcomplete val_m val_w, ?_⟩
  rintro ⟨nu, hnuComplete, hdom, himprove⟩
  have hall : ∀ i : Fin n, nu.m_match i = x.m_match i := by
    intro i
    refine Fin.strong_induction_on ?_ i
    intro i ih
    have hagree : paper_priority_agree_before i nu x := by
      intro j hj
      exact ih j hj
    have hbest := hserial val_m val_w i nu hnuComplete hagree
    have hdom_i := hdom.1 i
    rcases hnuComplete.1 i with ⟨wNu, hNu⟩
    rcases (hcomplete val_m val_w).1 i with ⟨wX, hX⟩
    have hle_nu_x : val_m i wNu ≤ val_m i wX := by
      simpa [paper_matching_valM, hNu, hX, x] using hbest
    have hle_x_nu : val_m i wX ≤ val_m i wNu := by
      simpa [paper_matching_valM, hNu, hX, x] using hdom_i
    have hvalue : val_m i wNu = val_m i wX := le_antisymm hle_nu_x hle_x_nu
    have hw : wNu = wX := hstrict i wNu wX hvalue
    simpa [x, hNu, hX, hw]
  have hnu_eq_x : nu = x := Assignment.ext_of_m_match hall
  subst nu
  rcases himprove with ⟨m, hm⟩ | ⟨w, hw⟩
  · exact (lt_irrefl _) hm
  · exact (lt_irrefl _) hw

/--
The serial-dictatorship choice and prefix-independence properties imply
men-side dominant-strategy truthfulness.
-/
theorem paper_serial_best_for_men_truthful_on_strict_men {n : ℕ}
    (mechanism :
      (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) →
        Assignment (Fin n) (Fin n))
    (hcomplete : paper_complete_matching_procedure_fin mechanism)
    (hserial : paper_serial_best_for_men mechanism)
    (hprefix : paper_serial_prefix_independent_for_men mechanism) :
    paper_truthful_for_men_on_strict_men mechanism := by
  intro val_m val_w _hstrict m report_m
  let y := mechanism (Function.update val_m m report_m) val_w
  have hyComplete : paper_is_complete_matching y :=
    hcomplete (Function.update val_m m report_m) val_w
  have hagree : paper_priority_agree_before m y (mechanism val_m val_w) := by
    intro j hj
    exact hprefix val_m val_w m j report_m hj
  simpa [y] using hserial val_m val_w m y hyComplete hagree

/--
Roth Theorem 4, serial-dictatorship proof-route wrapper: any mechanism satisfying
the explicit serial-dictatorship obligations is efficient on strict profiles and
strategyproof for all agents there.
-/
theorem paper_roth82_theorem4_serial_dictatorship_route
    {n : ℕ} (hcert : Theorem4SerialDictatorshipCertificate n) :
    paper_efficient_matching_procedure_on_strict_men hcert.mechanism ∧
      paper_truthful_for_men_on_strict_men hcert.mechanism ∧
      paper_truthful_for_women hcert.mechanism := by
  refine ⟨?_, ?_, ?_⟩
  · exact paper_serial_best_for_men_efficient_on_strict_men
      hcert.mechanism hcert.complete hcert.serial_best
  · exact paper_serial_best_for_men_truthful_on_strict_men
      hcert.mechanism hcert.complete hcert.serial_best hcert.prefix_independent
  · exact paper_truthful_for_women_of_ignores_women_reports
      hcert.mechanism hcert.ignores_women

/--
Constructed serial-dictatorship mechanism for Roth Theorem 4 on the canonical
strict finite marriage domain.
-/
theorem paper_roth82_theorem4_serial_dictatorship_constructed {n : ℕ} :
    paper_efficient_matching_procedure_on_strict_men
        (paper_serial_dictatorship_mechanism (n := n)) ∧
      paper_truthful_for_men_on_strict_men
        (paper_serial_dictatorship_mechanism (n := n)) ∧
      paper_truthful_for_women
        (paper_serial_dictatorship_mechanism (n := n)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact paper_serial_best_for_men_efficient_on_strict_men
      (paper_serial_dictatorship_mechanism (n := n))
      paper_serial_dictatorship_mechanism_complete
      paper_serial_dictatorship_mechanism_serial_best
  · exact paper_serial_dictatorship_mechanism_truthful_on_strict_men
  · exact paper_truthful_for_women_of_ignores_women_reports
      (paper_serial_dictatorship_mechanism (n := n))
      paper_serial_dictatorship_mechanism_ignores_women

/-! ## 5) Optimal stable procedures and one-sided incentives -/

/-- Certificate for the one-sided DA truthfulness claim used in Roth 1982 Theorem 5. -/
def DaTruthfulForMenCertificate {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] : Prop :=
  paper_truthful_for_men (deferredAcceptance (M := M) (W := W))

/-- Certificate for the women-side one-sided truthfulness claim via role reversal. -/
def DaTruthfulForWomenCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    Prop :=
  DaTruthfulForMenCertificate (M := W) (W := M)

/-- Auxiliary wrapper: truth-telling is dominant for men under men-proposing DA. -/
theorem paper_da_truthful_for_men {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hcert : @DaTruthfulForMenCertificate M W _ _ _ _) :
    paper_truthful_for_men (deferredAcceptance (M := M) (W := W)) := by
  exact hcert

/-- Auxiliary wrapper: truth-telling is dominant for women under women-proposing DA. -/
theorem paper_women_da_truthful_for_women
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hcert : @DaTruthfulForWomenCertificate M W _ _ _ _) :
    paper_truthful_for_women (paper_women_deferredAcceptance (M := M) (W := W)) := by
  intro val_m val_w w report_w
  have htruth := hcert val_w val_m w report_w
  simpa [paper_women_deferredAcceptance, paper_matching_valM, paper_matching_valW]
    using htruth

/--
Theorem 5 compatibility men-side wrapper: in the procedure selecting the
men-optimal stable outcome, truthful revelation is dominant for the men.
-/
theorem paper_roth82_theorem5_men_truthful
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hcert : @DaTruthfulForMenCertificate M W _ _ _ _) :
    paper_truthful_for_men (deferredAcceptance (M := M) (W := W)) := by
  exact paper_da_truthful_for_men hcert

/--
Theorem 5 compatibility women-side wrapper: in the procedure selecting the
women-optimal stable outcome, truthful revelation is dominant for the women.
-/
theorem paper_roth82_theorem5_women_truthful
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hcert : @DaTruthfulForWomenCertificate M W _ _ _ _) :
    paper_truthful_for_women (paper_women_deferredAcceptance (M := M) (W := W)) := by
  exact paper_women_da_truthful_for_women hcert

/--
Theorem 5 compatibility full wrapper: each side is strategyproof in its own
optimal-stable-outcome procedure once the generic DA truthfulness certificates
are supplied.
-/
theorem paper_roth82_theorem5_optimal_side_truthful
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hmen : @DaTruthfulForMenCertificate M W _ _ _ _)
    (hwomen : @DaTruthfulForWomenCertificate M W _ _ _ _) :
    paper_truthful_for_men (deferredAcceptance (M := M) (W := W)) ∧
      paper_truthful_for_women (paper_women_deferredAcceptance (M := M) (W := W)) := by
  exact ⟨paper_roth82_theorem5_men_truthful hmen,
    paper_roth82_theorem5_women_truthful hwomen⟩

/-! ## 5.1) Simple misrepresentations and first-choice reports -/

/-- A canonical positive strict report that ranks `wstar` uniquely first. -/
noncomputable def paper_strict_top_report {W : Type*} [Fintype W] [DecidableEq W]
    (wstar : W) : W → ℝ :=
  fun w =>
    if w = wstar then (Fintype.card W : ℝ) + 1
    else ((Fintype.equivFin W w).val : ℝ) + 1

theorem paper_strict_top_report_pos {W : Type*} [Fintype W] [DecidableEq W]
    (wstar w : W) :
    0 < paper_strict_top_report wstar w := by
  by_cases h : w = wstar
  · have hnonneg : (0 : ℝ) ≤ Fintype.card W := by exact_mod_cast Nat.zero_le _
    simp [paper_strict_top_report, h]
    linarith
  · have hnonneg : (0 : ℝ) ≤ (Fintype.equivFin W w).val := by
      exact_mod_cast Nat.zero_le _
    simp [paper_strict_top_report, h]
    linarith

theorem paper_strict_top_report_top {W : Type*} [Fintype W] [DecidableEq W]
    (wstar : W) :
    ∀ w, w ≠ wstar →
      paper_strict_top_report wstar w < paper_strict_top_report wstar wstar := by
  intro w hne
  have hltNat : (Fintype.equivFin W w).val < Fintype.card W :=
    (Fintype.equivFin W w).isLt
  have hlt : ((Fintype.equivFin W w).val : ℝ) < (Fintype.card W : ℝ) := by
    exact_mod_cast hltNat
  simp [paper_strict_top_report, hne]

/-- The canonical strict-top report preserves a woman's true first choice. -/
theorem paper_strict_top_report_preserves_woman_first_choice
    {M W : Type*} [Fintype M] [DecidableEq M]
    (val_w : W → M → ℝ) (w : W) (mstar : M)
    (hfirst : paper_is_strict_top_choice_for_woman val_w w mstar) :
    paper_woman_report_preserves_first_choice val_w w
      (paper_strict_top_report mstar) := by
  intro top htop m hm
  have htop_eq : top = mstar := by
    by_contra hne
    have hlt1 := hfirst top hne
    have hlt2 := htop mstar (fun h => hne h.symm)
    linarith
  subst top
  exact paper_strict_top_report_top (W := M) mstar m hm

theorem paper_strict_top_report_strict {W : Type*} [Fintype W] [DecidableEq W]
    (wstar : W) :
    ∀ w w', paper_strict_top_report wstar w =
      paper_strict_top_report wstar w' → w = w' := by
  intro w w' heq
  by_cases hw : w = wstar
  · by_cases hw' : w' = wstar
    · exact hw.trans hw'.symm
    · have hltNat : (Fintype.equivFin W w').val < Fintype.card W :=
        (Fintype.equivFin W w').isLt
      have hlt : ((Fintype.equivFin W w').val : ℝ) < (Fintype.card W : ℝ) := by
        exact_mod_cast hltNat
      simp [paper_strict_top_report, hw, hw'] at heq
      linarith
  · by_cases hw' : w' = wstar
    · have hltNat : (Fintype.equivFin W w).val < Fintype.card W :=
        (Fintype.equivFin W w).isLt
      have hlt : ((Fintype.equivFin W w).val : ℝ) < (Fintype.card W : ℝ) := by
        exact_mod_cast hltNat
      simp [paper_strict_top_report, hw, hw'] at heq
      linarith
    · have hcast :
          ((Fintype.equivFin W w).val : ℝ) =
            ((Fintype.equivFin W w').val : ℝ) := by
        simpa [paper_strict_top_report, hw, hw'] using heq
      have hnat :
          (Fintype.equivFin W w).val = (Fintype.equivFin W w').val := by
        exact_mod_cast hcast
      have hfin : Fintype.equivFin W w = Fintype.equivFin W w' :=
        Fin.ext hnat
      exact (Fintype.equivFin W).injective hfin

/-- Updating one man's report to `paper_strict_top_report` preserves the strict marriage domain. -/
theorem paper_strict_marriage_domain_update_strict_top_report
    {M W : Type*} [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M) (wstar : W)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    paper_strict_marriage_domain
      (Function.update val_m m (paper_strict_top_report wstar)) val_w := by
  rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
  refine ⟨?_, hstrictW, ?_, hposW⟩
  · intro i w w' heq
    by_cases hi : i = m
    · subst i
      have heq' : paper_strict_top_report wstar w =
          paper_strict_top_report wstar w' := by
        simpa [Function.update] using heq
      exact paper_strict_top_report_strict (W := W) wstar w w' heq'
    · exact hstrictM i w w' (by simpa [Function.update, hi] using heq)
  · intro i w
    by_cases hi : i = m
    · subst i
      simpa [Function.update] using paper_strict_top_report_pos wstar w
    · simpa [Function.update, hi] using hposM i w

/-- A strict simple report places the specified partner uniquely first. -/
def paper_man_report_strictly_ranks_partner_first {W : Type*} (report_m : W → ℝ)
    (partner : Option W) : Prop :=
  match partner with
  | none => ∀ w, report_m w < 0
  | some wstar => ∀ w, w ≠ wstar → report_m w < report_m wstar

/--
If `y` is stable under an arbitrary report by `m`, and a simple report ranks
`y.m_match m` first, then `y` is also stable under the simple report.
-/
theorem paper_simple_report_preserves_stability_of_partner
    {M W : Type*} [DecidableEq M]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (report_m simple_report_m : W → ℝ)
    (y : Assignment M W) (wstar : W)
    (hyStable : paper_is_stable (Function.update val_m m report_m) val_w y)
    (hyPartner : y.m_match m = some wstar)
    (hstarNonneg : 0 ≤ simple_report_m wstar)
    (hfirst : ∀ w, w ≠ wstar → simple_report_m w < simple_report_m wstar) :
    paper_is_stable (Function.update val_m m simple_report_m) val_w y := by
  rw [paper_is_stable_eq] at hyStable ⊢
  rcases hyStable with ⟨hmanIR, hwomanIR, hblock⟩
  refine ⟨?_, hwomanIR, ?_⟩
  · intro i
    by_cases hi : i = m
    · subst i
      simpa [valM, Function.update, hyPartner] using hstarNonneg
    · simpa [valM, Function.update, hi] using hmanIR i
  · intro i w hmi hwi
    by_cases hi : i = m
    · subst i
      have hneq : w ≠ wstar := by
        intro hw
        subst w
        simpa [valM, Function.update, hyPartner] using hmi
      have htop := hfirst w hneq
      have hmi' : simple_report_m wstar < simple_report_m w := by
        simpa [valM, Function.update, hyPartner] using hmi
      linarith
    · have hmiOld :
          valM (Function.update val_m m report_m) i (y.m_match i) <
            (Function.update val_m m report_m) i w := by
        simpa [valM, Function.update, hi] using hmi
      exact hblock i w hmiOld hwi

/--
Lemma 1 on Roth's strict marriage domain: replacing an arbitrary report by a
strict simple report with the same reported top partner leaves the manipulating
man with the same partner.
-/
theorem paper_roth82_lemma1_strict_simple_misrepresentation_same_partner
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M)
    (report_m simple_report_m : W → ℝ) (wstar : W)
    (hdomainSimple :
      paper_strict_marriage_domain (Function.update val_m m simple_report_m) val_w)
    (hyPartner :
      (deferredAcceptance (Function.update val_m m report_m) val_w).m_match m =
        some wstar)
    (hfirst : ∀ w, w ≠ wstar → simple_report_m w < simple_report_m wstar) :
    (deferredAcceptance (Function.update val_m m simple_report_m) val_w).m_match m =
      (deferredAcceptance (Function.update val_m m report_m) val_w).m_match m := by
  let y := deferredAcceptance (Function.update val_m m report_m) val_w
  let z := deferredAcceptance (Function.update val_m m simple_report_m) val_w
  rcases hdomainSimple with ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hdomainSimple' :
      paper_strict_marriage_domain (Function.update val_m m simple_report_m) val_w :=
    ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hstarPos : 0 < simple_report_m wstar := by
    have hpos := hposM m wstar
    simpa [Function.update] using hpos
  have hyStableReport :
      paper_is_stable (Function.update val_m m report_m) val_w y := by
    simpa [y] using paper_da_is_stable (Function.update val_m m report_m) val_w
  have hyStableSimple :
      paper_is_stable (Function.update val_m m simple_report_m) val_w y := by
    exact paper_simple_report_preserves_stability_of_partner
      val_m val_w m report_m simple_report_m y wstar hyStableReport
      (by simpa [y] using hyPartner) (le_of_lt hstarPos) hfirst
  have hmenOpt :=
    paper_da_is_men_optimal_on_strict_marriage_domain
      (Function.update val_m m simple_report_m) val_w hdomainSimple'
  have hle := hmenOpt.2 y hyStableSimple m
  cases hz : z.m_match m with
  | none =>
      have hle' : simple_report_m wstar ≤ 0 := by
        simpa [paper_matching_valM, y, z, hyPartner, hz, Function.update] using hle
      linarith
  | some w' =>
      have hle' : simple_report_m wstar ≤ simple_report_m w' := by
        simpa [paper_matching_valM, y, z, hyPartner, hz, Function.update] using hle
      by_cases hw' : w' = wstar
      · subst w'
        simpa [y, z, hyPartner, hz]
      · have hlt := hfirst w' hw'
        linarith

/-- Men-side DA truthfulness restricted to Roth's strict marriage domain. -/
def paper_da_truthful_for_men_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    paper_strict_marriage_domain val_m val_w →
      ∀ (m : M) (report_m : W → ℝ),
        paper_matching_valM val_m m
            ((deferredAcceptance (Function.update val_m m report_m) val_w).m_match m) ≤
          paper_matching_valM val_m m ((deferredAcceptance val_m val_w).m_match m)

/--
Source-route certificate for Theorem 5 after Lemma 1: strict simple
misrepresentations are not profitable for the manipulating man.
-/
def DaNoProfitableStrictSimpleMisreportForMenCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    paper_strict_marriage_domain val_m val_w →
      ∀ (m : M) (simple_report_m : W → ℝ) (wstar : W),
        paper_strict_marriage_domain
            (Function.update val_m m simple_report_m) val_w →
          paper_man_report_strictly_ranks_partner_first simple_report_m (some wstar) →
            paper_matching_valM val_m m
                ((deferredAcceptance
                  (Function.update val_m m simple_report_m) val_w).m_match m) ≤
              paper_matching_valM val_m m
                ((deferredAcceptance val_m val_w).m_match m)

/--
Theorem 5 reduction on the strict marriage domain: Lemma 1 plus the
no-profitable-strict-simple-misreport trace certificate imply men-side
truthfulness of men-proposing DA.
-/
theorem paper_da_truthful_for_men_on_strict_domain_of_no_simple_misreport
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hnoSimple : @DaNoProfitableStrictSimpleMisreportForMenCertificate
      M W _ _ _ _) :
    paper_da_truthful_for_men_on_strict_marriage_domain (M := M) (W := W) := by
  intro val_m val_w hdomain m report_m
  let x := deferredAcceptance val_m val_w
  let y := deferredAcceptance (Function.update val_m m report_m) val_w
  cases hy : y.m_match m with
  | none =>
      have hxStable : paper_is_stable val_m val_w x := by
        simpa [x] using paper_da_is_stable val_m val_w
      have hxIR := hxStable.1 m
      simpa [paper_matching_valM, x, y, hy] using hxIR
  | some wstar =>
      let simple_report_m := paper_strict_top_report wstar
      have hdomainSimple :
          paper_strict_marriage_domain
            (Function.update val_m m simple_report_m) val_w := by
        exact paper_strict_marriage_domain_update_strict_top_report
          val_m val_w m wstar hdomain
      have hfirst :
          ∀ w, w ≠ wstar → simple_report_m w < simple_report_m wstar := by
        simpa [simple_report_m] using
          paper_strict_top_report_top (W := W) wstar
      have hfirstProp :
          paper_man_report_strictly_ranks_partner_first
            simple_report_m (some wstar) := by
        simpa [paper_man_report_strictly_ranks_partner_first] using hfirst
      have hsame :
          (deferredAcceptance
              (Function.update val_m m simple_report_m) val_w).m_match m =
            y.m_match m := by
        exact paper_roth82_lemma1_strict_simple_misrepresentation_same_partner
          val_m val_w m report_m simple_report_m wstar hdomainSimple
          (by simpa [y] using hy) hfirst
      have hsimple := hnoSimple val_m val_w hdomain m simple_report_m wstar
        hdomainSimple hfirstProp
      rw [hsame] at hsimple
      simpa [x, y, hy] using hsimple

/--
Theorem 5 men-side source route on the strict marriage domain, with the
strict-simple-misreport trace certificate isolated as
`DaNoProfitableStrictSimpleMisreportForMenCertificate`.
-/
theorem paper_roth82_theorem5_men_truthful_on_strict_domain_of_no_simple_misreport
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hnoSimple : @DaNoProfitableStrictSimpleMisreportForMenCertificate
      M W _ _ _ _) :
    paper_da_truthful_for_men_on_strict_marriage_domain (M := M) (W := W) := by
  exact paper_da_truthful_for_men_on_strict_domain_of_no_simple_misreport
    hnoSimple

/-- Women-side DA truthfulness restricted to Roth's strict marriage domain. -/
def paper_da_truthful_for_women_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    paper_strict_marriage_domain val_m val_w →
      ∀ (w : W) (report_w : M → ℝ),
        paper_matching_valW val_w w
            ((paper_women_deferredAcceptance val_m
              (Function.update val_w w report_w)).w_match w) ≤
          paper_matching_valW val_w w
            ((paper_women_deferredAcceptance val_m val_w).w_match w)

/-- Source-route certificate for the women side, encoded by role reversal. -/
def DaNoProfitableStrictSimpleMisreportForWomenCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    Prop :=
  @DaNoProfitableStrictSimpleMisreportForMenCertificate W M _ _ _ _

/--
Theorem 5 reduction for the women-proposing procedure, obtained by applying the
men-side strict-simple-misreport reduction after swapping the two sides.
-/
theorem paper_da_truthful_for_women_on_strict_domain_of_no_simple_misreport
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hnoSimple : @DaNoProfitableStrictSimpleMisreportForWomenCertificate
      M W _ _ _ _) :
    paper_da_truthful_for_women_on_strict_marriage_domain (M := M) (W := W) := by
  intro val_m val_w hdomain w report_w
  rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hdomainSwap : paper_strict_marriage_domain val_w val_m :=
    ⟨hstrictW, hstrictM, hposW, hposM⟩
  have htruth :=
    paper_da_truthful_for_men_on_strict_domain_of_no_simple_misreport
      (M := W) (W := M) hnoSimple
  have h := htruth val_w val_m hdomainSwap w report_w
  simpa [paper_women_deferredAcceptance, paper_matching_valM, paper_matching_valW]
    using h

/--
Theorem 5 source route on the strict marriage domain for both proposing sides,
with each side's certificate-parametrized route isolated as a strict-simple-misreport
trace certificate.
-/
theorem paper_roth82_theorem5_optimal_side_truthful_on_strict_domain_of_no_simple_misreport
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hmenNoSimple : @DaNoProfitableStrictSimpleMisreportForMenCertificate
      M W _ _ _ _)
    (hwomenNoSimple : @DaNoProfitableStrictSimpleMisreportForWomenCertificate
      M W _ _ _ _) :
    paper_da_truthful_for_men_on_strict_marriage_domain (M := M) (W := W) ∧
      paper_da_truthful_for_women_on_strict_marriage_domain (M := M) (W := W) := by
  exact ⟨paper_roth82_theorem5_men_truthful_on_strict_domain_of_no_simple_misreport
      hmenNoSimple,
    paper_da_truthful_for_women_on_strict_domain_of_no_simple_misreport
      hwomenNoSimple⟩

/--
Certificate for Roth's Lemma 1.

If a man first uses an arbitrary report and then uses a simple report ranking
the resulting partner first, men-proposing DA gives him the same partner.
-/
def DaLemma1SimpleMisrepresentationPartnerCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M)
    (report_m simple_report_m : W → ℝ),
    paper_man_report_ranks_partner_first simple_report_m
        ((deferredAcceptance (Function.update val_m m report_m) val_w).m_match m) →
      (deferredAcceptance (Function.update val_m m simple_report_m) val_w).m_match m =
        (deferredAcceptance (Function.update val_m m report_m) val_w).m_match m

/--
Lemma 1 compatibility wrapper: the equivalent simple misrepresentation leaves
the manipulating man with the same partner.
-/
theorem paper_roth82_lemma1_simple_misrepresentation_same_partner
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hcert : @DaLemma1SimpleMisrepresentationPartnerCertificate M W _ _ _ _) :
    DaLemma1SimpleMisrepresentationPartnerCertificate (M := M) (W := W) := by
  exact hcert

/--
Certificate for Roth's Lemma 2.

For a simple misrepresentation that does not hurt the manipulating man, every
man weakly prefers the resulting DA outcome to the truthful DA outcome.
-/
def DaLemma2SimpleMisrepresentationNoMenHarmedCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M)
    (simple_report_m : W → ℝ),
    let x := deferredAcceptance val_m val_w
    let y := deferredAcceptance (Function.update val_m m simple_report_m) val_w
    paper_man_report_ranks_partner_first simple_report_m (y.m_match m) →
      paper_man_weakly_prefers_outcome val_m m y x →
        ∀ m', paper_man_weakly_prefers_outcome val_m m' y x

/--
Lemma 2 compatibility wrapper: a successful simple misrepresentation does not
make any man worse off.
-/
theorem paper_roth82_lemma2_simple_misrepresentation_no_men_harmed
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hcert : @DaLemma2SimpleMisrepresentationNoMenHarmedCertificate M W _ _ _ _) :
    DaLemma2SimpleMisrepresentationNoMenHarmedCertificate (M := M) (W := W) := by
  exact hcert

/--
Certificate for Corollary 5.1 in the men-proposing procedure: women cannot
profit from reports that misrepresent their first choice.
-/
def DaNoProfitableFirstChoiceMisreportForWomenCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    Prop :=
  paper_no_profitable_first_choice_misreport_for_women
    (deferredAcceptance (M := M) (W := W))

/--
Source-faithful certificate for Corollary 5.1 in the men-proposing procedure:
any woman report is weakly dominated by some report that keeps the woman's true
first choice first.
-/
def DaNoNeedToMisrepresentFirstChoiceForWomenCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    Prop :=
  paper_no_need_to_misrepresent_first_choice_for_women_on_strict_domain
    (deferredAcceptance (M := M) (W := W))

/--
Corollary 5.1 compatibility wrapper: in the men-optimal stable procedure, women
cannot profit by misrepresenting their first choice.
-/
theorem paper_roth82_corollary5_1_no_profitable_first_choice_misreport
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hcert : @DaNoProfitableFirstChoiceMisreportForWomenCertificate M W _ _ _ _) :
    paper_no_profitable_first_choice_misreport_for_women
      (deferredAcceptance (M := M) (W := W)) := by
  exact hcert

/--
Corollary 5.1 source-faithful compatibility wrapper: in the men-optimal stable
procedure, a woman never needs to misrepresent her first choice; any report is
weakly matched by a report preserving the true first choice.
-/
theorem paper_roth82_corollary5_1_no_need_to_misrepresent_first_choice
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (hcert : @DaNoNeedToMisrepresentFirstChoiceForWomenCertificate M W _ _ _ _) :
    paper_no_need_to_misrepresent_first_choice_for_women_on_strict_domain
      (deferredAcceptance (M := M) (W := W)) := by
  exact hcert

/--
Roth's proof-line observation for Corollary 5.1: if a woman's true first choice
has proposed to her in the men-proposing DA run, then she finishes matched to
that first choice.
-/
theorem paper_da_true_first_choice_proposal_implies_final_true_first_choice
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (w : W) (mstar : M)
    (hfirst : paper_is_strict_top_choice_for_woman val_w w mstar)
    (hpos : 0 < val_w w mstar)
    (hproposed : w ∉ (deferredAcceptanceState val_m val_w).m_proposals mstar) :
    (deferredAcceptance val_m val_w).w_match w = some mstar := by
  have hproposedN :
      w ∉ (daStateAfterSteps val_m val_w
        (Fintype.card M * Fintype.card W)).m_proposals mstar := by
    simpa [deferredAcceptanceState_eq_daStateAfterSteps] using hproposed
  rcases exists_proposal_removal_step_before_of_not_mem_daStateAfterSteps
      val_m val_w hproposedN with
    ⟨t, ht, hmem, hnot⟩
  have hfinal :=
    woman_final_value_ge_of_proposal_removed_at_daStateAfterSteps
      val_m val_w (steps := t) (m := mstar) (w := w) ht hmem hnot
  cases hmatch : (deferredAcceptanceState val_m val_w).w_match w with
  | none =>
      have hle : val_w w mstar ≤ 0 := by
        simpa [valW, hmatch] using hfinal
      linarith
  | some m =>
      by_cases hm : m = mstar
      · subst m
        simpa [deferredAcceptance, hmatch]
      · have hlt := hfirst m hm
        have hle : val_w w mstar ≤ val_w w m := by
          simpa [valW, hmatch] using hfinal
        linarith

/--
If the truthful men-proposing DA run already brings a woman a proposal from her
true first choice, no report by that woman can strictly improve her true payoff.
-/
theorem paper_da_true_first_choice_proposal_no_profitable_woman_report
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (w : W) (mstar : M) (report_w : M → ℝ)
    (hfirst : paper_is_strict_top_choice_for_woman val_w w mstar)
    (hpos : 0 < val_w w mstar)
    (hproposed : w ∉ (deferredAcceptanceState val_m val_w).m_proposals mstar) :
    paper_matching_valW val_w w
        ((deferredAcceptance val_m
          (Function.update val_w w report_w)).w_match w) ≤
      paper_matching_valW val_w w ((deferredAcceptance val_m val_w).w_match w) := by
  have htruth :
      (deferredAcceptance val_m val_w).w_match w = some mstar :=
    paper_da_true_first_choice_proposal_implies_final_true_first_choice
      val_m val_w w mstar hfirst hpos hproposed
  cases hmis :
      (deferredAcceptance val_m (Function.update val_w w report_w)).w_match w with
  | none =>
      have hnonneg : (0 : ℝ) ≤ val_w w mstar := le_of_lt hpos
      simpa [paper_matching_valW, htruth, hmis] using hnonneg
  | some m =>
      by_cases hm : m = mstar
      · subst m
        simp [paper_matching_valW, htruth]
      · have hlt := hfirst m hm
        have hle : val_w w m ≤ val_w w mstar := le_of_lt hlt
        simpa [paper_matching_valW, htruth, hmis] using hle

/--
Contrapositive Corollary 5.1 bridge: if a woman has a strictly profitable report,
then her true first choice cannot have proposed in the truthful men-proposing DA run.
-/
theorem paper_da_profitable_woman_report_implies_true_first_choice_not_proposed
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (w : W) (mstar : M) (report_w : M → ℝ)
    (hfirst : paper_is_strict_top_choice_for_woman val_w w mstar)
    (hpos : 0 < val_w w mstar)
    (hprofit :
      paper_matching_valW val_w w ((deferredAcceptance val_m val_w).w_match w) <
        paper_matching_valW val_w w
          ((deferredAcceptance val_m
            (Function.update val_w w report_w)).w_match w)) :
    w ∈ (deferredAcceptanceState val_m val_w).m_proposals mstar := by
  by_contra hnot
  have hle :=
    paper_da_true_first_choice_proposal_no_profitable_woman_report
      val_m val_w w mstar report_w hfirst hpos hnot
  linarith

/--
DA step persistence for Corollary 5.1: once a woman holds a man whom her report
ranks strictly above every other man, no later proposal step can dislodge him.
-/
theorem paper_da_woman_holds_report_top_persists_step
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (s : DAState M W) (w : W) (mstar : M)
    (htop : ∀ m, m ≠ mstar → val_w w m < val_w w mstar)
    (hpos : 0 < val_w w mstar)
    (hhold : s.w_match w = some mstar) :
    (daStep val_m val_w s).w_match w = some mstar := by
  have hmono := woman_match_value_daStep_mono val_m val_w s w
  cases hafter : (daStep val_m val_w s).w_match w with
  | none =>
      have hle : val_w w mstar ≤ 0 := by
        simpa [valW, hhold, hafter] using hmono
      linarith
  | some m =>
      by_cases hm : m = mstar
      · subst m
        rfl
      · have hlt := htop m hm
        have hle : val_w w mstar ≤ val_w w m := by
          simpa [valW, hhold, hafter] using hmono
        linarith

/-- Run-prefix persistence for a woman holding her report-top man. -/
theorem paper_da_woman_holds_report_top_persists_steps
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (w : W) (mstar : M)
    (htop : ∀ m, m ≠ mstar → val_w w m < val_w w mstar)
    (hpos : 0 < val_w w mstar)
    {steps later : ℕ} (hle : steps ≤ later)
    (hhold : (daStateAfterSteps val_m val_w steps).w_match w = some mstar) :
    (daStateAfterSteps val_m val_w later).w_match w = some mstar := by
  have hadd : steps + (later - steps) = later := Nat.add_sub_of_le hle
  suffices
      (daStateAfterSteps val_m val_w (steps + (later - steps))).w_match w =
        some mstar by
    simpa [hadd] using this
  induction later - steps with
  | zero =>
      simpa using hhold
  | succ extra ih =>
      have hstep :=
        paper_da_woman_holds_report_top_persists_step
          val_m val_w (daStateAfterSteps val_m val_w (steps + extra))
          w mstar htop hpos ih
      have hs :
          daStateAfterSteps val_m val_w (steps + (extra + 1)) =
            daStep val_m val_w (daStateAfterSteps val_m val_w (steps + extra)) := by
        rw [← Nat.add_assoc, daStateAfterSteps_succ]
      simpa [hs] using hstep

/--
One-step trace split for Corollary 5.1. If woman `w` changes an arbitrary report
by raising `mstar` above every other man while leaving other scores fixed, then
one DA step is either unchanged or the raised report makes `w` hold `mstar`.
-/
theorem paper_da_raise_first_choice_step_eq_or_holds_top
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (w : W) (mstar : M) (report_w : M → ℝ)
    (s : DAState M W) :
    let badVal := Function.update val_w w report_w
    let raised := paper_raise_first_choice_report mstar report_w
    let goodVal := Function.update val_w w raised
    daStep val_m badVal s = daStep val_m goodVal s ∨
      (daStep val_m goodVal s).w_match w = some mstar := by
  classical
  intro badVal raised goodVal
  have htopGood : ∀ m, m ≠ mstar → goodVal w m < goodVal w mstar := by
    intro m hm
    simpa [goodVal, raised, Function.update] using
      paper_raise_first_choice_report_top mstar report_w m hm
  have hposGood : 0 < goodVal w mstar := by
    simpa [goodVal, raised, Function.update] using
      paper_raise_first_choice_report_top_pos mstar report_w
  by_cases hactive : ∃ m, IsActiveMan val_m s m
  · by_cases hw0 : daStepChosenWoman val_m s hactive = w
    · cases hcur : s.w_match w with
      | none =>
          by_cases ha : daStepChosenMan val_m s hactive = mstar
          · right
            have haccGood : daStepChosenAccepts val_m goodVal s hactive := by
              simpa [daStepChosenAccepts, hw0, hcur, ha] using
                (le_of_lt hposGood)
            have hmatch :=
              daStep_w_match_chosen_of_accepts val_m goodVal s hactive haccGood
            simpa [hw0, ha] using hmatch
          · left
            have hgood_a :
                goodVal w (daStepChosenMan val_m s hactive) =
                  badVal w (daStepChosenMan val_m s hactive) := by
              simp [goodVal, badVal, raised,
                paper_raise_first_choice_report_of_ne mstar report_w ha]
            have haccIff :
                daStepChosenAccepts val_m badVal s hactive ↔
                  daStepChosenAccepts val_m goodVal s hactive := by
              simp [daStepChosenAccepts, hw0, hcur, hgood_a]
            exact daStep_eq_of_chosen_accepts_iff val_m badVal goodVal s
              hactive haccIff
      | some cur =>
          by_cases hcurstar : cur = mstar
          · right
            subst cur
            exact paper_da_woman_holds_report_top_persists_step
              val_m goodVal s w mstar htopGood hposGood hcur
          · by_cases ha : daStepChosenMan val_m s hactive = mstar
            · right
              have hltGood : goodVal w cur < goodVal w mstar := htopGood cur hcurstar
              have haccGood : daStepChosenAccepts val_m goodVal s hactive := by
                simpa [daStepChosenAccepts, hw0, hcur, ha] using hltGood
              have hmatch :=
                daStep_w_match_chosen_of_accepts val_m goodVal s hactive haccGood
              simpa [hw0, ha] using hmatch
            · left
              have hgood_a :
                  goodVal w (daStepChosenMan val_m s hactive) =
                    badVal w (daStepChosenMan val_m s hactive) := by
                simp [goodVal, badVal, raised,
                  paper_raise_first_choice_report_of_ne mstar report_w ha]
              have hgood_cur : goodVal w cur = badVal w cur := by
                simp [goodVal, badVal, raised,
                  paper_raise_first_choice_report_of_ne mstar report_w hcurstar]
              have haccIff :
                  daStepChosenAccepts val_m badVal s hactive ↔
                    daStepChosenAccepts val_m goodVal s hactive := by
                simp [daStepChosenAccepts, hw0, hcur, hgood_a, hgood_cur]
              exact daStep_eq_of_chosen_accepts_iff val_m badVal goodVal s
                hactive haccIff
    · left
      have hsameW :
          badVal (daStepChosenWoman val_m s hactive) =
            goodVal (daStepChosenWoman val_m s hactive) := by
        funext m
        simp [badVal, goodVal, hw0]
      have haccIff :
          daStepChosenAccepts val_m badVal s hactive ↔
            daStepChosenAccepts val_m goodVal s hactive := by
        simp [daStepChosenAccepts, hsameW]
      exact daStep_eq_of_chosen_accepts_iff val_m badVal goodVal s
        hactive haccIff
  · left
    simp [daStep, hactive]

/--
Run-prefix trace split for Corollary 5.1. Across the bad report and the report
that raises `mstar` to the top, the DA traces are equal until the raised trace
makes `w` hold `mstar`; once that happens it persists.
-/
theorem paper_da_raise_first_choice_trace_eq_or_holds_top
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (w : W) (mstar : M) (report_w : M → ℝ) (steps : ℕ) :
    let badVal := Function.update val_w w report_w
    let raised := paper_raise_first_choice_report mstar report_w
    let goodVal := Function.update val_w w raised
    daStateAfterSteps val_m badVal steps =
        daStateAfterSteps val_m goodVal steps ∨
      (daStateAfterSteps val_m goodVal steps).w_match w = some mstar := by
  classical
  intro badVal raised goodVal
  have htopGood : ∀ m, m ≠ mstar → goodVal w m < goodVal w mstar := by
    intro m hm
    simpa [goodVal, raised, Function.update] using
      paper_raise_first_choice_report_top mstar report_w m hm
  have hposGood : 0 < goodVal w mstar := by
    simpa [goodVal, raised, Function.update] using
      paper_raise_first_choice_report_top_pos mstar report_w
  induction steps with
  | zero =>
      left
      simp
  | succ steps ih =>
      rcases ih with hsame | hhold
      · have hstep :=
          paper_da_raise_first_choice_step_eq_or_holds_top
            val_m val_w w mstar report_w
            (daStateAfterSteps val_m badVal steps)
        rcases (by simpa [badVal, raised, goodVal] using hstep) with
          hstepSame | hstepHold
        · left
          rw [daStateAfterSteps_succ, daStateAfterSteps_succ, ← hsame,
            hstepSame]
        · right
          simpa [daStateAfterSteps_succ, ← hsame] using hstepHold
      · right
        have hpersist :=
          paper_da_woman_holds_report_top_persists_step
            val_m goodVal (daStateAfterSteps val_m goodVal steps)
            w mstar htopGood hposGood hhold
        simpa [daStateAfterSteps_succ] using hpersist

/--
Raising a woman's true first choice above an arbitrary report weakly dominates
that arbitrary report in the men-proposing DA outcome, measured by the woman's
true utility.
-/
theorem paper_da_raise_first_choice_report_weakly_dominates
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (w : W) (mstar : M) (report_w : M → ℝ)
    (hfirst : paper_is_strict_top_choice_for_woman val_w w mstar)
    (hpos : 0 < val_w w mstar) :
    paper_matching_valW val_w w
        ((deferredAcceptance val_m
          (Function.update val_w w report_w)).w_match w) ≤
      paper_matching_valW val_w w
        ((deferredAcceptance val_m
          (Function.update val_w w
            (paper_raise_first_choice_report mstar report_w))).w_match w) := by
  classical
  let badVal := Function.update val_w w report_w
  let raised := paper_raise_first_choice_report mstar report_w
  let goodVal := Function.update val_w w raised
  change
    paper_matching_valW val_w w ((deferredAcceptance val_m badVal).w_match w) ≤
      paper_matching_valW val_w w
        ((deferredAcceptance val_m goodVal).w_match w)
  have htrace :=
    paper_da_raise_first_choice_trace_eq_or_holds_top
      val_m val_w w mstar report_w (Fintype.card M * Fintype.card W)
  rcases (by simpa [badVal, raised, goodVal] using htrace) with hsame | htop
  · have hstate :
      deferredAcceptanceState val_m badVal =
        deferredAcceptanceState val_m goodVal := by
      simpa [deferredAcceptanceState_eq_daStateAfterSteps] using hsame
    simp [deferredAcceptance, hstate]
  · have hgood :
      (deferredAcceptance val_m goodVal).w_match w = some mstar := by
      simpa [deferredAcceptance, deferredAcceptanceState_eq_daStateAfterSteps]
        using htop
    cases hbad : (deferredAcceptance val_m badVal).w_match w with
    | none =>
        have hnonneg : (0 : ℝ) ≤ val_w w mstar := le_of_lt hpos
        simpa [paper_matching_valW, hgood] using hnonneg
    | some m =>
        by_cases hm : m = mstar
        · subst m
          simp [paper_matching_valW, hgood]
        · have hle : val_w w m ≤ val_w w mstar := le_of_lt (hfirst m hm)
          simpa [paper_matching_valW, hgood] using hle

/--
Source-faithful Corollary 5.1 for men-proposing DA on the strict marriage
domain: any woman report is weakly matched by a report preserving her true first
choice.
-/
theorem paper_da_no_need_to_misrepresent_first_choice_for_women_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M] :
    paper_no_need_to_misrepresent_first_choice_for_women_on_strict_domain
      (deferredAcceptance (M := M) (W := W)) := by
  intro val_m val_w hdomain w report_w hreport
  rcases hdomain with ⟨_hstrictM, hstrictW, _hposM, hposW⟩
  obtain ⟨mstar, hfirst⟩ :=
    paper_exists_strict_top_choice_for_woman val_w hstrictW w
  refine ⟨paper_raise_first_choice_report mstar report_w, ?_, ?_, ?_⟩
  · exact paper_strict_marriage_domain_update_raise_first_choice_report
      val_m val_w w mstar report_w hreport
  · exact paper_raise_first_choice_report_preserves_woman_first_choice
      val_w w mstar report_w hfirst
  · exact paper_da_raise_first_choice_report_weakly_dominates
      val_m val_w w mstar report_w hfirst (hposW w mstar)

/--
Paper-facing Corollary 5.1 wrapper, closed for nonempty finite strict marriage
markets.
-/
theorem paper_roth82_corollary5_1_no_need_to_misrepresent_first_choice_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M] :
    paper_no_need_to_misrepresent_first_choice_for_women_on_strict_domain
      (deferredAcceptance (M := M) (W := W)) :=
  paper_da_no_need_to_misrepresent_first_choice_for_women_on_strict_domain
    (M := M) (W := W)

/--
Role-reversed Corollary 5.1: for women-proposing DA on the original sides, any
man report is weakly matched by a report preserving his true first choice.
-/
theorem paper_roth82_corollary5_1_role_reversed_no_need_to_misrepresent_first_choice_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty W] :
    paper_no_need_to_misrepresent_first_choice_for_men_on_strict_domain
      (paper_women_deferredAcceptance (M := M) (W := W)) := by
  intro val_m val_w hdomain m report_m hreport
  have hdomainSwap : paper_strict_marriage_domain val_w val_m := by
    rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
    exact ⟨hstrictW, hstrictM, hposW, hposM⟩
  have hreportSwap :
      paper_strict_marriage_domain val_w
        (Function.update val_m m report_m) := by
    rcases hreport with ⟨hstrictM, hstrictW, hposM, hposW⟩
    exact ⟨hstrictW, hstrictM, hposW, hposM⟩
  obtain ⟨faithful_report_m, hfaithfulSwap, hpreserve, hweak⟩ :=
    paper_roth82_corollary5_1_no_need_to_misrepresent_first_choice_on_strict_domain
      (M := W) (W := M) val_w val_m hdomainSwap m report_m hreportSwap
  refine ⟨faithful_report_m, ?_, ?_, ?_⟩
  · rcases hfaithfulSwap with ⟨hstrictW, hstrictM, hposW, hposM⟩
    exact ⟨hstrictM, hstrictW, hposM, hposW⟩
  · simpa [paper_man_report_preserves_first_choice,
      paper_is_strict_top_choice_for_man, paper_woman_report_preserves_first_choice,
      paper_is_strict_top_choice_for_woman] using hpreserve
  · simpa [paper_man_weakly_prefers_outcome, paper_woman_weakly_prefers_outcome,
      paper_women_deferredAcceptance, paper_matching_valM, paper_matching_valW] using hweak

/-! ## 6) Weak Pareto optimality for the proposing side -/

/--
If a man strictly prefers `w` to his final DA partner, then he must have already
proposed to `w` by termination.
-/
theorem paper_da_final_better_partner_was_proposed
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M) (w : W)
    (hbetter :
      paper_matching_valM val_m m ((deferredAcceptance val_m val_w).m_match m) <
        val_m m w) :
    w ∉ (deferredAcceptanceState val_m val_w).m_proposals m := by
  have hstate := deferredAcceptanceState_satisfies_invariants_closed val_m val_w
  have hterm := deferredAcceptanceState_terminated val_m val_w
  unfold DAStateInvariantCertificate at hstate
  unfold DATerminationCertificate at hterm
  rcases hstate with ⟨hmanIR, _hwomanIR, hmatchedProposed, _hwomanReject,
    hproposalOrder⟩
  intro hremaining
  cases hfinal : (deferredAcceptanceState val_m val_w).m_match m with
  | none =>
      have hpositive : 0 < val_m m w := by
        simpa [paper_matching_valM, deferredAcceptance, hfinal] using hbetter
      exact hterm ⟨m, hfinal, ⟨w, hremaining, le_of_lt hpositive⟩⟩
  | some wcur =>
      have hnotCurrentRemaining :
          wcur ∉ (deferredAcceptanceState val_m val_w).m_proposals m :=
        hmatchedProposed m wcur hfinal
      have hbetter' : val_m m wcur < val_m m w := by
        simpa [paper_matching_valM, deferredAcceptance, hfinal] using hbetter
      have hnonneg : 0 ≤ val_m m w := by
        have hcurIR : 0 ≤ val_m m wcur := hmanIR m wcur hfinal
        linarith
      have hle := hproposalOrder m wcur w hnotCurrentRemaining hremaining hnonneg
      linarith

/--
The DA trace fact used in Roth's proof of Theorem 6: some final matched woman
received no proposals except from her final partner.
-/
def DaLastUniqueProposalForMenCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ∃ m w,
    (deferredAcceptance val_m val_w).m_match m = some w ∧
      ∀ m', m' ≠ m → w ∈ (deferredAcceptanceState val_m val_w).m_proposals m'

/--
Sharper final-step trace certificate for Theorem 6. It records a previous DA
state in which the final partner `w` was unmatched, together with the fact that
the final folded state is obtained by removing only `m`'s opportunity to propose
to `w`. This is the formal analogue of Roth's "man who makes a match in the
final period" observation.
-/
def DaFinalUnmatchedWomanStepCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ∃ (s : DAState M W) (m : M) (w : W),
    DAInvariants val_m val_w s ∧
      s.w_match w = none ∧
      (deferredAcceptance val_m val_w).m_match m = some w ∧
      (∀ m', m' ≠ m →
        (deferredAcceptanceState val_m val_w).m_proposals m' =
          s.m_proposals m')

/--
Timed version of the final-unmatched-woman certificate, stated directly in
terms of a prefix of the folded DA run.
-/
def DaFinalUnmatchedWomanStepAtTimeCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ∃ (t : ℕ) (m : M) (w : W),
    t < Fintype.card M * Fintype.card W ∧
      (daStateAfterSteps val_m val_w t).w_match w = none ∧
      (deferredAcceptance val_m val_w).m_match m = some w ∧
      (∀ m', m' ≠ m →
        (deferredAcceptanceState val_m val_w).m_proposals m' =
          (daStateAfterSteps val_m val_w t).m_proposals m')

/--
Trace certificate for the final active proposal step in the folded DA run.
The state at time `t` still has an active man, while the state at `t + 1` has
none.
-/
def DaLastActiveStepAtTimeCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ∃ t,
    t < Fintype.card M * Fintype.card W ∧
      (∃ m, IsActiveMan val_m (daStateAfterSteps val_m val_w t) m) ∧
      ¬ ∃ m, IsActiveMan val_m (daStateAfterSteps val_m val_w (t + 1)) m

lemma exists_last_true_before_false
    {P : ℕ → Prop} {N : ℕ} (h0 : P 0) (hN : ¬ P N) :
    ∃ t, t < N ∧ P t ∧ ¬ P (t + 1) := by
  classical
  let Q : ℕ → Prop := fun n => ¬ P n
  have hQ : ∃ n, Q n := ⟨N, hN⟩
  let n := Nat.find hQ
  have hnQ : Q n := Nat.find_spec hQ
  have hnpos : 0 < n := by
    by_contra hnot
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnot
    have hnQ0 : ¬ P 0 := by
      simpa [Q, hn0] using hnQ
    exact hnQ0 h0
  refine ⟨n - 1, ?_, ?_, ?_⟩
  · have hnleN : n ≤ N := Nat.find_min' hQ hN
    exact lt_of_lt_of_le (Nat.sub_one_lt hnpos.ne') hnleN
  · by_contra hnotP
    have hnle : n ≤ n - 1 := Nat.find_min' hQ hnotP
    exact (not_lt_of_ge hnle) (Nat.sub_one_lt hnpos.ne')
  · have hs : n - 1 + 1 = n :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt hnpos)
    simpa [Q, hs] using hnQ

/--
If a proposal opportunity is absent in the final DA state, then some concrete
folded step removed it. This is the run-prefix form of "the man proposed to
that woman at some step" used in Roth's trace arguments.
-/
theorem paper_da_exists_proposal_removal_step_of_final_not_remaining
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M) (w : W)
    (hnot : w ∉ (deferredAcceptanceState val_m val_w).m_proposals m) :
    ∃ t, t < Fintype.card M * Fintype.card W ∧
      w ∈ (daStateAfterSteps val_m val_w t).m_proposals m ∧
      w ∉ (daStateAfterSteps val_m val_w (t + 1)).m_proposals m := by
  let N := Fintype.card M * Fintype.card W
  let P : ℕ → Prop := fun t =>
    w ∈ (daStateAfterSteps val_m val_w t).m_proposals m
  have h0 : P 0 := by
    simp [P, initialDAState]
  have hN : ¬ P N := by
    simpa [P, N, deferredAcceptanceState_eq_daStateAfterSteps] using hnot
  simpa [P, N] using exists_last_true_before_false (P := P) h0 hN

/--
Lemma 2 trace bridge: if a non-manipulating man is worse off after one man's
report change, then the non-manipulator's truthful DA partner is removed from
his proposal set during the altered run.
-/
theorem paper_da_other_man_truthful_partner_removed_step_of_worse_after_one_man_report
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m m' : M) (report_m : W → ℝ) (w : W)
    (hm' : m' ≠ m)
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hworse :
      paper_matching_valM val_m m'
          ((deferredAcceptance
            (Function.update val_m m report_m) val_w).m_match m') <
        paper_matching_valM val_m m'
          ((deferredAcceptance val_m val_w).m_match m')) :
    ∃ t, t < Fintype.card M * Fintype.card W ∧
      w ∈ (daStateAfterSteps
          (Function.update val_m m report_m) val_w t).m_proposals m' ∧
      w ∉ (daStateAfterSteps
          (Function.update val_m m report_m) val_w (t + 1)).m_proposals m' := by
  have hbetterTrue :
      paper_matching_valM val_m m'
          ((deferredAcceptance
            (Function.update val_m m report_m) val_w).m_match m') <
        val_m m' w := by
    simpa [paper_matching_valM, hx] using hworse
  have hbetterReported :
      paper_matching_valM (Function.update val_m m report_m) m'
          ((deferredAcceptance
            (Function.update val_m m report_m) val_w).m_match m') <
        (Function.update val_m m report_m) m' w := by
    simpa [paper_matching_valM, Function.update, hm'] using hbetterTrue
  have hnot :
      w ∉ (deferredAcceptanceState
          (Function.update val_m m report_m) val_w).m_proposals m' :=
    paper_da_final_better_partner_was_proposed
      (Function.update val_m m report_m) val_w m' w hbetterReported
  exact paper_da_exists_proposal_removal_step_of_final_not_remaining
    (Function.update val_m m report_m) val_w m' w hnot

/--
Strengthened Lemma 2 trace bridge: the worse-off non-manipulator actively
proposes to his truthful DA partner at a concrete altered-run step.
-/
theorem paper_da_other_man_truthful_partner_proposed_step_of_worse_after_one_man_report
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m m' : M) (report_m : W → ℝ) (w : W)
    (hm' : m' ≠ m)
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hworse :
      paper_matching_valM val_m m'
          ((deferredAcceptance
            (Function.update val_m m report_m) val_w).m_match m') <
        paper_matching_valM val_m m'
          ((deferredAcceptance val_m val_w).m_match m')) :
    ∃ t, t < Fintype.card M * Fintype.card W ∧
      w ∈ (daStateAfterSteps
          (Function.update val_m m report_m) val_w t).m_proposals m' ∧
      w ∉ (daStateAfterSteps
          (Function.update val_m m report_m) val_w (t + 1)).m_proposals m' ∧
      IsActiveMan (Function.update val_m m report_m)
        (daStateAfterSteps (Function.update val_m m report_m) val_w t) m' ∧
      BestRemainingWoman (Function.update val_m m report_m)
        (daStateAfterSteps (Function.update val_m m report_m) val_w t) m' w := by
  rcases paper_da_other_man_truthful_partner_removed_step_of_worse_after_one_man_report
      val_m val_w m m' report_m w hm' hx hworse with
    ⟨t, ht, hmem, hnot⟩
  have hproposal :=
    proposal_removed_at_daStateAfterSteps_succ
      (Function.update val_m m report_m) val_w t hmem hnot
  exact ⟨t, ht, hmem, hnot, hproposal.1, hproposal.2⟩

/--
Woman-side consequence of the Lemma 2 trace bridge: in the altered run where a
non-manipulating man is worse off, his truthful partner's final altered-run
match is weakly preferred by that woman to him.
-/
theorem paper_da_other_man_truthful_partner_final_woman_weakly_prefers_after_worse
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m m' : M) (report_m : W → ℝ) (w : W)
    (hm' : m' ≠ m)
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hworse :
      paper_matching_valM val_m m'
          ((deferredAcceptance
            (Function.update val_m m report_m) val_w).m_match m') <
        paper_matching_valM val_m m'
          ((deferredAcceptance val_m val_w).m_match m')) :
    val_w w m' ≤
      paper_matching_valW val_w w
        ((deferredAcceptance
          (Function.update val_m m report_m) val_w).w_match w) := by
  rcases paper_da_other_man_truthful_partner_removed_step_of_worse_after_one_man_report
      val_m val_w m m' report_m w hm' hx hworse with
    ⟨t, ht, hmem, hnot⟩
  have hfinal :=
    woman_final_value_ge_of_proposal_removed_at_daStateAfterSteps
      (Function.update val_m m report_m) val_w
      (steps := t) (m := m') (w := w) ht hmem hnot
  simpa [paper_matching_valW, deferredAcceptance, valW] using hfinal

/--
Strict version of the Lemma 2 trace bridge. If the altered DA outcome is
complete and women have strict preferences, the truthful partner who receives a
proposal from the worse-off non-manipulator ends the altered run with a
different man whom she strictly prefers to that non-manipulator.
-/
theorem paper_da_other_man_truthful_partner_final_woman_strictly_prefers_after_worse
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m m' : M) (report_m : W → ℝ) (w : W)
    (hm' : m' ≠ m)
    (hstrictW : ∀ w m₁ m₂, val_w w m₁ = val_w w m₂ → m₁ = m₂)
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hyCompleteW :
      ∃ mk, (deferredAcceptance
        (Function.update val_m m report_m) val_w).w_match w = some mk)
    (hworse :
      paper_matching_valM val_m m'
          ((deferredAcceptance
            (Function.update val_m m report_m) val_w).m_match m') <
        paper_matching_valM val_m m'
          ((deferredAcceptance val_m val_w).m_match m')) :
    ∃ mk,
      (deferredAcceptance
        (Function.update val_m m report_m) val_w).w_match w = some mk ∧
        mk ≠ m' ∧ val_w w m' < val_w w mk := by
  let y := deferredAcceptance (Function.update val_m m report_m) val_w
  rcases hyCompleteW with ⟨mk, hmk⟩
  have hweak :
      val_w w m' ≤ paper_matching_valW val_w w (y.w_match w) := by
    simpa [y] using
      paper_da_other_man_truthful_partner_final_woman_weakly_prefers_after_worse
        val_m val_w m m' report_m w hm' hx hworse
  have hmk_ne : mk ≠ m' := by
    intro hmk_eq
    subst mk
    have hym : y.m_match m' = some w := (y.consistent_m m' w).2 hmk
    have hlt : val_m m' w < val_m m' w := by
      simpa [paper_matching_valM, y, hx, hym] using hworse
    exact (lt_irrefl (val_m m' w)) hlt
  have hle : val_w w m' ≤ val_w w mk := by
    simpa [paper_matching_valW, y, hmk] using hweak
  have hneVal : val_w w m' ≠ val_w w mk := by
    intro heq
    exact hmk_ne ((hstrictW w m' mk heq).symm)
  exact ⟨mk, by simpa [y] using hmk, hmk_ne, lt_of_le_of_ne hle hneVal⟩

/--
Source-domain version of the strict Lemma 2 trace bridge. Equal cardinality and
the strict marriage-domain assumptions after the report update provide altered
DA completeness, so the woman who receives the worse-off non-manipulator's
proposal ends with a strictly preferred different partner.
-/
theorem paper_da_other_man_truthful_partner_final_woman_strictly_prefers_after_worse_on_strict_report
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m m' : M) (report_m : W → ℝ) (w : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hm' : m' ≠ m)
    (hdomainReport :
      paper_strict_marriage_domain (Function.update val_m m report_m) val_w)
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hworse :
      paper_matching_valM val_m m'
          ((deferredAcceptance
            (Function.update val_m m report_m) val_w).m_match m') <
        paper_matching_valM val_m m'
          ((deferredAcceptance val_m val_w).m_match m')) :
    ∃ mk,
      (deferredAcceptance
        (Function.update val_m m report_m) val_w).w_match w = some mk ∧
        mk ≠ m' ∧ val_w w m' < val_w w mk := by
  rcases hdomainReport with ⟨_hstrictM, hstrictW, hposM, hposW⟩
  have hcomplete :
      (∀ m0, ∃ w0,
          (deferredAcceptance
            (Function.update val_m m report_m) val_w).m_match m0 = some w0) ∧
        (∀ w0, ∃ m0,
          (deferredAcceptance
            (Function.update val_m m report_m) val_w).w_match w0 = some m0) := by
    exact deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
      (Function.update val_m m report_m) val_w hcard ⟨hposM, hposW⟩
  exact paper_da_other_man_truthful_partner_final_woman_strictly_prefers_after_worse
    val_m val_w m m' report_m w hm' hstrictW hx (hcomplete.2 w) hworse

/--
Original-run trace fact used in Lemma 2: if `w` ends the truthful DA run with
`m'`, then a man whom `w` strictly prefers to `m'` cannot have proposed to `w`
in that truthful run.
-/
theorem paper_da_woman_better_than_final_partner_did_not_propose
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m' mk : M) (w : W)
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hwpref : val_w w m' < val_w w mk) :
    w ∈ (deferredAcceptanceState val_m val_w).m_proposals mk := by
  by_contra hnot
  rcases paper_da_exists_proposal_removal_step_of_final_not_remaining
      val_m val_w mk w hnot with ⟨t, ht, hmem, hremoved⟩
  have hfinal :=
    woman_final_value_ge_of_proposal_removed_at_daStateAfterSteps
      val_m val_w (steps := t) (m := mk) (w := w) ht hmem hremoved
  have hxw : (deferredAcceptance val_m val_w).w_match w = some m' :=
    (deferredAcceptance val_m val_w).consistent_m m' w |>.1 hx
  have hxwState : (deferredAcceptanceState val_m val_w).w_match w = some m' := by
    simpa [deferredAcceptance] using hxw
  have hle : val_w w mk ≤ val_w w m' := by
    simpa [valW, hxwState] using hfinal
  linarith

/--
Contrapositive of the final-better-partner trace fact: if a man did not propose
to a woman in a DA run, then he does not strictly prefer her to his final
partner.
-/
theorem paper_da_unproposed_partner_not_better_than_final
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M) (w : W)
    (hremaining : w ∈ (deferredAcceptanceState val_m val_w).m_proposals m) :
    val_m m w ≤
      paper_matching_valM val_m m ((deferredAcceptance val_m val_w).m_match m) := by
  by_contra hnot
  have hbetter :
      paper_matching_valM val_m m ((deferredAcceptance val_m val_w).m_match m) <
        val_m m w := lt_of_not_ge hnot
  exact paper_da_final_better_partner_was_proposed
    val_m val_w m w hbetter hremaining

/--
Source-domain trace consequence used in Lemma 2: if woman `w = x(m')` strictly
prefers `mk` to her truthful DA partner `m'`, then `mk` did not propose to `w`
in the truthful run, and therefore strictly prefers his own truthful DA partner
to `w`.
-/
theorem paper_da_woman_better_than_final_partner_implies_man_prefers_final_to_her_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m' mk : M) (w : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hmk_ne : mk ≠ m')
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hwpref : val_w w m' < val_w w mk) :
    ∃ wk,
      (deferredAcceptance val_m val_w).m_match mk = some wk ∧
        wk ≠ w ∧ val_m mk w < val_m mk wk := by
  rcases hdomain with ⟨hstrictM, _hstrictW, hposM, hposW⟩
  have hremaining :
      w ∈ (deferredAcceptanceState val_m val_w).m_proposals mk :=
    paper_da_woman_better_than_final_partner_did_not_propose
      val_m val_w m' mk w hx hwpref
  have hcomplete :
      (∀ m0, ∃ w0, (deferredAcceptance val_m val_w).m_match m0 = some w0) ∧
        (∀ w0, ∃ m0, (deferredAcceptance val_m val_w).w_match w0 = some m0) := by
    exact deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
      val_m val_w hcard ⟨hposM, hposW⟩
  rcases hcomplete.1 mk with ⟨wk, hwk⟩
  have hwk_ne : wk ≠ w := by
    intro hwk_eq
    subst wk
    have hxw : (deferredAcceptance val_m val_w).w_match w = some m' :=
      (deferredAcceptance val_m val_w).consistent_m m' w |>.1 hx
    have hmk_w : (deferredAcceptance val_m val_w).w_match w = some mk :=
      (deferredAcceptance val_m val_w).consistent_m mk w |>.1 hwk
    have : some mk = some m' := hmk_w.symm.trans hxw
    exact hmk_ne (Option.some.inj this)
  have hweak :
      val_m mk w ≤ val_m mk wk := by
    have hweakFinal :=
      paper_da_unproposed_partner_not_better_than_final val_m val_w mk w hremaining
    simpa [paper_matching_valM, hwk] using hweakFinal
  have hneVal : val_m mk w ≠ val_m mk wk := by
    intro heq
    exact hwk_ne (hstrictM mk w wk heq).symm
  exact ⟨wk, hwk, hwk_ne, lt_of_le_of_ne hweak hneVal⟩

/--
Combined predecessor step for Roth's Lemma 2 trace. If a non-manipulating man
`m'` is worse off under another man's report, then for his truthful partner `w`
there is a different man `mk` matched to `w` in the altered run such that `w`
strictly prefers `mk` to `m'`, and `mk` strictly prefers his own truthful DA
partner to `w`.
-/
theorem paper_da_worse_other_man_yields_predecessor_chain_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m m' : M) (report_m : W → ℝ) (w : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hm' : m' ≠ m)
    (hdomainReport :
      paper_strict_marriage_domain (Function.update val_m m report_m) val_w)
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hworse :
      paper_matching_valM val_m m'
          ((deferredAcceptance
            (Function.update val_m m report_m) val_w).m_match m') <
        paper_matching_valM val_m m'
          ((deferredAcceptance val_m val_w).m_match m')) :
    ∃ mk wk,
      (deferredAcceptance
        (Function.update val_m m report_m) val_w).w_match w = some mk ∧
        mk ≠ m' ∧ val_w w m' < val_w w mk ∧
        (deferredAcceptance val_m val_w).m_match mk = some wk ∧
        wk ≠ w ∧ val_m mk w < val_m mk wk := by
  rcases
      paper_da_other_man_truthful_partner_final_woman_strictly_prefers_after_worse_on_strict_report
        val_m val_w m m' report_m w hcard hm' hdomainReport hx hworse with
    ⟨mk, hyw, hmk_ne, hwpref⟩
  rcases
      paper_da_woman_better_than_final_partner_implies_man_prefers_final_to_her_on_strict_domain
        val_m val_w m' mk w hcard hdomain hmk_ne hx hwpref with
    ⟨wk, hxmk, hwk_ne, hmkpref⟩
  exact ⟨mk, wk, hyw, hmk_ne, hwpref, hxmk, hwk_ne, hmkpref⟩

/--
Outcome-level predecessor step: a worse-off non-manipulator generates a
different man who is also worse off in the altered run.
-/
theorem paper_da_worse_other_man_yields_another_worse_man_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m m' : M) (report_m : W → ℝ) (w : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hm' : m' ≠ m)
    (hdomainReport :
      paper_strict_marriage_domain (Function.update val_m m report_m) val_w)
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hworse :
      paper_matching_valM val_m m'
          ((deferredAcceptance
            (Function.update val_m m report_m) val_w).m_match m') <
        paper_matching_valM val_m m'
          ((deferredAcceptance val_m val_w).m_match m')) :
    ∃ mk,
      mk ≠ m' ∧
        paper_matching_valM val_m mk
            ((deferredAcceptance
              (Function.update val_m m report_m) val_w).m_match mk) <
          paper_matching_valM val_m mk
            ((deferredAcceptance val_m val_w).m_match mk) := by
  rcases paper_da_worse_other_man_yields_predecessor_chain_on_strict_domain
      val_m val_w m m' report_m w hcard hdomain hm' hdomainReport hx hworse with
    ⟨mk, wk, hyw, hmk_ne, _hwpref, hxmk, _hwk_ne, hmkpref⟩
  have hymk :
      (deferredAcceptance
        (Function.update val_m m report_m) val_w).m_match mk = some w :=
    (deferredAcceptance
      (Function.update val_m m report_m) val_w).consistent_m mk w |>.2 hyw
  exact ⟨mk, hmk_ne, by
    simpa [paper_matching_valM, hymk, hxmk] using hmkpref⟩

/--
First-crossing version of the Lemma 2 rejection trace. If a non-manipulating
man `m'` is worse off under `m`'s report, then for his truthful partner `w`
there is a first altered-run step at which `w` holds someone she strictly
prefers to `m'`.
-/
theorem paper_da_other_man_truthful_partner_first_strictly_better_holder_step_after_worse
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m m' : M) (report_m : W → ℝ) (w : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hm' : m' ≠ m)
    (hdomainReport :
      paper_strict_marriage_domain (Function.update val_m m report_m) val_w)
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hworse :
      paper_matching_valM val_m m'
          ((deferredAcceptance
            (Function.update val_m m report_m) val_w).m_match m') <
        paper_matching_valM val_m m'
          ((deferredAcceptance val_m val_w).m_match m')) :
    ∃ t mk,
      t < Fintype.card M * Fintype.card W ∧
        ¬ val_w w m' <
          valW val_w w
            ((daStateAfterSteps
              (Function.update val_m m report_m) val_w t).w_match w) ∧
        val_w w m' <
          valW val_w w
            ((daStateAfterSteps
              (Function.update val_m m report_m) val_w (t + 1)).w_match w) ∧
        IsActiveMan (Function.update val_m m report_m)
          (daStateAfterSteps (Function.update val_m m report_m) val_w t) mk ∧
        BestRemainingWoman (Function.update val_m m report_m)
          (daStateAfterSteps (Function.update val_m m report_m) val_w t) mk w ∧
        (daStateAfterSteps
          (Function.update val_m m report_m) val_w (t + 1)).w_match w =
            some mk ∧
        mk ≠ m' ∧ val_w w m' < val_w w mk := by
  rcases hdomain with ⟨_hstrictM, _hstrictW, _hposM, hposW⟩
  rcases
      paper_da_other_man_truthful_partner_final_woman_strictly_prefers_after_worse_on_strict_report
        val_m val_w m m' report_m w hcard hm' hdomainReport hx hworse with
    ⟨mkFinal, hywFinal, _hmkFinal_ne, hwprefFinal⟩
  let N := Fintype.card M * Fintype.card W
  have hstart :
      ¬ val_w w m' <
        valW val_w w
          ((daStateAfterSteps
            (Function.update val_m m report_m) val_w 0).w_match w) := by
    have hpos : 0 < val_w w m' := hposW w m'
    simp [initialDAState, valW]
    linarith
  have hend :
      val_w w m' <
        valW val_w w
          ((daStateAfterSteps
            (Function.update val_m m report_m) val_w N).w_match w) := by
    have hywState :
        (daStateAfterSteps
          (Function.update val_m m report_m) val_w N).w_match w =
            some mkFinal := by
      simpa [N, deferredAcceptance, deferredAcceptanceState_eq_daStateAfterSteps]
        using hywFinal
    simpa [valW, hywState] using hwprefFinal
  rcases exists_woman_threshold_crossing_step_before
      (Function.update val_m m report_m) val_w hstart hend with
    ⟨t, ht, hbefore, hafter⟩
  rcases woman_threshold_crossed_at_daStateAfterSteps_succ
      (Function.update val_m m report_m) val_w t w m' (le_of_not_gt hbefore)
      hafter with
    ⟨mk, hact, hbest, hmatch, hwpref⟩
  have hmk_ne : mk ≠ m' := by
    intro hmk
    subst mk
    exact (lt_irrefl (val_w w m')) hwpref
  exact ⟨t, mk, by simpa [N] using ht, hbefore, hafter, hact, hbest,
    hmatch, hmk_ne, hwpref⟩

/--
Predecessor-timing bridge for Lemma 2. At a crossing step for `x(m')`, if the
crossing proposer `mk` is not the manipulating man, then `mk`'s own truthful DA
partner was removed from his altered-run proposal set at a strictly earlier
step.
-/
theorem paper_da_crossing_proposer_truthful_partner_removed_before_crossing
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m m' mk : M) (report_m : W → ℝ) (w : W) (t : ℕ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hmk_ne_m : mk ≠ m)
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hbest :
      BestRemainingWoman (Function.update val_m m report_m)
        (daStateAfterSteps (Function.update val_m m report_m) val_w t) mk w)
    (hwpref : val_w w m' < val_w w mk) :
    ∃ wk tk,
      (deferredAcceptance val_m val_w).m_match mk = some wk ∧
        wk ≠ w ∧
        val_m mk w < val_m mk wk ∧
        tk < t ∧
        wk ∈ (daStateAfterSteps
          (Function.update val_m m report_m) val_w tk).m_proposals mk ∧
        wk ∉ (daStateAfterSteps
          (Function.update val_m m report_m) val_w (tk + 1)).m_proposals mk := by
  rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hdomainFull : paper_strict_marriage_domain val_m val_w :=
    ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hmk_ne_m' : mk ≠ m' := by
    intro hmk
    subst mk
    exact (lt_irrefl (val_w w m')) hwpref
  rcases
      paper_da_woman_better_than_final_partner_implies_man_prefers_final_to_her_on_strict_domain
        val_m val_w m' mk w hcard hdomainFull hmk_ne_m' hx hwpref with
    ⟨wk, hxmk, hwk_ne, hmkpref⟩
  have hnotwk :
      wk ∉ (daStateAfterSteps
        (Function.update val_m m report_m) val_w t).m_proposals mk := by
    intro hmem
    have hnonneg :
        0 ≤ (Function.update val_m m report_m) mk wk := by
      have hpos : 0 < val_m mk wk := hposM mk wk
      simpa [Function.update, hmk_ne_m] using le_of_lt hpos
    have hleReported :=
      hbest.2.2 wk hmem hnonneg
    have hleTrue : val_m mk wk ≤ val_m mk w := by
      simpa [Function.update, hmk_ne_m] using hleReported
    linarith
  rcases
      exists_proposal_removal_step_before_of_not_mem_daStateAfterSteps
        (Function.update val_m m report_m) val_w hnotwk with
    ⟨tk, htk, hmem, hnot⟩
  exact ⟨wk, tk, hxmk, hwk_ne, hmkpref, htk, hmem, hnot⟩

/--
Packaged Lemma 2 timing branch. A worse-off non-manipulator yields a first
crossing at his truthful partner. At that crossing, either the proposer is the
manipulator, or the proposer's own truthful partner was removed at a strictly
earlier altered-run step.
-/
theorem paper_da_worse_other_man_yields_first_crossing_or_earlier_predecessor
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m m' : M) (report_m : W → ℝ) (w : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hm' : m' ≠ m)
    (hdomainReport :
      paper_strict_marriage_domain (Function.update val_m m report_m) val_w)
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hworse :
      paper_matching_valM val_m m'
          ((deferredAcceptance
            (Function.update val_m m report_m) val_w).m_match m') <
        paper_matching_valM val_m m'
          ((deferredAcceptance val_m val_w).m_match m')) :
    ∃ t mk,
      t < Fintype.card M * Fintype.card W ∧
        ¬ val_w w m' <
          valW val_w w
            ((daStateAfterSteps
              (Function.update val_m m report_m) val_w t).w_match w) ∧
        val_w w m' <
          valW val_w w
            ((daStateAfterSteps
              (Function.update val_m m report_m) val_w (t + 1)).w_match w) ∧
        IsActiveMan (Function.update val_m m report_m)
          (daStateAfterSteps (Function.update val_m m report_m) val_w t) mk ∧
        BestRemainingWoman (Function.update val_m m report_m)
          (daStateAfterSteps (Function.update val_m m report_m) val_w t) mk w ∧
        (daStateAfterSteps
          (Function.update val_m m report_m) val_w (t + 1)).w_match w =
            some mk ∧
        mk ≠ m' ∧ val_w w m' < val_w w mk ∧
        (mk = m ∨
          ∃ wk tk,
            (deferredAcceptance val_m val_w).m_match mk = some wk ∧
              wk ≠ w ∧
              val_m mk w < val_m mk wk ∧
              tk < t ∧
              wk ∈ (daStateAfterSteps
                (Function.update val_m m report_m) val_w tk).m_proposals mk ∧
              wk ∉ (daStateAfterSteps
                (Function.update val_m m report_m) val_w (tk + 1)).m_proposals mk) := by
  rcases
      paper_da_other_man_truthful_partner_first_strictly_better_holder_step_after_worse
        val_m val_w m m' report_m w hcard hdomain hm' hdomainReport hx hworse with
    ⟨t, mk, ht, hbefore, hafter, hact, hbest, hmatch, hmk_ne_m', hwpref⟩
  by_cases hmk_m : mk = m
  · exact ⟨t, mk, ht, hbefore, hafter, hact, hbest, hmatch, hmk_ne_m',
      hwpref, Or.inl hmk_m⟩
  · rcases
        paper_da_crossing_proposer_truthful_partner_removed_before_crossing
          val_m val_w m m' mk report_m w t hcard hdomain hmk_m hx hbest hwpref with
      ⟨wk, tk, hxmk, hwk_ne, hmkpref, htk, hmem, hnot⟩
    exact ⟨t, mk, ht, hbefore, hafter, hact, hbest, hmatch, hmk_ne_m',
      hwpref, Or.inr ⟨wk, tk, hxmk, hwk_ne, hmkpref, htk, hmem, hnot⟩⟩

/--
Simple-report branch exclusion for Lemma 2. If the manipulating man weakly
prefers the simple-report DA outcome to the truthful DA outcome and the simple
report ranks his final partner uniquely first, then the first crossing proposer
for a worse-off non-manipulator cannot be the manipulating man.
-/
theorem paper_da_simple_report_first_crossing_proposer_ne_manipulator
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m m' mk : M) (simple_report_m : W → ℝ) (w ystar : W) (t : ℕ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hm' : m' ≠ m)
    (hdomainReport :
      paper_strict_marriage_domain
        (Function.update val_m m simple_report_m) val_w)
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hy :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hweakM :
      paper_man_weakly_prefers_outcome val_m m
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w))
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar))
    (ht : t < Fintype.card M * Fintype.card W)
    (hact :
      IsActiveMan (Function.update val_m m simple_report_m)
        (daStateAfterSteps
          (Function.update val_m m simple_report_m) val_w t) mk)
    (hbest :
      BestRemainingWoman (Function.update val_m m simple_report_m)
        (daStateAfterSteps
          (Function.update val_m m simple_report_m) val_w t) mk w)
    (hwpref : val_w w m' < val_w w mk) :
    mk ≠ m := by
  intro hmk
  subst mk
  by_cases hw_y : w = ystar
  · subst ystar
    have hm_ne_m' : m ≠ m' := fun h => hm' h.symm
    rcases
        paper_da_woman_better_than_final_partner_implies_man_prefers_final_to_her_on_strict_domain
          val_m val_w m' m w hcard hdomain hm_ne_m' hx hwpref with
      ⟨wk, hxmk, _hwk_ne, hmpref⟩
    have hweak : val_m m wk ≤ val_m m w := by
      simpa [paper_man_weakly_prefers_outcome, paper_matching_valM, hxmk, hy]
        using hweakM
    linarith
  · have hnotY :
        ystar ∉ (daStateAfterSteps
          (Function.update val_m m simple_report_m) val_w t).m_proposals m := by
      intro hmemY
      have hposReport :
          0 <
            (Function.update val_m m simple_report_m) m ystar :=
        hdomainReport.2.2.1 m ystar
      have hleReported :=
        hbest.2.2 ystar hmemY (le_of_lt hposReport)
      have hleSimple : simple_report_m ystar ≤ simple_report_m w := by
        simpa [Function.update] using hleReported
      have hltSimple : simple_report_m w < simple_report_m ystar := by
        simpa [paper_man_report_strictly_ranks_partner_first] using hfirst w hw_y
      linarith
    have hnotMatchAtT :
        (daStateAfterSteps
          (Function.update val_m m simple_report_m) val_w t).m_match m ≠
            some ystar := by
      rw [hact.1]
      simp
    have hnotFinal :
        (deferredAcceptanceState
          (Function.update val_m m simple_report_m) val_w).m_match m ≠
            some ystar :=
      m_match_ne_deferredAcceptanceState_of_not_mem_after_steps
        (Function.update val_m m simple_report_m) val_w
        (Nat.le_of_lt ht) hnotY hnotMatchAtT
    have hyState :
        (deferredAcceptanceState
          (Function.update val_m m simple_report_m) val_w).m_match m =
            some ystar := by
      simpa [deferredAcceptance] using hy
    exact hnotFinal hyState

/--
For a strict simple report that does not hurt the manipulating man, a worse-off
non-manipulator yields a strictly earlier predecessor proposal-removal event.
This is the formal induction step Roth uses in Lemma 2.
-/
theorem paper_da_simple_report_worse_other_man_yields_earlier_predecessor_removal
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m m' : M) (simple_report_m : W → ℝ) (w ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hm' : m' ≠ m)
    (hdomainReport :
      paper_strict_marriage_domain
        (Function.update val_m m simple_report_m) val_w)
    (hx : (deferredAcceptance val_m val_w).m_match m' = some w)
    (hy :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hweakM :
      paper_man_weakly_prefers_outcome val_m m
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w))
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar))
    (hworse :
      paper_matching_valM val_m m'
          ((deferredAcceptance
            (Function.update val_m m simple_report_m) val_w).m_match m') <
        paper_matching_valM val_m m'
          ((deferredAcceptance val_m val_w).m_match m')) :
    ∃ t mk wk tk,
      t < Fintype.card M * Fintype.card W ∧
        ¬ val_w w m' <
          valW val_w w
            ((daStateAfterSteps
              (Function.update val_m m simple_report_m) val_w t).w_match w) ∧
        val_w w m' <
          valW val_w w
            ((daStateAfterSteps
              (Function.update val_m m simple_report_m) val_w (t + 1)).w_match w) ∧
        IsActiveMan (Function.update val_m m simple_report_m)
          (daStateAfterSteps
            (Function.update val_m m simple_report_m) val_w t) mk ∧
        BestRemainingWoman (Function.update val_m m simple_report_m)
          (daStateAfterSteps
            (Function.update val_m m simple_report_m) val_w t) mk w ∧
        (daStateAfterSteps
          (Function.update val_m m simple_report_m) val_w (t + 1)).w_match w =
            some mk ∧
        mk ≠ m' ∧ val_w w m' < val_w w mk ∧
        (deferredAcceptance val_m val_w).m_match mk = some wk ∧
        wk ≠ w ∧
        val_m mk w < val_m mk wk ∧
        tk < t ∧
        wk ∈ (daStateAfterSteps
          (Function.update val_m m simple_report_m) val_w tk).m_proposals mk ∧
        wk ∉ (daStateAfterSteps
          (Function.update val_m m simple_report_m) val_w (tk + 1)).m_proposals mk := by
  rcases
      paper_da_worse_other_man_yields_first_crossing_or_earlier_predecessor
        val_m val_w m m' simple_report_m w hcard hdomain hm' hdomainReport
        hx hworse with
    ⟨t, mk, ht, hbefore, hafter, hact, hbest, hmatch, hmk_ne_m',
      hwpref, hbranch⟩
  have hmk_ne_m :
      mk ≠ m :=
    paper_da_simple_report_first_crossing_proposer_ne_manipulator
      val_m val_w m m' mk simple_report_m w ystar t hcard hdomain hm'
      hdomainReport hx hy hweakM hfirst ht hact hbest hwpref
  rcases hbranch with hmk_eq_m | ⟨wk, tk, hxmk, hwk_ne, hmkpref, htk, hmem, hnot⟩
  · exact False.elim (hmk_ne_m hmk_eq_m)
  · exact ⟨t, mk, wk, tk, ht, hbefore, hafter, hact, hbest, hmatch,
      hmk_ne_m', hwpref, hxmk, hwk_ne, hmkpref, htk, hmem, hnot⟩

/--
If a non-manipulating proposer has already spent the proposal to his truthful
DA partner and is later active, then that truthful partner must have crossed to
a strictly better holder at an earlier time. This supplies the decreasing
time measure in Roth's Lemma 2 proof.
-/
theorem paper_da_removed_truthful_partner_before_active_step_yields_earlier_crossing
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m mk : M) (simple_report_m : W → ℝ) (wk : W) (t tk : ℕ)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (htk : tk < t)
    (hremoved :
      wk ∉ (daStateAfterSteps
        (Function.update val_m m simple_report_m) val_w (tk + 1)).m_proposals mk)
    (hact :
      IsActiveMan (Function.update val_m m simple_report_m)
        (daStateAfterSteps
          (Function.update val_m m simple_report_m) val_w t) mk) :
    ∃ tc, tc < t ∧
      ¬ val_w wk mk <
        valW val_w wk
          ((daStateAfterSteps
            (Function.update val_m m simple_report_m) val_w tc).w_match wk) ∧
      val_w wk mk <
        valW val_w wk
          ((daStateAfterSteps
            (Function.update val_m m simple_report_m) val_w (tc + 1)).w_match wk) := by
  rcases hdomain with ⟨_hstrictM, hstrictW, _hposM, hposW⟩
  let reported := Function.update val_m m simple_report_m
  have hnotAtT :
      wk ∉ (daStateAfterSteps reported val_w t).m_proposals mk := by
    exact not_mem_daStateAfterSteps_of_not_mem_of_le reported val_w
      (Nat.succ_le_of_lt htk) hremoved
  have hnotMatchedAtT :
      (daStateAfterSteps reported val_w t).m_match mk ≠ some wk := by
    rw [hact.1]
    simp
  have hinv :
      DAInvariants reported val_w (daStateAfterSteps reported val_w t) :=
    daStateAfterSteps_satisfies_invariants reported val_w t
  have hthresholdT :
      val_w wk mk <
        valW val_w wk ((daStateAfterSteps reported val_w t).w_match wk) := by
    rcases hinv.2.2.2.1 wk mk hnotAtT hnotMatchedAtT with
      hneg | ⟨mcur, hwcur, hle⟩
    · have hpos := hposW wk mk
      linarith
    · have hmcur_ne : mcur ≠ mk := by
        intro hmcur
        subst mcur
        have hmatch : (daStateAfterSteps reported val_w t).m_match mk = some wk :=
          (daStateAfterSteps reported val_w t).consistent mk wk |>.2 hwcur
        exact hnotMatchedAtT hmatch
      have hneVal : val_w wk mk ≠ val_w wk mcur := by
        intro heq
        exact hmcur_ne ((hstrictW wk mk mcur heq).symm)
      have hstrict : val_w wk mk < val_w wk mcur :=
        lt_of_le_of_ne hle hneVal
      simpa [valW, hwcur] using hstrict
  have hstart :
      ¬ val_w wk mk <
        valW val_w wk
          ((daStateAfterSteps reported val_w 0).w_match wk) := by
    have hpos := hposW wk mk
    simp [reported, initialDAState, valW]
    linarith
  rcases exists_woman_threshold_crossing_step_before reported val_w hstart hthresholdT with
    ⟨tc, htc, hbefore, hafter⟩
  exact ⟨tc, htc, hbefore, hafter⟩

/--
Minimal-time contradiction for Roth's Lemma 2. Under a strict simple report
that leaves the manipulator weakly better off, no non-manipulating man's
truthful DA partner can ever cross to a strictly better holder in the altered
run.
-/
theorem paper_da_simple_report_no_nonmanipulator_truthful_partner_crossing
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (simple_report_m : W → ℝ) (ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hdomainReport :
      paper_strict_marriage_domain
        (Function.update val_m m simple_report_m) val_w)
    (hy :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hweakM :
      paper_man_weakly_prefers_outcome val_m m
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w))
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar)) :
    ¬ ∃ t i wi,
      t < Fintype.card M * Fintype.card W ∧
        i ≠ m ∧
        (deferredAcceptance val_m val_w).m_match i = some wi ∧
        ¬ val_w wi i <
          valW val_w wi
            ((daStateAfterSteps
              (Function.update val_m m simple_report_m) val_w t).w_match wi) ∧
        val_w wi i <
          valW val_w wi
            ((daStateAfterSteps
              (Function.update val_m m simple_report_m) val_w (t + 1)).w_match wi) := by
  intro hbad
  let reported := Function.update val_m m simple_report_m
  let N := Fintype.card M * Fintype.card W
  let P : ℕ → Prop := fun t =>
    ∃ i wi,
      t < N ∧
        i ≠ m ∧
        (deferredAcceptance val_m val_w).m_match i = some wi ∧
        ¬ val_w wi i <
          valW val_w wi ((daStateAfterSteps reported val_w t).w_match wi) ∧
        val_w wi i <
          valW val_w wi ((daStateAfterSteps reported val_w (t + 1)).w_match wi)
  have hExists : ∃ t, P t := by
    rcases hbad with ⟨t, i, wi, ht, hi, hxi, hbefore, hafter⟩
    exact ⟨t, i, wi, by simpa [N] using ht, hi, hxi, by simpa [reported] using hbefore,
      by simpa [reported] using hafter⟩
  let t0 := Nat.find hExists
  have ht0P : P t0 := Nat.find_spec hExists
  rcases ht0P with ⟨i, wi, ht0, hi_ne_m, hxi, hbefore, hafter⟩
  rcases woman_threshold_crossed_at_daStateAfterSteps_succ
      reported val_w t0 wi i (le_of_not_gt hbefore) hafter with
    ⟨mk, hact, hbest, _hmatch, hwpref⟩
  have hmk_ne_m :
      mk ≠ m :=
    paper_da_simple_report_first_crossing_proposer_ne_manipulator
      val_m val_w m i mk simple_report_m wi ystar t0 hcard hdomain hi_ne_m
      hdomainReport hxi hy hweakM hfirst (by simpa [N] using ht0)
      (by simpa [reported] using hact)
      (by simpa [reported] using hbest)
      hwpref
  rcases
      paper_da_crossing_proposer_truthful_partner_removed_before_crossing
        val_m val_w m i mk simple_report_m wi t0 hcard hdomain hmk_ne_m
        hxi (by simpa [reported] using hbest) hwpref with
    ⟨wk, tk, hxmk, _hwk_ne, _hmkpref, htk, _hmem, hremoved⟩
  rcases
      paper_da_removed_truthful_partner_before_active_step_yields_earlier_crossing
        val_m val_w m mk simple_report_m wk t0 tk hdomain htk
        (by simpa [reported] using hremoved)
        (by simpa [reported] using hact) with
    ⟨tc, htc, hbeforeC, hafterC⟩
  have hPtc : P tc := by
    exact ⟨mk, wk, lt_trans htc ht0, hmk_ne_m, hxmk, by simpa [reported] using hbeforeC,
      by simpa [reported] using hafterC⟩
  have hmin : t0 ≤ tc := Nat.find_min' hExists hPtc
  exact (not_lt_of_ge hmin) htc

/--
Lemma 2 source-route theorem on Roth's equal-size strict marriage domain:
under a strict simple report that leaves the manipulating man weakly better off,
every man weakly prefers the altered DA outcome to the truthful DA outcome.
-/
theorem paper_da_strict_simple_report_no_men_harmed_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (simple_report_m : W → ℝ) (ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hdomainReport :
      paper_strict_marriage_domain
        (Function.update val_m m simple_report_m) val_w)
    (hy :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hweakM :
      paper_man_weakly_prefers_outcome val_m m
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w))
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar)) :
    ∀ m',
      paper_man_weakly_prefers_outcome val_m m'
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w) := by
  have hdomainFull : paper_strict_marriage_domain val_m val_w := hdomain
  rcases hdomain with ⟨_hstrictM, _hstrictW, hposM, hposW⟩
  have hcompleteX :
      (∀ i, ∃ w, (deferredAcceptance val_m val_w).m_match i = some w) ∧
        (∀ w, ∃ i, (deferredAcceptance val_m val_w).w_match w = some i) := by
    exact deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
      val_m val_w hcard ⟨hposM, hposW⟩
  have hnoCross :=
    paper_da_simple_report_no_nonmanipulator_truthful_partner_crossing
      val_m val_w m simple_report_m ystar hcard hdomainFull hdomainReport
      hy hweakM hfirst
  intro m'
  by_cases hm' : m' = m
  · subst m'
    exact hweakM
  · by_contra hnotWeak
    have hworse :
        paper_matching_valM val_m m'
            ((deferredAcceptance
              (Function.update val_m m simple_report_m) val_w).m_match m') <
          paper_matching_valM val_m m'
            ((deferredAcceptance val_m val_w).m_match m') :=
      lt_of_not_ge hnotWeak
    rcases hcompleteX.1 m' with ⟨w, hx⟩
    rcases
        paper_da_other_man_truthful_partner_first_strictly_better_holder_step_after_worse
          val_m val_w m m' simple_report_m w hcard hdomainFull hm'
          hdomainReport hx hworse with
      ⟨t, _mk, ht, hbefore, hafter, _hact, _hbest, _hmatch, _hmk_ne, _hwpref⟩
    exact hnoCross ⟨t, m', w, ht, hm', hx, hbefore, hafter⟩

/--
Roth Lemma 2 on the equal-size strict domain, stated with the strict simple
report used in the source proof.
-/
theorem paper_roth82_lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (simple_report_m : W → ℝ) (ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hdomainReport :
      paper_strict_marriage_domain
        (Function.update val_m m simple_report_m) val_w)
    (hy :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hweakM :
      paper_man_weakly_prefers_outcome val_m m
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w))
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar)) :
    ∀ m',
      paper_man_weakly_prefers_outcome val_m m'
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w) := by
  exact paper_da_strict_simple_report_no_men_harmed_on_strict_domain
    val_m val_w m simple_report_m ystar hcard hdomain hdomainReport hy
    hweakM hfirst

/--
Theorem 5 trace bridge after Lemma 2. If a non-manipulating man is not worse
off in the altered run, then he cannot newly propose to a woman he truly ranks
below his truthful DA partner.
-/
theorem paper_da_no_worse_nonmanipulator_does_not_propose_below_truthful_partner
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m mk : M) (simple_report_m : W → ℝ) (w wk : W)
    (hmk_ne_m : mk ≠ m)
    (hposM : ∀ m w, 0 < val_m m w)
    (hxmk : (deferredAcceptance val_m val_w).m_match mk = some wk)
    (hweak :
      paper_man_weakly_prefers_outcome val_m mk
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w))
    (hpref : val_m mk w < val_m mk wk) :
    w ∈ (deferredAcceptanceState
      (Function.update val_m m simple_report_m) val_w).m_proposals mk := by
  let reported := Function.update val_m m simple_report_m
  by_contra hnot
  rcases paper_da_exists_proposal_removal_step_of_final_not_remaining
      reported val_w mk w hnot with
    ⟨t, ht, hmem, hremoved⟩
  have hproposal :=
    proposal_removed_at_daStateAfterSteps_succ reported val_w t hmem hremoved
  cases hy :
      (deferredAcceptance reported val_w).m_match mk with
  | none =>
      have hweak' : val_m mk wk ≤ 0 := by
        simpa [paper_man_weakly_prefers_outcome, paper_matching_valM,
          reported, hxmk, hy] using hweak
      have hpos := hposM mk wk
      linarith
  | some wy =>
      have hge : val_m mk wk ≤ val_m mk wy := by
        simpa [paper_man_weakly_prefers_outcome, paper_matching_valM,
          reported, hxmk, hy] using hweak
      have hwy_gt_w : val_m mk w < val_m mk wy := lt_of_lt_of_le hpref hge
      have hnotWyAtT :
          wy ∉ (daStateAfterSteps reported val_w t).m_proposals mk := by
        intro hmemWy
        have hnonneg : 0 ≤ reported mk wy := by
          have hpos := hposM mk wy
          simpa [reported, Function.update, hmk_ne_m] using le_of_lt hpos
        have hleReported := hproposal.2.2.2 wy hmemWy hnonneg
        have hleTrue : val_m mk wy ≤ val_m mk w := by
          simpa [reported, Function.update, hmk_ne_m] using hleReported
        linarith
      have hnotMatchAtT :
          (daStateAfterSteps reported val_w t).m_match mk ≠ some wy := by
        rw [hproposal.1.1]
        simp
      have hnotFinal :
          (deferredAcceptanceState reported val_w).m_match mk ≠ some wy :=
        m_match_ne_deferredAcceptanceState_of_not_mem_after_steps
          reported val_w (Nat.le_of_lt ht) hnotWyAtT hnotMatchAtT
      have hyState :
          (deferredAcceptanceState reported val_w).m_match mk = some wy := by
        simpa [deferredAcceptance, reported] using hy
      exact hnotFinal hyState

/--
Manipulator-inclusive version of the no-new-low-proposal bridge. The
manipulator case uses the strict simple report's unique top final partner; all
other men use unchanged preferences.
-/
theorem paper_da_no_worse_man_does_not_propose_below_truthful_partner_of_simple_report
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m mk : M) (simple_report_m : W → ℝ) (w wk ystar : W)
    (hposM : ∀ m w, 0 < val_m m w)
    (hdomainReport :
      paper_strict_marriage_domain
        (Function.update val_m m simple_report_m) val_w)
    (hxmk : (deferredAcceptance val_m val_w).m_match mk = some wk)
    (hy :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar))
    (hweak :
      paper_man_weakly_prefers_outcome val_m mk
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w))
    (hpref : val_m mk w < val_m mk wk) :
    w ∈ (deferredAcceptanceState
      (Function.update val_m m simple_report_m) val_w).m_proposals mk := by
  by_cases hmk_ne_m : mk ≠ m
  · exact paper_da_no_worse_nonmanipulator_does_not_propose_below_truthful_partner
      val_m val_w m mk simple_report_m w wk hmk_ne_m hposM hxmk hweak hpref
  · have hmk_eq_m : mk = m := by
      exact of_not_not hmk_ne_m
    subst mk
    let reported := Function.update val_m m simple_report_m
    by_contra hnot
    rcases paper_da_exists_proposal_removal_step_of_final_not_remaining
        reported val_w m w hnot with
      ⟨t, ht, hmem, hremoved⟩
    have hproposal :=
      proposal_removed_at_daStateAfterSteps_succ reported val_w t hmem hremoved
    by_cases hw_y : w = ystar
    · subst ystar
      have hweak' : val_m m wk ≤ val_m m w := by
        simpa [paper_man_weakly_prefers_outcome, paper_matching_valM,
          reported, hxmk, hy] using hweak
      linarith
    · have hnotYAtT :
          ystar ∉ (daStateAfterSteps reported val_w t).m_proposals m := by
        intro hmemY
        have hposReport :
            0 < reported m ystar :=
          hdomainReport.2.2.1 m ystar
        have hleReported := hproposal.2.2.2 ystar hmemY (le_of_lt hposReport)
        have hleSimple : simple_report_m ystar ≤ simple_report_m w := by
          simpa [reported, Function.update] using hleReported
        have hltSimple : simple_report_m w < simple_report_m ystar := by
          simpa [paper_man_report_strictly_ranks_partner_first] using hfirst w hw_y
        linarith
      have hnotMatchAtT :
          (daStateAfterSteps reported val_w t).m_match m ≠ some ystar := by
        rw [hproposal.1.1]
        simp
      have hnotFinal :
          (deferredAcceptanceState reported val_w).m_match m ≠ some ystar :=
        m_match_ne_deferredAcceptanceState_of_not_mem_after_steps
          reported val_w (Nat.le_of_lt ht) hnotYAtT hnotMatchAtT
      have hyState :
          (deferredAcceptanceState reported val_w).m_match m = some ystar := by
        simpa [deferredAcceptance, reported] using hy
      exact hnotFinal hyState

/--
Theorem 5 base trace: if `mq` was the only truthful-run proposer to his truthful
DA partner, then any strict simple-report run in which no man is worse off keeps
`mq` matched to that partner.
-/
theorem paper_da_unique_truthful_proposer_fixed_under_simple_report_no_worse
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m mq : M) (simple_report_m : W → ℝ) (w ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hdomainReport :
      paper_strict_marriage_domain
        (Function.update val_m m simple_report_m) val_w)
    (hxq : (deferredAcceptance val_m val_w).m_match mq = some w)
    (honly :
      ∀ r, r ≠ mq →
        w ∈ (deferredAcceptanceState val_m val_w).m_proposals r)
    (hyM :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar))
    (hallWeak :
      ∀ r,
        paper_man_weakly_prefers_outcome val_m r
          (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
          (deferredAcceptance val_m val_w)) :
    (deferredAcceptance
      (Function.update val_m m simple_report_m) val_w).m_match mq = some w := by
  let reported := Function.update val_m m simple_report_m
  let x := deferredAcceptance val_m val_w
  let y := deferredAcceptance reported val_w
  rcases hdomain with ⟨hstrictM, _hstrictW, hposM, hposW⟩
  have hcompleteX :
      (∀ r, ∃ wr, x.m_match r = some wr) ∧
        (∀ wr, ∃ r, x.w_match wr = some r) := by
    simpa [x] using
      deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
        val_m val_w hcard ⟨hposM, hposW⟩
  have hcompleteY :
      (∀ r, ∃ wr, y.m_match r = some wr) ∧
        (∀ wr, ∃ r, y.w_match wr = some r) := by
    simpa [y, reported] using
      deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
        reported val_w hcard ⟨hdomainReport.2.2.1, hdomainReport.2.2.2⟩
  rcases hcompleteY.2 w with ⟨r, hyrw⟩
  have hyr : y.m_match r = some w := y.consistent_m r w |>.2 hyrw
  by_cases hr : r = mq
  · subst r
    simpa [y] using hyr
  · have hremainingX :
        w ∈ (deferredAcceptanceState val_m val_w).m_proposals r :=
      honly r hr
    rcases hcompleteX.1 r with ⟨wk, hxrk⟩
    have hleWeak :
        val_m r w ≤ val_m r wk := by
      have hweakFinal :=
        paper_da_unproposed_partner_not_better_than_final val_m val_w r w
          hremainingX
      simpa [x, paper_matching_valM, hxrk] using hweakFinal
    have hwk_ne_w : wk ≠ w := by
      intro hwk
      subst wk
      have hxw_mq : x.w_match w = some mq := x.consistent_m mq w |>.1 (by
        simpa [x] using hxq)
      have hxw_r : x.w_match w = some r := x.consistent_m r w |>.1 hxrk
      have : some r = some mq := hxw_r.symm.trans hxw_mq
      exact hr (Option.some.inj this)
    have hneVal : val_m r w ≠ val_m r wk := by
      intro heq
      exact hwk_ne_w ((hstrictM r w wk heq).symm)
    have hpref : val_m r w < val_m r wk :=
      lt_of_le_of_ne hleWeak hneVal
    have hremainingY :
        w ∈ (deferredAcceptanceState reported val_w).m_proposals r := by
      exact paper_da_no_worse_man_does_not_propose_below_truthful_partner_of_simple_report
        val_m val_w m r simple_report_m w wk ystar hposM hdomainReport
        (by simpa [x] using hxrk) (by simpa [y, reported] using hyM)
        hfirst (by simpa [x, y, reported] using hallWeak r) hpref
    have hinvY :
        DAInvariants reported val_w (deferredAcceptanceState reported val_w) :=
      deferredAcceptanceState_satisfies_invariants_closed reported val_w
    have hnotY :
        w ∉ (deferredAcceptanceState reported val_w).m_proposals r :=
      hinvY.2.2.1 r w (by simpa [y, deferredAcceptance, reported] using hyr)
    exact False.elim (hnotY hremainingY)

/--
Theorem 5 base case for the manipulator. If the manipulator's truthful DA
partner had no other proposers in the truthful run, then a strict simple report
that does not hurt him leaves him with that truthful partner.
-/
theorem paper_da_simple_report_manipulator_fixed_of_unique_truthful_partner_proposer
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (simple_report_m : W → ℝ) (w ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hdomainReport :
      paper_strict_marriage_domain
        (Function.update val_m m simple_report_m) val_w)
    (hxM : (deferredAcceptance val_m val_w).m_match m = some w)
    (honly :
      ∀ r, r ≠ m →
        w ∈ (deferredAcceptanceState val_m val_w).m_proposals r)
    (hyM :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hweakM :
      paper_man_weakly_prefers_outcome val_m m
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w))
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar)) :
    (deferredAcceptance
      (Function.update val_m m simple_report_m) val_w).m_match m = some w := by
  have hallWeak :=
    paper_da_strict_simple_report_no_men_harmed_on_strict_domain
      val_m val_w m simple_report_m ystar hcard hdomain hdomainReport
      hyM hweakM hfirst
  exact paper_da_unique_truthful_proposer_fixed_under_simple_report_no_worse
    val_m val_w m m simple_report_m w ystar hcard hdomain hdomainReport
    hxM honly hyM hfirst hallWeak

/--
Truthful DA match-time predicate: man `mq` makes his truthful final match with
`w` at DA prefix `t`, meaning the proposal opportunity to `w` is removed at
that step and `w` is his final truthful DA partner.
-/
def paper_da_truthful_match_step
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mq : M) (w : W) (t : ℕ) : Prop :=
  (deferredAcceptance val_m val_w).m_match mq = some w ∧
    t < Fintype.card M * Fintype.card W ∧
      w ∈ (daStateAfterSteps val_m val_w t).m_proposals mq ∧
      w ∉ (daStateAfterSteps val_m val_w (t + 1)).m_proposals mq

/-- Every complete truthful DA partner has a concrete truthful match step. -/
theorem paper_da_exists_truthful_match_step
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mq : M) (w : W)
    (hxq : (deferredAcceptance val_m val_w).m_match mq = some w) :
    ∃ t, paper_da_truthful_match_step val_m val_w mq w t := by
  have hinv :
      DAInvariants val_m val_w (deferredAcceptanceState val_m val_w) :=
    deferredAcceptanceState_satisfies_invariants_closed val_m val_w
  have hxqState :
      (deferredAcceptanceState val_m val_w).m_match mq = some w := by
    simpa [deferredAcceptance] using hxq
  have hnot :
      w ∉ (deferredAcceptanceState val_m val_w).m_proposals mq :=
    hinv.2.2.1 mq w hxqState
  rcases paper_da_exists_proposal_removal_step_of_final_not_remaining
      val_m val_w mq w hnot with
    ⟨t, ht, hmem, hremoved⟩
  exact ⟨t, hxq, ht, hmem, hremoved⟩

/--
The men who matter for Roth's Theorem 5 induction at woman `w`: their truthful
DA partner is not `w`, and they strictly prefer `w` to that truthful partner.
-/
def paper_da_truthful_rejected_proposer_for_woman
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mq r : M) (w : W) : Prop :=
  r ≠ mq ∧
    ∃ wr,
      (deferredAcceptance val_m val_w).m_match r = some wr ∧
        val_m r wr < val_m r w

/--
`mu` is woman `w`'s favorite member of Roth's rejected-proposer set. This is the
finite choice used in the backward induction proof of Theorem 5.
-/
def paper_da_top_truthful_rejected_proposer_for_woman
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mq mu : M) (w : W) : Prop :=
  paper_da_truthful_rejected_proposer_for_woman val_m val_w mq mu w ∧
    ∀ r,
      paper_da_truthful_rejected_proposer_for_woman val_m val_w mq r w →
        val_w w r ≤ val_w w mu

/--
If there is at least one rejected proposer for `w`, finite choice provides a
woman-favorite one.
-/
theorem paper_da_exists_top_truthful_rejected_proposer_for_woman
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mq : M) (w : W)
    (hnonempty :
      ∃ r, paper_da_truthful_rejected_proposer_for_woman val_m val_w mq r w) :
    ∃ mu, paper_da_top_truthful_rejected_proposer_for_woman
      val_m val_w mq mu w := by
  classical
  let rejected : Finset M :=
    (Finset.univ : Finset M).filter fun r =>
      paper_da_truthful_rejected_proposer_for_woman val_m val_w mq r w
  have hrejected_nonempty : rejected.Nonempty := by
    rcases hnonempty with ⟨r, hr⟩
    exact ⟨r, by simp [rejected, hr]⟩
  obtain ⟨mu, hmu_mem, hmu_max⟩ :=
    Finset.exists_max_image rejected (fun r => val_w w r) hrejected_nonempty
  refine ⟨mu, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hmu_mem).2
  · intro r hr
    exact hmu_max r (by simp [rejected, hr])

/--
If a man proposed to `w` in the truthful DA run but ultimately matched to a
different `wr`, then under strict truthful preferences he strictly prefers `w`
to `wr`.
-/
theorem paper_da_truthful_proposal_to_nonfinal_partner_is_strictly_preferred
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (r : M) (w wr : W)
    (hstrictM : ∀ m w w', val_m m w = val_m m w' → w = w')
    (hposM : ∀ m w, 0 < val_m m w)
    (hxr : (deferredAcceptance val_m val_w).m_match r = some wr)
    (hwr_ne_w : wr ≠ w)
    (hproposed : w ∉ (deferredAcceptanceState val_m val_w).m_proposals r) :
    val_m r wr < val_m r w := by
  rcases paper_da_exists_proposal_removal_step_of_final_not_remaining
      val_m val_w r w hproposed with
    ⟨t, ht, hmem, hremoved⟩
  have hproposal :=
    proposal_removed_at_daStateAfterSteps_succ val_m val_w t hmem hremoved
  have hwr_mem_at_t :
      wr ∈ (daStateAfterSteps val_m val_w t).m_proposals r := by
    by_contra hnotWr
    have hnotMatchAtT :
        (daStateAfterSteps val_m val_w t).m_match r ≠ some wr := by
      rw [hproposal.1.1]
      simp
    have hnotFinal :
        (deferredAcceptanceState val_m val_w).m_match r ≠ some wr :=
      m_match_ne_deferredAcceptanceState_of_not_mem_after_steps
        val_m val_w (Nat.le_of_lt ht) hnotWr hnotMatchAtT
    have hxrState :
        (deferredAcceptanceState val_m val_w).m_match r = some wr := by
      simpa [deferredAcceptance] using hxr
    exact hnotFinal hxrState
  have hle : val_m r wr ≤ val_m r w :=
    hproposal.2.2.2 wr hwr_mem_at_t (le_of_lt (hposM r wr))
  have hneVal : val_m r wr ≠ val_m r w := by
    intro heq
    exact hwr_ne_w (hstrictM r wr w heq)
  exact lt_of_le_of_ne hle hneVal

/--
If woman `w = x(mq)` has no rejected proposers in Roth's sense, then no other
man proposed to `w` in the truthful DA run.
-/
theorem paper_da_no_rejected_proposer_implies_unique_truthful_proposer
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mq : M) (w : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hxq : (deferredAcceptance val_m val_w).m_match mq = some w)
    (hnoRejected :
      ¬ ∃ r, paper_da_truthful_rejected_proposer_for_woman
        val_m val_w mq r w) :
    ∀ r, r ≠ mq →
      w ∈ (deferredAcceptanceState val_m val_w).m_proposals r := by
  rcases hdomain with ⟨hstrictM, _hstrictW, hposM, hposW⟩
  have hcompleteX :
      (∀ r, ∃ wr, (deferredAcceptance val_m val_w).m_match r = some wr) ∧
        (∀ wr, ∃ r, (deferredAcceptance val_m val_w).w_match wr = some r) := by
    exact deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
      val_m val_w hcard ⟨hposM, hposW⟩
  intro r hr_ne
  by_contra hproposed
  rcases hcompleteX.1 r with ⟨wr, hxr⟩
  have hwr_ne_w : wr ≠ w := by
    intro hwr
    subst wr
    have hxw_mq :
        (deferredAcceptance val_m val_w).w_match w = some mq :=
      (deferredAcceptance val_m val_w).consistent_m mq w |>.1 hxq
    have hxw_r :
        (deferredAcceptance val_m val_w).w_match w = some r :=
      (deferredAcceptance val_m val_w).consistent_m r w |>.1 hxr
    have : some r = some mq := hxw_r.symm.trans hxw_mq
    exact hr_ne (Option.some.inj this)
  have hpref :=
    paper_da_truthful_proposal_to_nonfinal_partner_is_strictly_preferred
      val_m val_w r w wr hstrictM hposM hxr hwr_ne_w hproposed
  exact hnoRejected ⟨r, hr_ne, wr, hxr, hpref⟩

/--
Theorem 5 base case in Roth's rejected-proposer language: if `x(mq)` has no
rejected proposers, then `mq` is fixed in any no-worse strict simple-report run.
-/
theorem paper_da_no_rejected_proposer_fixed_under_simple_report_no_worse
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m mq : M) (simple_report_m : W → ℝ) (w ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hdomainReport :
      paper_strict_marriage_domain
        (Function.update val_m m simple_report_m) val_w)
    (hxq : (deferredAcceptance val_m val_w).m_match mq = some w)
    (hnoRejected :
      ¬ ∃ r, paper_da_truthful_rejected_proposer_for_woman
        val_m val_w mq r w)
    (hyM :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar))
    (hallWeak :
      ∀ r,
        paper_man_weakly_prefers_outcome val_m r
          (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
          (deferredAcceptance val_m val_w)) :
    (deferredAcceptance
      (Function.update val_m m simple_report_m) val_w).m_match mq = some w := by
  have honly :=
    paper_da_no_rejected_proposer_implies_unique_truthful_proposer
      val_m val_w mq w hcard hdomain hxq hnoRejected
  exact paper_da_unique_truthful_proposer_fixed_under_simple_report_no_worse
    val_m val_w m mq simple_report_m w ystar hcard hdomain hdomainReport
    hxq honly hyM hfirst hallWeak

/--
Theorem 5 backward-induction step. If `mu` is a woman `w`'s favorite truthful-run
proposer among the men who strictly prefer `w` to their truthful DA partners,
and `mu` is already fixed in the altered run, then `w`'s truthful DA partner
`mq` is fixed as well.
-/
theorem paper_da_top_rejected_proposer_fixed_implies_truthful_partner_fixed
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m mq mu : M) (simple_report_m : W → ℝ) (w wmu ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hdomainReport :
      paper_strict_marriage_domain
        (Function.update val_m m simple_report_m) val_w)
    (hmu_ne_m : mu ≠ m)
    (hxq : (deferredAcceptance val_m val_w).m_match mq = some w)
    (hxmu : (deferredAcceptance val_m val_w).m_match mu = some wmu)
    (hmuPref : val_m mu wmu < val_m mu w)
    (hmuTop :
      ∀ r wr,
        r ≠ mq →
          (deferredAcceptance val_m val_w).m_match r = some wr →
            val_m r wr < val_m r w →
              val_w w r ≤ val_w w mu)
    (hyM :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar))
    (hallWeak :
      ∀ r,
        paper_man_weakly_prefers_outcome val_m r
          (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
          (deferredAcceptance val_m val_w))
    (hmuFixed :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match mu =
          some wmu) :
    (deferredAcceptance
      (Function.update val_m m simple_report_m) val_w).m_match mq = some w := by
  let reported := Function.update val_m m simple_report_m
  let x := deferredAcceptance val_m val_w
  let y := deferredAcceptance reported val_w
  rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hcompleteX :
      (∀ r, ∃ wr, x.m_match r = some wr) ∧
        (∀ wr, ∃ r, x.w_match wr = some r) := by
    simpa [x] using
      deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
        val_m val_w hcard ⟨hposM, hposW⟩
  have hcompleteY :
      (∀ r, ∃ wr, y.m_match r = some wr) ∧
        (∀ wr, ∃ r, y.w_match wr = some r) := by
    simpa [y, reported] using
      deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
        reported val_w hcard ⟨hdomainReport.2.2.1, hdomainReport.2.2.2⟩
  have hmu_w_ne : wmu ≠ w := by
    intro h
    subst wmu
    exact (lt_irrefl (val_m mu w)) hmuPref
  rcases hcompleteY.2 w with ⟨a, hyaw⟩
  have hya : y.m_match a = some w := y.consistent_m a w |>.2 hyaw
  by_cases ha_mq : a = mq
  · subst a
    simpa [y] using hya
  · have hmuProposedY :
        w ∉ (deferredAcceptanceState reported val_w).m_proposals mu := by
      have hbetterReported :
          paper_matching_valM reported mu (y.m_match mu) < reported mu w := by
        simpa [paper_matching_valM, y, reported, Function.update, hmu_ne_m,
          hmuFixed] using hmuPref
      exact paper_da_final_better_partner_was_proposed reported val_w mu w
        hbetterReported
    have hmuNotMatchedW :
        (deferredAcceptanceState reported val_w).m_match mu ≠ some w := by
      intro hmatch
      have hmatchY : y.m_match mu = some w := by
        simpa [y, deferredAcceptance, reported] using hmatch
      have : some wmu = some w := hmuFixed.symm.trans hmatchY
      exact hmu_w_ne (Option.some.inj this)
    have hinvY :
        DAInvariants reported val_w (deferredAcceptanceState reported val_w) :=
      deferredAcceptanceState_satisfies_invariants_closed reported val_w
    have hmuLeA : val_w w mu ≤ val_w w a := by
      rcases hinvY.2.2.2.1 w mu hmuProposedY hmuNotMatchedW with
        hneg | ⟨cur, hcur, hle⟩
      · have hpos := hposW w mu
        linarith
      · have hcur_eq : cur = a := by
          have hcurY : y.w_match w = some cur := by
            simpa [y, deferredAcceptance, reported] using hcur
          exact Option.some.inj (hcurY.symm.trans hyaw)
        subst cur
        exact hle
    have ha_ne_mu : a ≠ mu := by
      intro ha
      subst a
      have hmatchY : y.m_match mu = some w := hya
      have : some wmu = some w := hmuFixed.symm.trans hmatchY
      exact hmu_w_ne (Option.some.inj this)
    rcases hcompleteX.1 a with ⟨wa, hxa⟩
    have haPrefW : val_m a wa < val_m a w := by
      have hweakA := hallWeak a
      have hle : val_m a wa ≤ val_m a w := by
        simpa [paper_man_weakly_prefers_outcome, paper_matching_valM, x, y,
          reported, hxa, hya] using hweakA
      have hwa_ne_w : wa ≠ w := by
        intro hwa
        subst wa
        have hxw_mq : x.w_match w = some mq := x.consistent_m mq w |>.1 (by
          simpa [x] using hxq)
        have hxw_a : x.w_match w = some a := x.consistent_m a w |>.1 hxa
        have : some a = some mq := hxw_a.symm.trans hxw_mq
        exact ha_mq (Option.some.inj this)
      have hneVal : val_m a wa ≠ val_m a w := by
        intro heq
        exact hwa_ne_w (hstrictM a wa w heq)
      exact lt_of_le_of_ne hle hneVal
    have haLeMu : val_w w a ≤ val_w w mu :=
      hmuTop a wa ha_mq (by simpa [x] using hxa) haPrefW
    have hEq : val_w w a = val_w w mu := le_antisymm haLeMu hmuLeA
    exact False.elim (ha_ne_mu (hstrictW w a mu hEq))

/--
Generic DA crossing bridge: if `mk` has already spent the proposal to `w` and
is active at a later truthful-run prefix, then before that later prefix woman
`w` crossed to a holder she strictly prefers to `mk`.
-/
theorem paper_da_spent_proposal_before_active_step_yields_earlier_crossing
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mk : M) (w : W) (t tk : ℕ)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (htk : tk < t)
    (hremoved :
      w ∉ (daStateAfterSteps val_m val_w (tk + 1)).m_proposals mk)
    (hact : IsActiveMan val_m (daStateAfterSteps val_m val_w t) mk) :
    ∃ tc, tc < t ∧
      ¬ val_w w mk <
        valW val_w w ((daStateAfterSteps val_m val_w tc).w_match w) ∧
      val_w w mk <
        valW val_w w ((daStateAfterSteps val_m val_w (tc + 1)).w_match w) := by
  rcases hdomain with ⟨_hstrictM, hstrictW, _hposM, hposW⟩
  have hnotAtT :
      w ∉ (daStateAfterSteps val_m val_w t).m_proposals mk :=
    not_mem_daStateAfterSteps_of_not_mem_of_le val_m val_w
      (Nat.succ_le_of_lt htk) hremoved
  have hnotMatchedAtT :
      (daStateAfterSteps val_m val_w t).m_match mk ≠ some w := by
    rw [hact.1]
    simp
  have hinv :
      DAInvariants val_m val_w (daStateAfterSteps val_m val_w t) :=
    daStateAfterSteps_satisfies_invariants val_m val_w t
  have hthresholdT :
      val_w w mk < valW val_w w ((daStateAfterSteps val_m val_w t).w_match w) := by
    rcases hinv.2.2.2.1 w mk hnotAtT hnotMatchedAtT with
      hneg | ⟨cur, hwcur, hle⟩
    · have hpos := hposW w mk
      linarith
    · have hcur_ne : cur ≠ mk := by
        intro hcur_eq
        subst cur
        have hmatch : (daStateAfterSteps val_m val_w t).m_match mk = some w :=
          (daStateAfterSteps val_m val_w t).consistent mk w |>.2 hwcur
        exact hnotMatchedAtT hmatch
      have hneVal : val_w w mk ≠ val_w w cur := by
        intro heq
        exact hcur_ne ((hstrictW w mk cur heq).symm)
      have hstrict : val_w w mk < val_w w cur :=
        lt_of_le_of_ne hle hneVal
      simpa [valW, hwcur] using hstrict
  have hstart :
      ¬ val_w w mk <
        valW val_w w ((daStateAfterSteps val_m val_w 0).w_match w) := by
    have hpos := hposW w mk
    simp [initialDAState, valW]
    linarith
  rcases exists_woman_threshold_crossing_step_before val_m val_w hstart hthresholdT with
    ⟨tc, htc, hbefore, hafter⟩
  exact ⟨tc, htc, hbefore, hafter⟩

/--
DA timing certificate for Roth's Theorem 5 induction: a woman-favorite truthful
rejected proposer makes his own truthful final match strictly later than the man
who ultimately matches with that woman.
-/
def DaTopRejectedProposerLaterMatchTimeCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  ∀ (mq mu : M) (w : W) (tq : ℕ),
    paper_da_truthful_match_step val_m val_w mq w tq →
      paper_da_top_truthful_rejected_proposer_for_woman val_m val_w mq mu w →
        ∃ wmu tmu,
          paper_da_truthful_match_step val_m val_w mu wmu tmu ∧ tq < tmu

/-- Roth's top-rejected-proposer timing fact for the truthful DA run. -/
theorem paper_da_top_rejected_proposer_later_match_time
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    DaTopRejectedProposerLaterMatchTimeCertificate val_m val_w := by
  classical
  intro mq mu w tq hmatchq htop
  rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hdomainFull : paper_strict_marriage_domain val_m val_w :=
    ⟨hstrictM, hstrictW, hposM, hposW⟩
  rcases htop.1 with ⟨hmu_ne_mq, wmu, hxmu, hmuPref⟩
  rcases paper_da_exists_truthful_match_step val_m val_w mu wmu hxmu with
    ⟨tmu, hmatchMu⟩
  refine ⟨wmu, tmu, hmatchMu, ?_⟩
  by_contra hnotLt
  have hle_tmu_tq : tmu ≤ tq := le_of_not_gt hnotLt
  have hnotFinalW :
      w ∉ (deferredAcceptanceState val_m val_w).m_proposals mu := by
    have hbetter :
        paper_matching_valM val_m mu
            ((deferredAcceptance val_m val_w).m_match mu) < val_m mu w := by
      simpa [paper_matching_valM, hxmu] using hmuPref
    exact paper_da_final_better_partner_was_proposed val_m val_w mu w hbetter
  rcases paper_da_exists_proposal_removal_step_of_final_not_remaining
      val_m val_w mu w hnotFinalW with
    ⟨tw, htw, htw_mem, htw_removed⟩
  have hproposalMu :=
    proposal_removed_at_daStateAfterSteps_succ val_m val_w tmu
      hmatchMu.2.2.1 hmatchMu.2.2.2
  have htw_lt_tmu : tw < tmu := by
    by_contra hnot
    have htmu_le_tw : tmu ≤ tw := le_of_not_gt hnot
    have hw_mem_tmu :
        w ∈ (daStateAfterSteps val_m val_w tmu).m_proposals mu :=
      m_proposals_daStateAfterSteps_subset_of_le val_m val_w htmu_le_tw mu
        htw_mem
    have hle := hproposalMu.2.2.2 w hw_mem_tmu (le_of_lt (hposM mu w))
    linarith
  rcases
      paper_da_spent_proposal_before_active_step_yields_earlier_crossing
        val_m val_w mu w tmu tw hdomainFull htw_lt_tmu htw_removed
        hproposalMu.1 with
    ⟨tc, htc_lt_tmu, hbefore, hafter⟩
  rcases
      woman_threshold_crossed_at_daStateAfterSteps_succ
        val_m val_w tc w mu (le_of_not_gt hbefore) hafter with
    ⟨a, hactA, _hbestA, hmatchAAfter, hwprefA⟩
  have htc_lt_tq : tc < tq := lt_of_lt_of_le htc_lt_tmu hle_tmu_tq
  have ha_ne_mq : a ≠ mq := by
    intro ha
    subst a
    have hnotAfter :
        w ∉ (daStateAfterSteps val_m val_w (tc + 1)).m_proposals mq := by
      have hinvAfter :
          DAInvariants val_m val_w
            (daStateAfterSteps val_m val_w (tc + 1)) :=
        daStateAfterSteps_satisfies_invariants val_m val_w (tc + 1)
      have hmAfter :
          (daStateAfterSteps val_m val_w (tc + 1)).m_match mq = some w :=
        (daStateAfterSteps val_m val_w (tc + 1)).consistent mq w |>.2
          hmatchAAfter
      exact hinvAfter.2.2.1 mq w hmAfter
    have hnotAtTq :
        w ∉ (daStateAfterSteps val_m val_w tq).m_proposals mq :=
      not_mem_daStateAfterSteps_of_not_mem_of_le val_m val_w
        (Nat.succ_le_of_lt htc_lt_tq) hnotAfter
    exact hnotAtTq hmatchq.2.2.1
  have hcompleteX :
      (∀ r, ∃ wr, (deferredAcceptance val_m val_w).m_match r = some wr) ∧
        (∀ wr, ∃ r, (deferredAcceptance val_m val_w).w_match wr = some r) := by
    exact deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
      val_m val_w hcard ⟨hposM, hposW⟩
  rcases hcompleteX.1 a with ⟨wa, hxa⟩
  have hwa_ne_w : wa ≠ w := by
    intro hwa
    subst wa
    have hxw_mq :
        (deferredAcceptance val_m val_w).w_match w = some mq :=
      (deferredAcceptance val_m val_w).consistent_m mq w |>.1 hmatchq.1
    have hxw_a :
        (deferredAcceptance val_m val_w).w_match w = some a :=
      (deferredAcceptance val_m val_w).consistent_m a w |>.1 hxa
    have : some a = some mq := hxw_a.symm.trans hxw_mq
    exact ha_ne_mq (Option.some.inj this)
  have hproposedAState :
      w ∉ (daStateAfterSteps val_m val_w (tc + 1)).m_proposals a := by
    have hinvAfter :
        DAInvariants val_m val_w
          (daStateAfterSteps val_m val_w (tc + 1)) :=
      daStateAfterSteps_satisfies_invariants val_m val_w (tc + 1)
    have hmAfter :
        (daStateAfterSteps val_m val_w (tc + 1)).m_match a = some w :=
      (daStateAfterSteps val_m val_w (tc + 1)).consistent a w |>.2 hmatchAAfter
    exact hinvAfter.2.2.1 a w hmAfter
  have htc_succ_le_N : tc + 1 ≤ Fintype.card M * Fintype.card W :=
    Nat.succ_le_of_lt (lt_trans htc_lt_tmu hmatchMu.2.1)
  have hproposedAFinal :
      w ∉ (deferredAcceptanceState val_m val_w).m_proposals a :=
    not_mem_deferredAcceptanceState_of_not_mem_after_steps
      val_m val_w (tc + 1) htc_succ_le_N hproposedAState
  have haPrefW :
      val_m a wa < val_m a w :=
    paper_da_truthful_proposal_to_nonfinal_partner_is_strictly_preferred
      val_m val_w a w wa hstrictM hposM hxa hwa_ne_w hproposedAFinal
  have haLeMu : val_w w a ≤ val_w w mu :=
    htop.2 a ⟨ha_ne_mq, wa, hxa, haPrefW⟩
  linarith

/--
Given the top-rejected-proposer timing certificate, Roth's no-profitable strict
simple-report step follows from Lemma 2 and the latest-bad-match-time argument.
This is the men-side core of Theorem 5 on the equal-size strict source domain.
-/
theorem paper_da_no_profitable_strict_simple_report_of_top_rejected_later_certificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (simple_report_m : W → ℝ) (ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hdomainReport :
      paper_strict_marriage_domain
        (Function.update val_m m simple_report_m) val_w)
    (hyM :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar))
    (htiming : DaTopRejectedProposerLaterMatchTimeCertificate val_m val_w) :
    paper_matching_valM val_m m
        ((deferredAcceptance
          (Function.update val_m m simple_report_m) val_w).m_match m) ≤
      paper_matching_valM val_m m
        ((deferredAcceptance val_m val_w).m_match m) := by
  classical
  let reported := Function.update val_m m simple_report_m
  let x := deferredAcceptance val_m val_w
  let y := deferredAcceptance reported val_w
  let N := Fintype.card M * Fintype.card W
  rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hdomainFull : paper_strict_marriage_domain val_m val_w :=
    ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hcompleteX :
      (∀ r, ∃ wr, x.m_match r = some wr) ∧
        (∀ wr, ∃ r, x.w_match wr = some r) := by
    simpa [x] using
      deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
        val_m val_w hcard ⟨hposM, hposW⟩
  by_contra hnot
  have hprofitable :
      paper_matching_valM val_m m (x.m_match m) <
        paper_matching_valM val_m m (y.m_match m) :=
    lt_of_not_ge hnot
  have hweakM :
      paper_man_weakly_prefers_outcome val_m m y x := by
    simpa [paper_man_weakly_prefers_outcome, x, y] using le_of_lt hprofitable
  have hallWeak :
      ∀ r, paper_man_weakly_prefers_outcome val_m r y x := by
    intro r
    exact paper_da_strict_simple_report_no_men_harmed_on_strict_domain
      val_m val_w m simple_report_m ystar hcard hdomainFull hdomainReport
      (by simpa [y, reported] using hyM) (by simpa [x, y, reported] using hweakM)
      hfirst r
  rcases hcompleteX.1 m with ⟨wm, hxm⟩
  have hy_ne_xm : y.m_match m ≠ some wm := by
    intro hym
    have hlt : val_m m wm < val_m m wm := by
      simpa [paper_matching_valM, x, y, hxm, hym] using hprofitable
    exact (lt_irrefl (val_m m wm)) hlt
  rcases paper_da_exists_truthful_match_step val_m val_w m wm
      (by simpa [x] using hxm) with
    ⟨tm, htm⟩
  let BadAt : ℕ → Prop := fun t =>
    ∃ q wq,
      paper_da_truthful_match_step val_m val_w q wq t ∧
        y.m_match q ≠ some wq
  have hBadExists : ∃ t, t ∈ (Finset.range N).filter BadAt := by
    refine ⟨tm, ?_⟩
    have htm_lt : tm < N := htm.2.1
    have hbadTm : BadAt tm := ⟨m, wm, htm, by simpa [y] using hy_ne_xm⟩
    simp [BadAt, N, htm_lt, hbadTm]
  have hBadNonempty : ((Finset.range N).filter BadAt).Nonempty := by
    rcases hBadExists with ⟨t, ht⟩
    exact ⟨t, ht⟩
  obtain ⟨t0, ht0mem, ht0max⟩ :=
    Finset.exists_max_image ((Finset.range N).filter BadAt) (fun t => t)
      hBadNonempty
  have ht0_range : t0 ∈ Finset.range N := (Finset.mem_filter.mp ht0mem).1
  have ht0Bad : BadAt t0 := (Finset.mem_filter.mp ht0mem).2
  rcases ht0Bad with ⟨mq, wq, hmatchq, hbadq⟩
  by_cases hnoRejected :
      ¬ ∃ r, paper_da_truthful_rejected_proposer_for_woman val_m val_w mq r wq
  · have hfixed :=
      paper_da_no_rejected_proposer_fixed_under_simple_report_no_worse
        val_m val_w m mq simple_report_m wq ystar hcard hdomainFull
        hdomainReport hmatchq.1 hnoRejected (by simpa [y, reported] using hyM)
        hfirst (by simpa [x, y, reported] using hallWeak)
    exact hbadq (by simpa [y, reported] using hfixed)
  · have hsomeRejected :
        ∃ r, paper_da_truthful_rejected_proposer_for_woman val_m val_w mq r wq :=
      not_not.mp hnoRejected
    rcases paper_da_exists_top_truthful_rejected_proposer_for_woman
        val_m val_w mq wq hsomeRejected with
      ⟨mu, htopMu⟩
    rcases htiming mq mu wq t0 hmatchq htopMu with
      ⟨wmu, tmu, hmatchMu, ht_lt_mu⟩
    have hmu_ne_m : mu ≠ m := by
      intro hmu_eq
      subst mu
      have hbadMu : BadAt tmu := by
        have hy_ne_wmu : y.m_match m ≠ some wmu := by
          intro hymu
          have hlt : val_m m wmu < val_m m wmu := by
            simpa [paper_matching_valM, x, y, hmatchMu.1, hymu] using hprofitable
          exact (lt_irrefl (val_m m wmu)) hlt
        exact ⟨m, wmu, hmatchMu, hy_ne_wmu⟩
      have htmu_mem : tmu ∈ (Finset.range N).filter BadAt := by
        simp [BadAt, N, hmatchMu.2.1, hbadMu]
      have hmax := ht0max tmu htmu_mem
      exact (not_lt_of_ge hmax) ht_lt_mu
    have hmuFixed : y.m_match mu = some wmu := by
      by_contra hnotFixed
      have hbadMu : BadAt tmu := ⟨mu, wmu, hmatchMu, hnotFixed⟩
      have htmu_mem : tmu ∈ (Finset.range N).filter BadAt := by
        simp [BadAt, N, hmatchMu.2.1, hbadMu]
      have hmax := ht0max tmu htmu_mem
      exact False.elim ((not_lt_of_ge hmax) ht_lt_mu)
    rcases htopMu.1 with ⟨_hmu_ne_mq, wmu', hxmu', hmuPref'⟩
    have hmu_w_eq : wmu' = wmu := by
      have : some wmu' = some wmu := hxmu'.symm.trans hmatchMu.1
      exact Option.some.inj this
    subst wmu'
    have hfixedQ :=
      paper_da_top_rejected_proposer_fixed_implies_truthful_partner_fixed
        val_m val_w m mq mu simple_report_m wq wmu ystar hcard hdomainFull
        hdomainReport hmu_ne_m hmatchq.1 hmatchMu.1 hmuPref'
        (by
          intro r wr hr hxr hpref
          exact htopMu.2 r ⟨hr, wr, hxr, hpref⟩)
        (by simpa [y, reported] using hyM) hfirst
        (by simpa [x, y, reported] using hallWeak)
        (by simpa [y] using hmuFixed)
    exact hbadq (by simpa [y, reported] using hfixedQ)

/-- Source-domain timing certificate for the men-side Theorem 5 route. -/
def DaTopRejectedProposerLaterMatchTimeForMenCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    Prop :=
  ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    paper_strict_marriage_domain val_m val_w →
      DaTopRejectedProposerLaterMatchTimeCertificate val_m val_w

/--
Men-side Theorem 5 source route on equal-size strict marriage domains, reduced
to the single top-rejected-proposer timing certificate.
-/
theorem paper_da_truthful_for_men_on_strict_domain_of_card_eq_of_top_rejected_later_certificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (htimingCert : @DaTopRejectedProposerLaterMatchTimeForMenCertificate
      M W _ _ _ _) :
    ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
      Fintype.card M = Fintype.card W →
        paper_strict_marriage_domain val_m val_w →
          ∀ (m : M) (report_m : W → ℝ),
            paper_matching_valM val_m m
                ((deferredAcceptance
                  (Function.update val_m m report_m) val_w).m_match m) ≤
              paper_matching_valM val_m m
                ((deferredAcceptance val_m val_w).m_match m) := by
  intro val_m val_w hcard hdomain m report_m
  let x := deferredAcceptance val_m val_w
  let y := deferredAcceptance (Function.update val_m m report_m) val_w
  cases hy : y.m_match m with
  | none =>
      have hxStable : paper_is_stable val_m val_w x := by
        simpa [x] using paper_da_is_stable val_m val_w
      have hxIR := hxStable.1 m
      simpa [paper_matching_valM, x, y, hy] using hxIR
  | some wstar =>
      let simple_report_m := paper_strict_top_report wstar
      have hdomainSimple :
          paper_strict_marriage_domain
            (Function.update val_m m simple_report_m) val_w := by
        exact paper_strict_marriage_domain_update_strict_top_report
          val_m val_w m wstar hdomain
      have hfirst :
          ∀ w, w ≠ wstar → simple_report_m w < simple_report_m wstar := by
        simpa [simple_report_m] using
          paper_strict_top_report_top (W := W) wstar
      have hfirstProp :
          paper_man_report_strictly_ranks_partner_first
            simple_report_m (some wstar) := by
        simpa [paper_man_report_strictly_ranks_partner_first] using hfirst
      have hsame :
          (deferredAcceptance
              (Function.update val_m m simple_report_m) val_w).m_match m =
            y.m_match m := by
        exact paper_roth82_lemma1_strict_simple_misrepresentation_same_partner
          val_m val_w m report_m simple_report_m wstar hdomainSimple
          (by simpa [y] using hy) hfirst
      have hsimple :=
        paper_da_no_profitable_strict_simple_report_of_top_rejected_later_certificate
          val_m val_w m simple_report_m wstar hcard hdomain hdomainSimple
          (by simpa [y, hsame] using hy) hfirstProp
          (htimingCert val_m val_w hdomain)
      rw [hsame] at hsimple
      simpa [x, y, hy] using hsimple

/--
Paper-facing men-side Theorem 5 route with the DA timing certificate isolated.
-/
theorem paper_roth82_theorem5_men_truthful_on_strict_domain_of_card_eq_of_top_rejected_later_certificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (htimingCert : @DaTopRejectedProposerLaterMatchTimeForMenCertificate
      M W _ _ _ _) :
    ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
      Fintype.card M = Fintype.card W →
        paper_strict_marriage_domain val_m val_w →
          ∀ (m : M) (report_m : W → ℝ),
            paper_matching_valM val_m m
                ((deferredAcceptance
                  (Function.update val_m m report_m) val_w).m_match m) ≤
              paper_matching_valM val_m m
                ((deferredAcceptance val_m val_w).m_match m) := by
  exact
    paper_da_truthful_for_men_on_strict_domain_of_card_eq_of_top_rejected_later_certificate
      htimingCert

/-- No strict simple report is profitable for men on Roth's equal-size strict domain. -/
theorem paper_da_no_profitable_strict_simple_report_on_strict_domain_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (simple_report_m : W → ℝ) (ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hdomainReport :
      paper_strict_marriage_domain
        (Function.update val_m m simple_report_m) val_w)
    (hyM :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar)) :
    paper_matching_valM val_m m
        ((deferredAcceptance
          (Function.update val_m m simple_report_m) val_w).m_match m) ≤
      paper_matching_valM val_m m
        ((deferredAcceptance val_m val_w).m_match m) := by
  exact paper_da_no_profitable_strict_simple_report_of_top_rejected_later_certificate
    val_m val_w m simple_report_m ystar hcard hdomain hdomainReport hyM
    hfirst (paper_da_top_rejected_proposer_later_match_time val_m val_w hcard hdomain)

/--
Closed men-side Theorem 5 source route on equal-size strict marriage domains.
-/
theorem paper_da_truthful_for_men_on_strict_domain_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
      Fintype.card M = Fintype.card W →
        paper_strict_marriage_domain val_m val_w →
          ∀ (m : M) (report_m : W → ℝ),
            paper_matching_valM val_m m
                ((deferredAcceptance
                  (Function.update val_m m report_m) val_w).m_match m) ≤
              paper_matching_valM val_m m
                ((deferredAcceptance val_m val_w).m_match m) := by
  intro val_m val_w hcard hdomain m report_m
  let x := deferredAcceptance val_m val_w
  let y := deferredAcceptance (Function.update val_m m report_m) val_w
  cases hy : y.m_match m with
  | none =>
      have hxStable : paper_is_stable val_m val_w x := by
        simpa [x] using paper_da_is_stable val_m val_w
      have hxIR := hxStable.1 m
      simpa [paper_matching_valM, x, y, hy] using hxIR
  | some wstar =>
      let simple_report_m := paper_strict_top_report wstar
      have hdomainSimple :
          paper_strict_marriage_domain
            (Function.update val_m m simple_report_m) val_w := by
        exact paper_strict_marriage_domain_update_strict_top_report
          val_m val_w m wstar hdomain
      have hfirst :
          ∀ w, w ≠ wstar → simple_report_m w < simple_report_m wstar := by
        simpa [simple_report_m] using
          paper_strict_top_report_top (W := W) wstar
      have hfirstProp :
          paper_man_report_strictly_ranks_partner_first
            simple_report_m (some wstar) := by
        simpa [paper_man_report_strictly_ranks_partner_first] using hfirst
      have hsame :
          (deferredAcceptance
              (Function.update val_m m simple_report_m) val_w).m_match m =
            y.m_match m := by
        exact paper_roth82_lemma1_strict_simple_misrepresentation_same_partner
          val_m val_w m report_m simple_report_m wstar hdomainSimple
          (by simpa [y] using hy) hfirst
      have hsimple :=
        paper_da_no_profitable_strict_simple_report_on_strict_domain_of_card_eq
          val_m val_w m simple_report_m wstar hcard hdomain hdomainSimple
          (by simpa [y, hsame] using hy) hfirstProp
      rw [hsame] at hsimple
      simpa [x, y, hy] using hsimple

/-- Paper-facing men-side Theorem 5 on Roth's equal-size strict domain. -/
theorem paper_roth82_theorem5_men_truthful_on_strict_domain_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
      Fintype.card M = Fintype.card W →
        paper_strict_marriage_domain val_m val_w →
          ∀ (m : M) (report_m : W → ℝ),
            paper_matching_valM val_m m
                ((deferredAcceptance
                  (Function.update val_m m report_m) val_w).m_match m) ≤
              paper_matching_valM val_m m
                ((deferredAcceptance val_m val_w).m_match m) := by
  exact paper_da_truthful_for_men_on_strict_domain_of_card_eq

/-- Closed women-side Theorem 5 source route by role reversal. -/
theorem paper_da_truthful_for_women_on_strict_domain_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
      Fintype.card M = Fintype.card W →
        paper_strict_marriage_domain val_m val_w →
          ∀ (w : W) (report_w : M → ℝ),
            paper_matching_valW val_w w
                ((paper_women_deferredAcceptance val_m
                  (Function.update val_w w report_w)).w_match w) ≤
              paper_matching_valW val_w w
                ((paper_women_deferredAcceptance val_m val_w).w_match w) := by
  intro val_m val_w hcard hdomain w report_w
  rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hdomainSwap : paper_strict_marriage_domain val_w val_m :=
    ⟨hstrictW, hstrictM, hposW, hposM⟩
  have htruth := paper_da_truthful_for_men_on_strict_domain_of_card_eq
    (M := W) (W := M)
  have h := htruth val_w val_m hcard.symm hdomainSwap w report_w
  simpa [paper_women_deferredAcceptance, paper_matching_valM, paper_matching_valW]
    using h

/-- Paper-facing women-side Theorem 5 on Roth's equal-size strict domain. -/
theorem paper_roth82_theorem5_women_truthful_on_strict_domain_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
      Fintype.card M = Fintype.card W →
        paper_strict_marriage_domain val_m val_w →
          ∀ (w : W) (report_w : M → ℝ),
            paper_matching_valW val_w w
                ((paper_women_deferredAcceptance val_m
                  (Function.update val_w w report_w)).w_match w) ≤
              paper_matching_valW val_w w
                ((paper_women_deferredAcceptance val_m val_w).w_match w) := by
  exact paper_da_truthful_for_women_on_strict_domain_of_card_eq

/-- Theorem 5 on Roth's equal-size strict domain for each side's optimal procedure. -/
theorem paper_roth82_theorem5_optimal_side_truthful_on_strict_domain_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
      Fintype.card M = Fintype.card W →
        paper_strict_marriage_domain val_m val_w →
          (∀ (m : M) (report_m : W → ℝ),
            paper_matching_valM val_m m
                ((deferredAcceptance
                  (Function.update val_m m report_m) val_w).m_match m) ≤
              paper_matching_valM val_m m
                ((deferredAcceptance val_m val_w).m_match m)) ∧
          (∀ (w : W) (report_w : M → ℝ),
            paper_matching_valW val_w w
                ((paper_women_deferredAcceptance val_m
                  (Function.update val_w w report_w)).w_match w) ≤
              paper_matching_valW val_w w
                ((paper_women_deferredAcceptance val_m val_w).w_match w)) := by
  intro val_m val_w hcard hdomain
  exact ⟨paper_roth82_theorem5_men_truthful_on_strict_domain_of_card_eq
      val_m val_w hcard hdomain,
    paper_roth82_theorem5_women_truthful_on_strict_domain_of_card_eq
      val_m val_w hcard hdomain⟩

/--
When the DA outcome is complete and every man finds every woman acceptable, the
finite folded run has a final active proposal step.
-/
theorem paper_da_last_active_step_at_time_of_complete
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hmAcceptable : ∀ m w, 0 < val_m m w)
    (hcomplete : paper_is_complete_matching (deferredAcceptance val_m val_w)) :
    DaLastActiveStepAtTimeCertificate val_m val_w := by
  classical
  let N := Fintype.card M * Fintype.card W
  let P : ℕ → Prop :=
    fun n => ∃ m, IsActiveMan val_m (daStateAfterSteps val_m val_w n) m
  have hactive0 : P 0 := by
    let m0 : M := Classical.choice ‹Nonempty M›
    rcases hcomplete.1 m0 with ⟨w0, _hw0⟩
    refine ⟨m0, ?_, ⟨w0, ?_, ?_⟩⟩
    · simp [initialDAState]
    · simp [initialDAState]
    · exact le_of_lt (hmAcceptable m0 w0)
  have hnotN : ¬ P N := by
    have hterm := deferredAcceptanceState_terminated val_m val_w
    unfold DATerminationCertificate at hterm
    simpa [P, N, deferredAcceptanceState_eq_daStateAfterSteps] using hterm
  rcases exists_last_true_before_false (P := P) hactive0 hnotN with
    ⟨t, ht, hPt, hnotNext⟩
  exact ⟨t, by simpa [N] using ht, by simpa [P] using hPt,
    by simpa [P] using hnotNext⟩

/-- A timed final-unmatched-woman trace witness gives the invariant-rich certificate. -/
theorem paper_da_final_unmatched_woman_step_at_time_implies_certificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaFinalUnmatchedWomanStepAtTimeCertificate val_m val_w) :
    DaFinalUnmatchedWomanStepCertificate val_m val_w := by
  rcases hcert with ⟨t, m, w, _ht, hwNone, hfinal, hprops⟩
  refine ⟨daStateAfterSteps val_m val_w t, m, w, ?_, hwNone, hfinal, hprops⟩
  exact daStateAfterSteps_satisfies_invariants val_m val_w t

/--
If the last active DA step is followed by a complete final matching, then that
step must have matched a previously unmatched woman. This is the formalized
version of Roth's final-period trace observation used in Theorem 6.
-/
theorem paper_da_last_active_step_at_time_implies_final_unmatched_woman_step_at_time
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcomplete : paper_is_complete_matching (deferredAcceptance val_m val_w))
    (hcert : DaLastActiveStepAtTimeCertificate val_m val_w) :
    DaFinalUnmatchedWomanStepAtTimeCertificate val_m val_w := by
  classical
  rcases hcert with ⟨t, ht, hactive, hnoNext⟩
  let s := daStateAfterSteps val_m val_w t
  have hactiveS : ∃ m, IsActiveMan val_m s m := by
    simpa [s] using hactive
  let m := Classical.choose hactiveS
  have hact : IsActiveMan val_m s m := by
    simpa [m] using Classical.choose_spec hactiveS
  let w_exists := exists_best_woman val_m s m hact
  let w := Classical.choose w_exists
  have hwbest : BestRemainingWoman val_m s m w := by
    simpa [w, w_exists] using Classical.choose_spec w_exists
  have hnext :
      daStateAfterSteps val_m val_w (t + 1) = daStep val_m val_w s := by
    simpa [s] using daStateAfterSteps_succ val_m val_w t
  have hleNext : t + 1 ≤ Fintype.card M * Fintype.card W :=
    Nat.succ_le_of_lt ht
  have hfinalState :
      deferredAcceptanceState val_m val_w =
        daStateAfterSteps val_m val_w (t + 1) :=
    deferredAcceptanceState_eq_daStateAfterSteps_of_not_active
      val_m val_w (t + 1) hleNext hnoNext
  have hfinalStep :
      deferredAcceptanceState val_m val_w = daStep val_m val_w s := by
    rw [hfinalState, hnext]
  have hcompleteState :
      ∀ i, (deferredAcceptanceState val_m val_w).m_match i ≠ none := by
    intro i hnone
    rcases hcomplete.1 i with ⟨wi, hwi⟩
    have hsome :
        (deferredAcceptanceState val_m val_w).m_match i = some wi := by
      simpa [deferredAcceptance] using hwi
    rw [hnone] at hsome
    cases hsome
  have hcurNone : s.w_match w = none := by
    cases hcur : s.w_match w with
    | none =>
        rfl
    | some mcur =>
        have hmcurMatch : s.m_match mcur = some w := (s.consistent mcur w).2 hcur
        have hmcur_ne_m : mcur ≠ m := by
          intro hmcur
          subst mcur
          rw [hact.1] at hmcurMatch
          cases hmcurMatch
        by_cases hacc : val_w w mcur < val_w w m
        · have hmcurNone :
              (deferredAcceptanceState val_m val_w).m_match mcur = none := by
            rw [hfinalStep]
            simp [daStep, hactiveS, m, w, hcur, hacc, hmcur_ne_m]
          exact False.elim (hcompleteState mcur hmcurNone)
        · have hmNone :
              (deferredAcceptanceState val_m val_w).m_match m = none := by
            rw [hfinalStep]
            simp [daStep, hactiveS, m, w, hcur, hacc, hact.1]
          exact False.elim (hcompleteState m hmNone)
  have haccNone : 0 ≤ val_w w m := by
    by_contra hacc
    have hmNone :
        (deferredAcceptanceState val_m val_w).m_match m = none := by
      rw [hfinalStep]
      simp [daStep, hactiveS, m, w, hcurNone, hacc, hact.1]
    exact hcompleteState m hmNone
  refine ⟨t, m, w, ht, ?_, ?_, ?_⟩
  · simpa [s] using hcurNone
  · change (deferredAcceptanceState val_m val_w).m_match m = some w
    rw [hfinalStep]
    simp [daStep, hactiveS, m, w, hcurNone, haccNone]
  · intro m' hne
    rw [hfinalStep]
    simp [daStep, hactiveS, m, w, hcurNone, haccNone, removeProposal, hne, s]

/--
If a final matched woman was unmatched in the immediately preceding trace state,
then no other man had previously proposed to her, provided every woman finds
every man acceptable.
-/
theorem paper_da_final_unmatched_woman_step_implies_last_unique_proposal
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hwAcceptable : ∀ w m, 0 < val_w w m)
    (hcert : DaFinalUnmatchedWomanStepCertificate val_m val_w) :
    DaLastUniqueProposalForMenCertificate val_m val_w := by
  rcases hcert with ⟨s, m, w, hinv, hwNone, hfinal, hprops⟩
  refine ⟨m, w, hfinal, ?_⟩
  intro m' hne
  rw [hprops m' hne]
  exact unmatched_woman_mem_proposals_of_invariants
    val_m val_w s hwAcceptable hinv hwNone m'

/--
Roth Theorem 6 proof-route bridge: the final unique-proposal trace fact implies
that no complete outcome is strictly better for every man than men-proposing DA.
-/
theorem paper_da_last_unique_proposal_implies_weak_pareto_for_men
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaLastUniqueProposalForMenCertificate val_m val_w) :
    paper_weakly_pareto_optimal_for_men val_m (deferredAcceptance val_m val_w) := by
  rintro ⟨nu, hcomplete, hallStrict⟩
  rcases hcert with ⟨m, w, hda_m, honly⟩
  rcases hcomplete.2 w with ⟨m', hnu_w⟩
  have hnu_m' : nu.m_match m' = some w := (nu.consistent_m m' w).2 hnu_w
  by_cases hm' : m' = m
  · subst m'
    have hstrict := hallStrict m
    have hnu_m : nu.m_match m = some w := hnu_m'
    rw [paper_strictly_better_for_all_men] at hallStrict
    simpa [paper_matching_valM, hda_m, hnu_m] using hstrict
  · have hremaining := honly m' hm'
    have hstrict := hallStrict m'
    have hbetter :
        paper_matching_valM val_m m'
            ((deferredAcceptance val_m val_w).m_match m') <
          val_m m' w := by
      simpa [paper_matching_valM, hnu_m'] using hstrict
    exact (paper_da_final_better_partner_was_proposed val_m val_w m' w hbetter)
      hremaining

/--
Certificate for Roth's Theorem 6 conclusion for the men-proposing
deferred-acceptance outcome.
-/
def DaWeaklyParetoOptimalForMenCertificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  paper_weakly_pareto_optimal_for_men val_m (deferredAcceptance val_m val_w)

/--
Theorem 6 compatibility wrapper: no feasible outcome is strictly preferred by
every man to the men-proposing deferred-acceptance outcome once the weak-Pareto
certificate is supplied.
-/
theorem paper_roth82_theorem6_no_feasible_outcome_strictly_better_for_all_men
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaWeaklyParetoOptimalForMenCertificate val_m val_w) :
    paper_weakly_pareto_optimal_for_men val_m (deferredAcceptance val_m val_w) := by
  exact hcert

/--
Theorem 6 via Roth's final unique-proposal trace certificate.
-/
theorem paper_roth82_theorem6_of_last_unique_proposal_certificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcert : DaLastUniqueProposalForMenCertificate val_m val_w) :
    paper_weakly_pareto_optimal_for_men val_m (deferredAcceptance val_m val_w) := by
  exact paper_da_last_unique_proposal_implies_weak_pareto_for_men val_m val_w hcert

/--
Theorem 6 via the final-unmatched-woman trace certificate.
-/
theorem paper_roth82_theorem6_of_final_unmatched_woman_step_certificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hwAcceptable : ∀ w m, 0 < val_w w m)
    (hcert : DaFinalUnmatchedWomanStepCertificate val_m val_w) :
    paper_weakly_pareto_optimal_for_men val_m (deferredAcceptance val_m val_w) := by
  exact paper_roth82_theorem6_of_last_unique_proposal_certificate val_m val_w
    (paper_da_final_unmatched_woman_step_implies_last_unique_proposal
      val_m val_w hwAcceptable hcert)

/--
Theorem 6 via a timed final-unmatched-woman trace certificate.
-/
theorem paper_roth82_theorem6_of_final_unmatched_woman_step_at_time_certificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hwAcceptable : ∀ w m, 0 < val_w w m)
    (hcert : DaFinalUnmatchedWomanStepAtTimeCertificate val_m val_w) :
    paper_weakly_pareto_optimal_for_men val_m (deferredAcceptance val_m val_w) := by
  exact paper_roth82_theorem6_of_final_unmatched_woman_step_certificate
    val_m val_w hwAcceptable
    (paper_da_final_unmatched_woman_step_at_time_implies_certificate
      val_m val_w hcert)

/--
Theorem 6 via Roth's final active proposal step. Completeness of the DA outcome
rules out the final active step being a rejection or a displacement, so it gives
the final unmatched-woman trace certificate used above.
-/
theorem paper_roth82_theorem6_of_last_active_step_at_time_certificate
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hwAcceptable : ∀ w m, 0 < val_w w m)
    (hcomplete : paper_is_complete_matching (deferredAcceptance val_m val_w))
    (hcert : DaLastActiveStepAtTimeCertificate val_m val_w) :
    paper_weakly_pareto_optimal_for_men val_m (deferredAcceptance val_m val_w) := by
  exact paper_roth82_theorem6_of_final_unmatched_woman_step_at_time_certificate
    val_m val_w hwAcceptable
    (paper_da_last_active_step_at_time_implies_final_unmatched_woman_step_at_time
      val_m val_w hcomplete hcert)

/--
Theorem 6 on the complete marriage-problem DA outcome: all-pairs acceptability
and completeness produce the last active proposal step internally.
-/
theorem paper_roth82_theorem6_of_complete_da_outcome
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hmAcceptable : ∀ m w, 0 < val_m m w)
    (hwAcceptable : ∀ w m, 0 < val_w w m)
    (hcomplete : paper_is_complete_matching (deferredAcceptance val_m val_w)) :
    paper_weakly_pareto_optimal_for_men val_m (deferredAcceptance val_m val_w) := by
  exact paper_roth82_theorem6_of_last_active_step_at_time_certificate
    val_m val_w hwAcceptable hcomplete
    (paper_da_last_active_step_at_time_of_complete
      val_m val_w hmAcceptable hcomplete)

/--
The DA outcome is complete on Roth's equal-size strict marriage domain.
-/
theorem paper_da_complete_on_strict_marriage_domain_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    paper_is_complete_matching (deferredAcceptance val_m val_w) := by
  rcases hdomain with ⟨_hstrictM, _hstrictW, hposM, hposW⟩
  exact deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
    val_m val_w hcard ⟨hposM, hposW⟩

/--
Theorem 6 on Roth's source marriage domain: for nonempty equal-size sides with
complete strict preferences, no feasible outcome is strictly preferred by every
man to the men-proposing DA outcome.
-/
theorem paper_roth82_theorem6_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    paper_weakly_pareto_optimal_for_men val_m (deferredAcceptance val_m val_w) := by
  rcases hdomain with ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hdomain' : paper_strict_marriage_domain val_m val_w :=
    ⟨hstrictM, hstrictW, hposM, hposW⟩
  have hcomplete :
      paper_is_complete_matching (deferredAcceptance val_m val_w) :=
    paper_da_complete_on_strict_marriage_domain_of_card_eq
      val_m val_w hcard hdomain'
  exact paper_roth82_theorem6_of_complete_da_outcome
    val_m val_w hposM hposW hcomplete

/-! ## 7) Limits on eliminating manipulation -/

/-- The one-indexed rank of an alternative under a real-valued strict preference report. -/
noncomputable def paper_rank_of_choice {A : Type*} [Fintype A] [DecidableEq A]
    (score : A → ℝ) (a : A) : ℕ :=
  ((Finset.univ : Finset A).filter fun b => score a < score b).card + 1

/--
A report misrepresents the `k`th choice if some alternative that is truly ranked
`k` is no longer ranked `k` in the report.
-/
def paper_report_misrepresents_kth_choice {A : Type*} [Fintype A] [DecidableEq A]
    (true_score report_score : A → ℝ) (k : ℕ) : Prop :=
  ∃ a, paper_rank_of_choice true_score a = k ∧
    paper_rank_of_choice report_score a ≠ k

/--
A mechanism has a profitable `k`th-choice manipulation at some profile if one
agent on either side can profitably change a report in a way that changes the
rank of an alternative that was truly ranked `k`.
-/
def paper_stable_procedure_has_profitable_kth_choice_misreport
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (k : ℕ)
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∃ val_m val_w,
    (∃ m report_m,
      paper_report_misrepresents_kth_choice (val_m m) report_m k ∧
        paper_profitable_man_misreport mechanism val_m val_w m report_m) ∨
    (∃ w report_w,
      paper_report_misrepresents_kth_choice (val_w w) report_w k ∧
        paper_profitable_woman_misreport mechanism val_m val_w w report_w)

/--
Compatibility Theorem 7 property for a fixed finite marriage domain: every
stable procedure admits some profitable `k`th-choice manipulation, without
requiring strict true and reported profiles.
-/
def paper_no_stable_procedure_avoids_kth_choice_manipulation_on
    (M W : Type*) [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (k : ℕ) : Prop :=
  ∀ mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W,
    paper_stable_matching_procedure mechanism →
      paper_stable_procedure_has_profitable_kth_choice_misreport k mechanism

/--
Source-domain version of the Theorem 7 manipulation predicate: the true and
unilaterally reported profiles are complete, strict marriage profiles.
-/
def paper_stable_procedure_has_profitable_strict_kth_choice_misreport
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (k : ℕ)
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∃ val_m val_w, paper_strict_marriage_domain val_m val_w ∧
    ((∃ m report_m,
      paper_strict_marriage_domain (Function.update val_m m report_m) val_w ∧
        paper_report_misrepresents_kth_choice (val_m m) report_m k ∧
          paper_profitable_man_misreport mechanism val_m val_w m report_m) ∨
    (∃ w report_w,
      paper_strict_marriage_domain val_m (Function.update val_w w report_w) ∧
        paper_report_misrepresents_kth_choice (val_w w) report_w k ∧
          paper_profitable_woman_misreport mechanism val_m val_w w report_w))

/-- Source-facing complete strict-marriage Theorem 7 property for a fixed finite domain. -/
def paper_no_stable_procedure_avoids_strict_kth_choice_manipulation_on
    (M W : Type*) [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (k : ℕ) : Prop :=
  ∀ mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W,
    paper_stable_matching_procedure_on_strict_marriage_domain mechanism →
      paper_stable_procedure_has_profitable_strict_kth_choice_misreport k mechanism

/--
Compatibility arbitrary-family obligation for Roth Theorem 7 without explicit
strict-profile hypotheses.  The strict-profile certificate below is the final
source-facing endpoint.
-/
def PaperTheorem7ArbitraryKFamilyCertificate : Prop :=
  ∀ k, 1 < k →
    ∃ n : ℕ,
      paper_no_stable_procedure_avoids_kth_choice_manipulation_on
        (Fin n) (Fin n) k

/-- Source-facing arbitrary-family obligation for Roth Theorem 7 on strict profiles. -/
def PaperTheorem7StrictArbitraryKFamilyCertificate : Prop :=
  ∀ k, 1 < k →
    ∃ n : ℕ,
      paper_no_stable_procedure_avoids_strict_kth_choice_manipulation_on
        (Fin n) (Fin n) k

/-! ### Theorem 7 padded Theorem 3 family -/

/--
The padded family used for Roth's Theorem 7.  The first three agents are the
Theorem 3 counterexample; the remaining `r` agents are dummy pairs.  The rank
being manipulated is `r + 2`, so this realizes every `k > 1` by taking
`r = k - 2`.
-/
abbrev Theorem7PaddedAgent (r : ℕ) := Fin (r + 3)

/-- Distinct dummy scores inserted between the manipulated agent's first and second core choices. -/
noncomputable def theorem7InterposedScore (r : ℕ) (a : Theorem7PaddedAgent r) : ℝ :=
  3 + (a.1 : ℝ) / (((r + 3 : ℕ) : ℝ))

/--
Distinct positive fallback scores below every core choice.  Positivity keeps
the padded family inside Roth's complete marriage domain; only their ordinal
position below the score `1` is used by the construction.
-/
noncomputable def theorem7BadScore {r : ℕ} (a : Theorem7PaddedAgent r) : ℝ :=
  ((a.1 + 1 : ℕ) : ℝ) / ((r + 4 : ℕ) : ℝ)

theorem theorem7InterposedScore_gt_two (r : ℕ) (a : Theorem7PaddedAgent r) :
    2 < theorem7InterposedScore r a := by
  unfold theorem7InterposedScore
  have hnonneg : 0 ≤ (a.1 : ℝ) / (((r + 3 : ℕ) : ℝ)) := by
    have hden : (0 : ℝ) ≤ (((r + 3 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.zero_le (r + 3)
    exact div_nonneg (by exact_mod_cast Nat.zero_le a.1) hden
  linarith

theorem theorem7InterposedScore_lt_four (r : ℕ) (a : Theorem7PaddedAgent r) :
    theorem7InterposedScore r a < 4 := by
  unfold theorem7InterposedScore
  have hdenpos : (0 : ℝ) < (((r + 3 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos (r + 2)
  have hnumlt : (a.1 : ℝ) < (((r + 3 : ℕ) : ℝ)) := by
    exact_mod_cast a.2
  have hfrac : (a.1 : ℝ) / (((r + 3 : ℕ) : ℝ)) < 1 :=
    (div_lt_one hdenpos).2 hnumlt
  linarith

theorem theorem7BadScore_pos {r : ℕ} (a : Theorem7PaddedAgent r) :
    0 < theorem7BadScore a := by
  unfold theorem7BadScore
  positivity

theorem theorem7BadScore_lt_one {r : ℕ} (a : Theorem7PaddedAgent r) :
    theorem7BadScore a < 1 := by
  unfold theorem7BadScore
  have hden : (0 : ℝ) < ((r + 4 : ℕ) : ℝ) := by positivity
  rw [div_lt_one hden]
  exact_mod_cast (Nat.add_lt_add_right a.2 1)

theorem theorem7BadScore_injective {r : ℕ} :
    Function.Injective (@theorem7BadScore r) := by
  intro a b h
  unfold theorem7BadScore at h
  have hden : (((r + 4 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hnum : (((a.1 + 1 : ℕ) : ℝ)) = (((b.1 + 1 : ℕ) : ℝ)) := by
    exact (div_left_inj' hden).mp h
  apply Fin.ext
  exact Nat.add_right_cancel (by exact_mod_cast hnum)

theorem theorem7InterposedScore_injective (r : ℕ) :
    Function.Injective (theorem7InterposedScore r) := by
  intro a b h
  apply Fin.ext
  unfold theorem7InterposedScore at h
  have hdiv :
      (a.1 : ℝ) / (((r + 3 : ℕ) : ℝ)) =
        (b.1 : ℝ) / (((r + 3 : ℕ) : ℝ)) := by
    linarith
  have hdenpos : (0 : ℝ) < (((r + 3 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos (r + 2)
  have hdenne : (((r + 3 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hdenpos
  have hmul := congrArg (fun x : ℝ => x * (((r + 3 : ℕ) : ℝ))) hdiv
  change (a.1 : ℝ) / (((r + 3 : ℕ) : ℝ)) * (((r + 3 : ℕ) : ℝ)) =
    (b.1 : ℝ) / (((r + 3 : ℕ) : ℝ)) * (((r + 3 : ℕ) : ℝ)) at hmul
  have hcast : (a.1 : ℝ) = (b.1 : ℝ) := by
    rw [div_mul_cancel₀ (a.1 : ℝ) hdenne,
      div_mul_cancel₀ (b.1 : ℝ) hdenne] at hmul
    exact hmul
  exact_mod_cast hcast

/-- Embed a core Theorem 3 agent into the padded Theorem 7 market. -/
def theorem7Core (r : ℕ) (a : Theorem3Agent) : Theorem7PaddedAgent r :=
  ⟨a.1, Nat.lt_of_lt_of_le a.2 (Nat.le_add_left 3 r)⟩

@[simp] theorem theorem7Core_val (r : ℕ) (a : Theorem3Agent) :
    (theorem7Core r a).1 = a.1 := rfl

@[simp] theorem theorem7Core_zero (r : ℕ) :
    theorem7Core r 0 = (0 : Theorem7PaddedAgent r) := by
  ext
  rfl

@[simp] theorem theorem7Core_one (r : ℕ) :
    theorem7Core r 1 = (1 : Theorem7PaddedAgent r) := by
  ext
  rfl

@[simp] theorem theorem7Core_two (r : ℕ) :
    theorem7Core r 2 = (2 : Theorem7PaddedAgent r) := by
  ext
  rfl

@[simp] private theorem theorem7Padded_zero_ne_one (r : ℕ) :
    (0 : Theorem7PaddedAgent r) ≠ 1 := by
  intro h
  have hv := congrArg Fin.val h
  have h0 : ((0 : Theorem7PaddedAgent r).val) = 0 :=
    Fin.val_cast_of_lt (Nat.lt_of_lt_of_le (by decide : 0 < 3) (Nat.le_add_left 3 r))
  have h1 : ((1 : Theorem7PaddedAgent r).val) = 1 :=
    Fin.val_cast_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 3) (Nat.le_add_left 3 r))
  rw [h0, h1] at hv
  norm_num at hv

@[simp] private theorem theorem7Padded_one_ne_zero (r : ℕ) :
    (1 : Theorem7PaddedAgent r) ≠ 0 := by
  intro h
  exact theorem7Padded_zero_ne_one r h.symm

@[simp] private theorem theorem7Padded_zero_ne_two (r : ℕ) :
    (0 : Theorem7PaddedAgent r) ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  have h0 : ((0 : Theorem7PaddedAgent r).val) = 0 :=
    Fin.val_cast_of_lt (Nat.lt_of_lt_of_le (by decide : 0 < 3) (Nat.le_add_left 3 r))
  have h2 : ((2 : Theorem7PaddedAgent r).val) = 2 :=
    Fin.val_cast_of_lt (Nat.lt_of_lt_of_le (by decide : 2 < 3) (Nat.le_add_left 3 r))
  rw [h0, h2] at hv
  norm_num at hv

@[simp] private theorem theorem7Padded_two_ne_zero (r : ℕ) :
    (2 : Theorem7PaddedAgent r) ≠ 0 := by
  intro h
  exact theorem7Padded_zero_ne_two r h.symm

@[simp] private theorem theorem7Padded_one_ne_two (r : ℕ) :
    (1 : Theorem7PaddedAgent r) ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  have h1 : ((1 : Theorem7PaddedAgent r).val) = 1 :=
    Fin.val_cast_of_lt (Nat.lt_of_lt_of_le (by decide : 1 < 3) (Nat.le_add_left 3 r))
  have h2 : ((2 : Theorem7PaddedAgent r).val) = 2 :=
    Fin.val_cast_of_lt (Nat.lt_of_lt_of_le (by decide : 2 < 3) (Nat.le_add_left 3 r))
  rw [h1, h2] at hv
  norm_num at hv

@[simp] private theorem theorem7Padded_two_ne_one (r : ℕ) :
    (2 : Theorem7PaddedAgent r) ≠ 1 := by
  intro h
  exact theorem7Padded_one_ne_two r h.symm

/-- Project a padded agent back to the Theorem 3 core when possible. -/
def theorem7AsCore? (r : ℕ) (a : Theorem7PaddedAgent r) : Option Theorem3Agent :=
  if a = (0 : Theorem7PaddedAgent r) then some 0
  else if a = (1 : Theorem7PaddedAgent r) then some 1
  else if a = (2 : Theorem7PaddedAgent r) then some 2
  else none

@[simp] theorem theorem7AsCore?_zero (r : ℕ) :
    theorem7AsCore? r (0 : Theorem7PaddedAgent r) = some 0 := by
  simp [theorem7AsCore?]

@[simp] theorem theorem7AsCore?_one (r : ℕ) :
    theorem7AsCore? r (1 : Theorem7PaddedAgent r) = some 1 := by
  simp [theorem7AsCore?]

@[simp] theorem theorem7AsCore?_two (r : ℕ) :
    theorem7AsCore? r (2 : Theorem7PaddedAgent r) = some 2 := by
  simp [theorem7AsCore?]

@[simp] theorem theorem7AsCore?_core (r : ℕ) (a : Theorem3Agent) :
    theorem7AsCore? r (theorem7Core r a) = some a := by
  fin_cases a <;> simp

theorem theorem7AsCore?_eq_some_iff {r : ℕ} {a : Theorem7PaddedAgent r}
    {c : Theorem3Agent} :
    theorem7AsCore? r a = some c ↔ a = theorem7Core r c := by
  constructor
  · intro h
    unfold theorem7AsCore? at h
    split_ifs at h with h0 h1 h2
    · cases h
      simpa using h0
    · cases h
      simpa using h1
    · cases h
      simpa using h2
  · intro h
    subst h
    simp

private theorem theorem7AsCore?_none_ne_zero {r : ℕ} {a : Theorem7PaddedAgent r}
    (h : theorem7AsCore? r a = none) : a ≠ 0 := by
  intro ha
  subst a
  simp at h

private theorem theorem7AsCore?_none_ne_one {r : ℕ} {a : Theorem7PaddedAgent r}
    (h : theorem7AsCore? r a = none) : a ≠ 1 := by
  intro ha
  subst a
  simp at h

private theorem theorem7AsCore?_none_ne_two {r : ℕ} {a : Theorem7PaddedAgent r}
    (h : theorem7AsCore? r a = none) : a ≠ 2 := by
  intro ha
  subst a
  simp at h

/--
Woman `w₁`'s true report in the padded family.  Dummy men are placed between
her first and second core choices, making the old second choice the `(r + 2)`nd
choice.
-/
noncomputable def theorem7PaddedWoman0TrueReport (r : ℕ) : Theorem7PaddedAgent r → ℝ := fun m =>
  if m = (0 : Theorem7PaddedAgent r) then 4
  else if m = (2 : Theorem7PaddedAgent r) then 2
  else if m = (1 : Theorem7PaddedAgent r) then 1
  else theorem7InterposedScore r m

/-- Woman `w₁`'s padded prime report: the old second and third core choices swap. -/
noncomputable def theorem7PaddedWoman0PrimeReport (r : ℕ) : Theorem7PaddedAgent r → ℝ := fun m =>
  if m = (0 : Theorem7PaddedAgent r) then 4
  else if m = (1 : Theorem7PaddedAgent r) then 2
  else if m = (2 : Theorem7PaddedAgent r) then 1
  else theorem7InterposedScore r m

/--
Man `m₁`'s true report in the padded family.  Dummy women are placed between
his first and second core choices.
-/
noncomputable def theorem7PaddedMan0TrueReport (r : ℕ) : Theorem7PaddedAgent r → ℝ := fun w =>
  if w = (1 : Theorem7PaddedAgent r) then 4
  else if w = (0 : Theorem7PaddedAgent r) then 2
  else if w = (2 : Theorem7PaddedAgent r) then 1
  else theorem7InterposedScore r w

/-- Man `m₁`'s padded double-prime report: the old second and third core choices swap. -/
noncomputable def theorem7PaddedMan0DoublePrimeReport (r : ℕ) : Theorem7PaddedAgent r → ℝ := fun w =>
  if w = (1 : Theorem7PaddedAgent r) then 4
  else if w = (2 : Theorem7PaddedAgent r) then 2
  else if w = (0 : Theorem7PaddedAgent r) then 1
  else theorem7InterposedScore r w

set_option linter.unusedSimpArgs false in
private theorem theorem7CoreInterposedReport_strict
    (r : ℕ) {top mid low : Theorem7PaddedAgent r}
    (htm : top ≠ mid) (htl : top ≠ low) (hml : mid ≠ low) :
    ∀ a b,
      (if a = top then (4 : ℝ) else if a = mid then 2 else if a = low then 1
        else theorem7InterposedScore r a) =
      (if b = top then (4 : ℝ) else if b = mid then 2 else if b = low then 1
        else theorem7InterposedScore r b) → a = b := by
  intro a b h
  have hmt : mid ≠ top := htm.symm
  have hlt : low ≠ top := htl.symm
  have hlm : low ≠ mid := hml.symm
  by_cases hat : a = top
  · subst a
    by_cases hbt : b = top
    · subst b
      rfl
    · by_cases hbm : b = mid
      · subst b
        simp [hbt, htm, htl, hml, hmt, hlt, hlm] at h
      · by_cases hbl : b = low
        · subst b
          simp [hbt, hbm, htm, htl, hml, hmt, hlt, hlm] at h
        · simp [hbt, hbm, hbl, htm, htl, hml, hmt, hlt, hlm] at h
          have hb := theorem7InterposedScore_lt_four r b
          linarith
  · by_cases ham : a = mid
    · subst a
      by_cases hbt : b = top
      · subst b
        simp [hat, htm, htl, hml, hmt, hlt, hlm] at h
      · by_cases hbm : b = mid
        · subst b
          rfl
        · by_cases hbl : b = low
          · subst b
            simp [hat, hbt, hbm, htm, htl, hml, hmt, hlt, hlm] at h
          · simp [hat, hbt, hbm, hbl, htm, htl, hml, hmt, hlt, hlm] at h
            have hb := theorem7InterposedScore_gt_two r b
            linarith
    · by_cases hal : a = low
      · subst a
        by_cases hbt : b = top
        · subst b
          simp [hat, ham, htm, htl, hml, hmt, hlt, hlm] at h
        · by_cases hbm : b = mid
          · subst b
            simp [hat, ham, hbt, htm, htl, hml, hmt, hlt, hlm] at h
          · by_cases hbl : b = low
            · subst b
              rfl
            · simp [hat, ham, hbt, hbm, hbl, htm, htl, hml, hmt, hlt, hlm] at h
              have hb := theorem7InterposedScore_gt_two r b
              linarith
      · by_cases hbt : b = top
        · subst b
          simp [hat, ham, hal, htm, htl, hml, hmt, hlt, hlm] at h
          have ha := theorem7InterposedScore_lt_four r a
          linarith
        · by_cases hbm : b = mid
          · subst b
            simp [hat, ham, hal, hbt, htm, htl, hml, hmt, hlt, hlm] at h
            have ha := theorem7InterposedScore_gt_two r a
            linarith
          · by_cases hbl : b = low
            · subst b
              simp [hat, ham, hal, hbt, hbm, htm, htl, hml, hmt, hlt, hlm] at h
              have ha := theorem7InterposedScore_gt_two r a
              linarith
            · simp [hat, ham, hal, hbt, hbm, hbl, htm, htl, hml, hmt, hlt, hlm] at h
              exact theorem7InterposedScore_injective r h

private theorem theorem7Padded_ne_of_val_ne {r : ℕ}
    {a b : Theorem7PaddedAgent r} (hval : a.1 ≠ b.1) : a ≠ b := by
  intro h
  exact hval (congrArg Fin.val h)

theorem theorem7PaddedWoman0TrueReport_strict (r : ℕ) :
    ∀ a b, theorem7PaddedWoman0TrueReport r a =
      theorem7PaddedWoman0TrueReport r b → a = b := by
  simpa [theorem7PaddedWoman0TrueReport] using
    (theorem7CoreInterposedReport_strict (r := r)
      (top := (0 : Theorem7PaddedAgent r)) (mid := 2) (low := 1)
      (theorem7Padded_zero_ne_two r)
      (theorem7Padded_zero_ne_one r)
      (theorem7Padded_one_ne_two r).symm)

theorem theorem7PaddedWoman0PrimeReport_strict (r : ℕ) :
    ∀ a b, theorem7PaddedWoman0PrimeReport r a =
      theorem7PaddedWoman0PrimeReport r b → a = b := by
  simpa [theorem7PaddedWoman0PrimeReport] using
    (theorem7CoreInterposedReport_strict (r := r)
      (top := (0 : Theorem7PaddedAgent r)) (mid := 1) (low := 2)
      (theorem7Padded_zero_ne_one r)
      (theorem7Padded_zero_ne_two r)
      (theorem7Padded_one_ne_two r))

theorem theorem7PaddedMan0TrueReport_strict (r : ℕ) :
    ∀ a b, theorem7PaddedMan0TrueReport r a =
      theorem7PaddedMan0TrueReport r b → a = b := by
  simpa [theorem7PaddedMan0TrueReport] using
    (theorem7CoreInterposedReport_strict (r := r)
      (top := (1 : Theorem7PaddedAgent r)) (mid := 0) (low := 2)
      (theorem7Padded_zero_ne_one r).symm
      (theorem7Padded_one_ne_two r)
      (theorem7Padded_zero_ne_two r))

theorem theorem7PaddedMan0DoublePrimeReport_strict (r : ℕ) :
    ∀ a b, theorem7PaddedMan0DoublePrimeReport r a =
      theorem7PaddedMan0DoublePrimeReport r b → a = b := by
  simpa [theorem7PaddedMan0DoublePrimeReport] using
    (theorem7CoreInterposedReport_strict (r := r)
      (top := (1 : Theorem7PaddedAgent r)) (mid := 2) (low := 0)
      (theorem7Padded_one_ne_two r)
      (theorem7Padded_zero_ne_one r).symm
      (theorem7Padded_zero_ne_two r).symm)

theorem theorem7PaddedWoman0TrueReport_pos (r : ℕ) :
    ∀ a, 0 < theorem7PaddedWoman0TrueReport r a := by
  intro a
  simp only [theorem7PaddedWoman0TrueReport]
  split_ifs <;> try norm_num
  linarith [theorem7InterposedScore_gt_two r a]

theorem theorem7PaddedWoman0PrimeReport_pos (r : ℕ) :
    ∀ a, 0 < theorem7PaddedWoman0PrimeReport r a := by
  intro a
  simp only [theorem7PaddedWoman0PrimeReport]
  split_ifs <;> try norm_num
  linarith [theorem7InterposedScore_gt_two r a]

theorem theorem7PaddedMan0TrueReport_pos (r : ℕ) :
    ∀ a, 0 < theorem7PaddedMan0TrueReport r a := by
  intro a
  simp only [theorem7PaddedMan0TrueReport]
  split_ifs <;> try norm_num
  linarith [theorem7InterposedScore_gt_two r a]

theorem theorem7PaddedMan0DoublePrimeReport_pos (r : ℕ) :
    ∀ a, 0 < theorem7PaddedMan0DoublePrimeReport r a := by
  intro a
  simp only [theorem7PaddedMan0DoublePrimeReport]
  split_ifs <;> try norm_num
  linarith [theorem7InterposedScore_gt_two r a]

set_option linter.unusedSimpArgs false in
private theorem theorem7CoreBadReport_strict
    {r : ℕ} {top mid low : Theorem7PaddedAgent r}
    (htm : top ≠ mid) (htl : top ≠ low) (hml : mid ≠ low) :
    ∀ a b,
      (if a = top then (3 : ℝ) else if a = mid then 2 else if a = low then 1
        else theorem7BadScore a) =
      (if b = top then (3 : ℝ) else if b = mid then 2 else if b = low then 1
        else theorem7BadScore b) → a = b := by
  intro a b h
  have hmt : mid ≠ top := htm.symm
  have hlt : low ≠ top := htl.symm
  have hlm : low ≠ mid := hml.symm
  by_cases hat : a = top
  · subst a
    by_cases hbt : b = top
    · subst b
      rfl
    · by_cases hbm : b = mid
      · subst b
        simp [hbt, htm, htl, hml, hmt, hlt, hlm] at h
      · by_cases hbl : b = low
        · subst b
          simp [hbt, hbm, htm, htl, hml, hmt, hlt, hlm] at h
        · simp [hbt, hbm, hbl, htm, htl, hml, hmt, hlt, hlm] at h
          have hb := theorem7BadScore_lt_one b
          linarith
  · by_cases ham : a = mid
    · subst a
      by_cases hbt : b = top
      · subst b
        simp [hat, htm, htl, hml, hmt, hlt, hlm] at h
      · by_cases hbm : b = mid
        · subst b
          rfl
        · by_cases hbl : b = low
          · subst b
            simp [hat, hbt, hbm, htm, htl, hml, hmt, hlt, hlm] at h
          · simp [hat, hbt, hbm, hbl, htm, htl, hml, hmt, hlt, hlm] at h
            have hb := theorem7BadScore_lt_one b
            linarith
    · by_cases hal : a = low
      · subst a
        by_cases hbt : b = top
        · subst b
          simp [hat, ham, htm, htl, hml, hmt, hlt, hlm] at h
        · by_cases hbm : b = mid
          · subst b
            simp [hat, ham, hbt, htm, htl, hml, hmt, hlt, hlm] at h
          · by_cases hbl : b = low
            · subst b
              rfl
            · simp [hat, ham, hbt, hbm, hbl, htm, htl, hml, hmt, hlt, hlm] at h
              have hb := theorem7BadScore_lt_one b
              linarith
      · by_cases hbt : b = top
        · subst b
          simp [hat, ham, hal, htm, htl, hml, hmt, hlt, hlm] at h
          have ha := theorem7BadScore_lt_one a
          linarith
        · by_cases hbm : b = mid
          · subst b
            simp [hat, ham, hal, hbt, htm, htl, hml, hmt, hlt, hlm] at h
            have ha := theorem7BadScore_lt_one a
            linarith
          · by_cases hbl : b = low
            · subst b
              simp [hat, ham, hal, hbt, hbm, htm, htl, hml, hmt, hlt, hlm] at h
              have ha := theorem7BadScore_lt_one a
              linarith
            · simp [hat, ham, hal, hbt, hbm, hbl, htm, htl, hml, hmt, hlt, hlm] at h
              exact theorem7BadScore_injective h

private theorem theorem7DummyReport_strict {r : ℕ} (self : Theorem7PaddedAgent r) :
    ∀ a b,
      (if a = self then (1000 : ℝ) else theorem7BadScore a) =
      (if b = self then (1000 : ℝ) else theorem7BadScore b) → a = b := by
  intro a b h
  by_cases ha : a = self
  · subst a
    by_cases hb : b = self
    · subst b
      rfl
    · simp [hb] at h
      have hbad := theorem7BadScore_lt_one b
      linarith
  · by_cases hb : b = self
    · subst b
      simp [ha] at h
      have hbad := theorem7BadScore_lt_one a
      linarith
    · simp [ha, hb] at h
      exact theorem7BadScore_injective h

/-- Padded Theorem 3 base profile, men side. -/
noncomputable def theorem7PaddedMenProfile (r : ℕ) :
    Theorem7PaddedAgent r → Theorem7PaddedAgent r → ℝ := fun m w =>
  if m = (0 : Theorem7PaddedAgent r) then
    theorem7PaddedMan0TrueReport r w
  else if m = (1 : Theorem7PaddedAgent r) then
    if w = (0 : Theorem7PaddedAgent r) then 3
    else if w = (1 : Theorem7PaddedAgent r) then 2
    else if w = (2 : Theorem7PaddedAgent r) then 1
    else theorem7BadScore w
  else if m = (2 : Theorem7PaddedAgent r) then
    if w = (0 : Theorem7PaddedAgent r) then 3
    else if w = (1 : Theorem7PaddedAgent r) then 2
    else if w = (2 : Theorem7PaddedAgent r) then 1
    else theorem7BadScore w
  else if w = m then 1000 else theorem7BadScore w

/-- Padded Theorem 3 base profile, women side. -/
noncomputable def theorem7PaddedWomenProfile (r : ℕ) :
    Theorem7PaddedAgent r → Theorem7PaddedAgent r → ℝ := fun w m =>
  if w = (0 : Theorem7PaddedAgent r) then
    theorem7PaddedWoman0TrueReport r m
  else if w = (1 : Theorem7PaddedAgent r) then
    if m = (2 : Theorem7PaddedAgent r) then 3
    else if m = (0 : Theorem7PaddedAgent r) then 2
    else if m = (1 : Theorem7PaddedAgent r) then 1
    else theorem7BadScore m
  else if w = (2 : Theorem7PaddedAgent r) then
    if m = (0 : Theorem7PaddedAgent r) then 3
    else if m = (1 : Theorem7PaddedAgent r) then 2
    else if m = (2 : Theorem7PaddedAgent r) then 1
    else theorem7BadScore m
  else if m = w then 1000 else theorem7BadScore m

/-- Padded profile `P'`, differing only in woman `w₁`'s report. -/
noncomputable def theorem7PaddedWomenProfilePrime (r : ℕ) :
    Theorem7PaddedAgent r → Theorem7PaddedAgent r → ℝ :=
  Function.update (theorem7PaddedWomenProfile r) 0
    (theorem7PaddedWoman0PrimeReport r)

/-- Padded profile `P''`, differing only in man `m₁`'s report. -/
noncomputable def theorem7PaddedMenProfileDoublePrime (r : ℕ) :
    Theorem7PaddedAgent r → Theorem7PaddedAgent r → ℝ :=
  Function.update (theorem7PaddedMenProfile r) 0
    (theorem7PaddedMan0DoublePrimeReport r)

theorem theorem7PaddedMenProfile_strict (r : ℕ) :
    ∀ m w w', theorem7PaddedMenProfile r m w =
      theorem7PaddedMenProfile r m w' → w = w' := by
  intro m w w' h
  by_cases hm0 : m = (0 : Theorem7PaddedAgent r)
  · subst m
    exact theorem7PaddedMan0TrueReport_strict r w w' h
  · by_cases hm1 : m = (1 : Theorem7PaddedAgent r)
    · subst m
      exact theorem7CoreBadReport_strict
        (top := (0 : Theorem7PaddedAgent r)) (mid := 1) (low := 2)
        (theorem7Padded_zero_ne_one r) (theorem7Padded_zero_ne_two r)
        (theorem7Padded_one_ne_two r) w w' h
    · by_cases hm2 : m = (2 : Theorem7PaddedAgent r)
      · subst m
        exact theorem7CoreBadReport_strict
          (top := (0 : Theorem7PaddedAgent r)) (mid := 1) (low := 2)
          (theorem7Padded_zero_ne_one r) (theorem7Padded_zero_ne_two r)
          (theorem7Padded_one_ne_two r) w w' h
      · have h' :
            (if w = m then (1000 : ℝ) else theorem7BadScore w) =
              (if w' = m then (1000 : ℝ) else theorem7BadScore w') := by
          simpa [theorem7PaddedMenProfile, hm0, hm1, hm2] using h
        exact theorem7DummyReport_strict m w w' h'

theorem theorem7PaddedMenProfileDoublePrime_strict (r : ℕ) :
    ∀ m w w', theorem7PaddedMenProfileDoublePrime r m w =
      theorem7PaddedMenProfileDoublePrime r m w' → w = w' := by
  intro m w w' h
  by_cases hm0 : m = (0 : Theorem7PaddedAgent r)
  · subst m
    exact theorem7PaddedMan0DoublePrimeReport_strict r w w' h
  · have h' : theorem7PaddedMenProfile r m w =
        theorem7PaddedMenProfile r m w' := by
      simpa [theorem7PaddedMenProfileDoublePrime, hm0] using h
    exact theorem7PaddedMenProfile_strict r m w w' h'

theorem theorem7PaddedWomenProfile_strict (r : ℕ) :
    ∀ w m m', theorem7PaddedWomenProfile r w m =
      theorem7PaddedWomenProfile r w m' → m = m' := by
  intro w m m' h
  by_cases hw0 : w = (0 : Theorem7PaddedAgent r)
  · subst w
    exact theorem7PaddedWoman0TrueReport_strict r m m' h
  · by_cases hw1 : w = (1 : Theorem7PaddedAgent r)
    · subst w
      exact theorem7CoreBadReport_strict
        (top := (2 : Theorem7PaddedAgent r)) (mid := 0) (low := 1)
        (theorem7Padded_two_ne_zero r) (theorem7Padded_two_ne_one r)
        (theorem7Padded_zero_ne_one r) m m' h
    · by_cases hw2 : w = (2 : Theorem7PaddedAgent r)
      · subst w
        exact theorem7CoreBadReport_strict
          (top := (0 : Theorem7PaddedAgent r)) (mid := 1) (low := 2)
          (theorem7Padded_zero_ne_one r) (theorem7Padded_zero_ne_two r)
          (theorem7Padded_one_ne_two r) m m' h
      · have h' :
            (if m = w then (1000 : ℝ) else theorem7BadScore m) =
              (if m' = w then (1000 : ℝ) else theorem7BadScore m') := by
          simpa [theorem7PaddedWomenProfile, hw0, hw1, hw2] using h
        exact theorem7DummyReport_strict w m m' h'

theorem theorem7PaddedWomenProfilePrime_strict (r : ℕ) :
    ∀ w m m', theorem7PaddedWomenProfilePrime r w m =
      theorem7PaddedWomenProfilePrime r w m' → m = m' := by
  intro w m m' h
  by_cases hw0 : w = (0 : Theorem7PaddedAgent r)
  · subst w
    exact theorem7PaddedWoman0PrimeReport_strict r m m' h
  · have h' : theorem7PaddedWomenProfile r w m =
        theorem7PaddedWomenProfile r w m' := by
      simpa [theorem7PaddedWomenProfilePrime, hw0] using h
    exact theorem7PaddedWomenProfile_strict r w m m' h'

theorem theorem7PaddedMenProfile_pos (r : ℕ) :
    ∀ m w, 0 < theorem7PaddedMenProfile r m w := by
  intro m w
  simp only [theorem7PaddedMenProfile]
  split_ifs <;>
    first
    | exact theorem7PaddedMan0TrueReport_pos r w
    | exact theorem7BadScore_pos w
    | norm_num

theorem theorem7PaddedWomenProfile_pos (r : ℕ) :
    ∀ w m, 0 < theorem7PaddedWomenProfile r w m := by
  intro w m
  simp only [theorem7PaddedWomenProfile]
  split_ifs <;>
    first
    | exact theorem7PaddedWoman0TrueReport_pos r m
    | exact theorem7BadScore_pos m
    | norm_num

theorem theorem7PaddedWomenProfilePrime_pos (r : ℕ) :
    ∀ w m, 0 < theorem7PaddedWomenProfilePrime r w m := by
  intro w m
  by_cases hw : w = (0 : Theorem7PaddedAgent r)
  · subst w
    simpa [theorem7PaddedWomenProfilePrime] using
      theorem7PaddedWoman0PrimeReport_pos r m
  · simpa [theorem7PaddedWomenProfilePrime, hw] using
      theorem7PaddedWomenProfile_pos r w m

theorem theorem7PaddedMenProfileDoublePrime_pos (r : ℕ) :
    ∀ m w, 0 < theorem7PaddedMenProfileDoublePrime r m w := by
  intro m w
  by_cases hm : m = (0 : Theorem7PaddedAgent r)
  · subst m
    simpa [theorem7PaddedMenProfileDoublePrime] using
      theorem7PaddedMan0DoublePrimeReport_pos r w
  · simpa [theorem7PaddedMenProfileDoublePrime, hm] using
      theorem7PaddedMenProfile_pos r m w

theorem theorem7Padded_base_strict_preference_profile (r : ℕ) :
    paper_strict_preference_profile (theorem7PaddedMenProfile r)
      (theorem7PaddedWomenProfile r) := by
  exact ⟨theorem7PaddedMenProfile_strict r, theorem7PaddedWomenProfile_strict r⟩

theorem theorem7Padded_woman_prime_strict_preference_profile (r : ℕ) :
    paper_strict_preference_profile (theorem7PaddedMenProfile r)
      (theorem7PaddedWomenProfilePrime r) := by
  exact ⟨theorem7PaddedMenProfile_strict r, theorem7PaddedWomenProfilePrime_strict r⟩

theorem theorem7Padded_man_double_prime_strict_preference_profile (r : ℕ) :
    paper_strict_preference_profile (theorem7PaddedMenProfileDoublePrime r)
      (theorem7PaddedWomenProfile r) := by
  exact ⟨theorem7PaddedMenProfileDoublePrime_strict r,
    theorem7PaddedWomenProfile_strict r⟩

theorem theorem7Padded_base_strict_marriage_domain (r : ℕ) :
    paper_strict_marriage_domain (theorem7PaddedMenProfile r)
      (theorem7PaddedWomenProfile r) := by
  exact ⟨theorem7PaddedMenProfile_strict r, theorem7PaddedWomenProfile_strict r,
    theorem7PaddedMenProfile_pos r, theorem7PaddedWomenProfile_pos r⟩

theorem theorem7Padded_woman_prime_strict_marriage_domain (r : ℕ) :
    paper_strict_marriage_domain (theorem7PaddedMenProfile r)
      (theorem7PaddedWomenProfilePrime r) := by
  exact ⟨theorem7PaddedMenProfile_strict r, theorem7PaddedWomenProfilePrime_strict r,
    theorem7PaddedMenProfile_pos r, theorem7PaddedWomenProfilePrime_pos r⟩

theorem theorem7Padded_man_double_prime_strict_marriage_domain (r : ℕ) :
    paper_strict_marriage_domain (theorem7PaddedMenProfileDoublePrime r)
      (theorem7PaddedWomenProfile r) := by
  exact ⟨theorem7PaddedMenProfileDoublePrime_strict r,
    theorem7PaddedWomenProfile_strict r,
    theorem7PaddedMenProfileDoublePrime_pos r, theorem7PaddedWomenProfile_pos r⟩

/-- Restrict a padded Theorem 7 assignment to its Theorem 3 core agents. -/
def theorem7RestrictAssignment (r : ℕ)
    (mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r)) :
    Assignment Theorem3Agent Theorem3Agent where
  m_match m := (mu.m_match (theorem7Core r m)).bind (theorem7AsCore? r)
  w_match w := (mu.w_match (theorem7Core r w)).bind (theorem7AsCore? r)
  consistent_m := by
    intro m w
    constructor
    · intro h
      simp only [Option.bind_eq_some_iff] at h ⊢
      rcases h with ⟨a, hma, ha⟩
      have haeq : a = theorem7Core r w := theorem7AsCore?_eq_some_iff.1 ha
      subst a
      exact ⟨theorem7Core r m,
        Assignment.w_match_eq_some_of_m_match_eq_some hma,
        theorem7AsCore?_core r m⟩
    · intro h
      simp only [Option.bind_eq_some_iff] at h ⊢
      rcases h with ⟨a, hwa, ha⟩
      have haeq : a = theorem7Core r m := theorem7AsCore?_eq_some_iff.1 ha
      subst a
      exact ⟨theorem7Core r w,
        (mu.consistent_m (theorem7Core r m) (theorem7Core r w)).2 hwa,
        theorem7AsCore?_core r w⟩

@[simp] theorem theorem7RestrictAssignment_m_match
    (r : ℕ) (mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r))
    (m : Theorem3Agent) :
    (theorem7RestrictAssignment r mu).m_match m =
      (mu.m_match (theorem7Core r m)).bind (theorem7AsCore? r) := rfl

@[simp] theorem theorem7RestrictAssignment_w_match
    (r : ℕ) (mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r))
    (w : Theorem3Agent) :
    (theorem7RestrictAssignment r mu).w_match w =
      (mu.w_match (theorem7Core r w)).bind (theorem7AsCore? r) := rfl

private theorem theorem7Restrict_m_match_eq_some
    {r : ℕ} {mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r)}
    {m w : Theorem3Agent}
    (h : (theorem7RestrictAssignment r mu).m_match m = some w) :
    mu.m_match (theorem7Core r m) = some (theorem7Core r w) := by
  simp only [theorem7RestrictAssignment_m_match, Option.bind_eq_some_iff] at h
  rcases h with ⟨a, ha, hacore⟩
  have haeq : a = theorem7Core r w := theorem7AsCore?_eq_some_iff.1 hacore
  simpa [haeq] using ha

private theorem theorem7Restrict_w_match_eq_some
    {r : ℕ} {mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r)}
    {w m : Theorem3Agent}
    (h : (theorem7RestrictAssignment r mu).w_match w = some m) :
    mu.w_match (theorem7Core r w) = some (theorem7Core r m) := by
  simp only [theorem7RestrictAssignment_w_match, Option.bind_eq_some_iff] at h
  rcases h with ⟨a, ha, hacore⟩
  have haeq : a = theorem7Core r m := theorem7AsCore?_eq_some_iff.1 hacore
  simpa [haeq] using ha

private theorem theorem7_dummy_self_match_of_stable
    {A : Type*} [DecidableEq A]
    {val_m val_w : A → A → ℝ} {mu : Assignment A A} (d : A)
    (hmOwn : val_m d d = 1000)
    (hmOther : ∀ w, w ≠ d → val_m d w < 1000)
    (hwOwn : val_w d d = 1000)
    (hwOther : ∀ m, m ≠ d → val_w d m < 1000)
    (hstable : paper_is_stable val_m val_w mu) :
    mu.m_match d = some d := by
  by_contra hnot
  have hmPref : paper_matching_valM val_m d (mu.m_match d) < val_m d d := by
    cases hcur : mu.m_match d with
    | none =>
        simp [paper_matching_valM, hmOwn]
    | some w =>
        by_cases hwd : w = d
        · subst w
          exact False.elim (hnot hcur)
        · simpa [paper_matching_valM, hmOwn] using hmOther w hwd
  have hwPref : paper_matching_valW val_w d (mu.w_match d) < val_w d d := by
    cases hcur : mu.w_match d with
    | none =>
        simp [paper_matching_valW, hwOwn]
    | some m =>
        by_cases hmd : m = d
        · subst m
          have hm : mu.m_match d = some d := (mu.consistent_m d d).2 hcur
          exact False.elim (hnot hm)
        · simpa [paper_matching_valW, hwOwn] using hwOther m hmd
  exact hstable.2.2 d d hmPref hwPref

private theorem theorem7Padded_dummy_self_match_base
    {r : ℕ} {mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r)}
    (hstable : paper_is_stable (theorem7PaddedMenProfile r)
      (theorem7PaddedWomenProfile r) mu)
    {d : Theorem7PaddedAgent r}
    (hd0 : d ≠ 0) (hd1 : d ≠ 1) (hd2 : d ≠ 2) :
    mu.m_match d = some d := by
  refine theorem7_dummy_self_match_of_stable (d := d) ?_ ?_ ?_ ?_ hstable
  · simp [theorem7PaddedMenProfile, hd0, hd1, hd2]
  · intro w hwd
    simp [theorem7PaddedMenProfile, hd0, hd1, hd2, hwd]
    have hbad := theorem7BadScore_lt_one w
    linarith
  · simp [theorem7PaddedWomenProfile, hd0, hd1, hd2]
  · intro m hmd
    simp [theorem7PaddedWomenProfile, hd0, hd1, hd2, hmd]
    have hbad := theorem7BadScore_lt_one m
    linarith

private theorem theorem7Padded_dummy_self_match_woman_prime
    {r : ℕ} {mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r)}
    (hstable : paper_is_stable (theorem7PaddedMenProfile r)
      (theorem7PaddedWomenProfilePrime r) mu)
    {d : Theorem7PaddedAgent r}
    (hd0 : d ≠ 0) (hd1 : d ≠ 1) (hd2 : d ≠ 2) :
    mu.m_match d = some d := by
  refine theorem7_dummy_self_match_of_stable (d := d) ?_ ?_ ?_ ?_ hstable
  · simp [theorem7PaddedMenProfile, hd0, hd1, hd2]
  · intro w hwd
    simp [theorem7PaddedMenProfile, hd0, hd1, hd2, hwd]
    have hbad := theorem7BadScore_lt_one w
    linarith
  · simp [theorem7PaddedWomenProfilePrime, theorem7PaddedWomenProfile, hd0, hd1, hd2]
  · intro m hmd
    simp [theorem7PaddedWomenProfilePrime, theorem7PaddedWomenProfile, hd0, hd1, hd2, hmd]
    have hbad := theorem7BadScore_lt_one m
    linarith

private theorem theorem7Padded_dummy_self_match_man_double_prime
    {r : ℕ} {mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r)}
    (hstable : paper_is_stable (theorem7PaddedMenProfileDoublePrime r)
      (theorem7PaddedWomenProfile r) mu)
    {d : Theorem7PaddedAgent r}
    (hd0 : d ≠ 0) (hd1 : d ≠ 1) (hd2 : d ≠ 2) :
    mu.m_match d = some d := by
  refine theorem7_dummy_self_match_of_stable (d := d) ?_ ?_ ?_ ?_ hstable
  · simp [theorem7PaddedMenProfileDoublePrime, theorem7PaddedMenProfile, hd0, hd1, hd2]
  · intro w hwd
    simp [theorem7PaddedMenProfileDoublePrime, theorem7PaddedMenProfile, hd0, hd1, hd2, hwd]
    have hbad := theorem7BadScore_lt_one w
    linarith
  · simp [theorem7PaddedWomenProfile, hd0, hd1, hd2]
  · intro m hmd
    simp [theorem7PaddedWomenProfile, hd0, hd1, hd2, hmd]
    have hbad := theorem7BadScore_lt_one m
    linarith

private theorem theorem7Padded_core_man_not_matched_dummy_base
    {r : ℕ} {mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r)}
    (hstable : paper_is_stable (theorem7PaddedMenProfile r)
      (theorem7PaddedWomenProfile r) mu)
    (m : Theorem3Agent) {d : Theorem7PaddedAgent r}
    (hd : theorem7AsCore? r d = none) :
    mu.m_match (theorem7Core r m) ≠ some d := by
  intro hmatch
  have hwmatch : mu.w_match d = some (theorem7Core r m) :=
    Assignment.w_match_eq_some_of_m_match_eq_some hmatch
  have hd0 : d ≠ 0 := theorem7AsCore?_none_ne_zero hd
  have hd1 : d ≠ 1 := theorem7AsCore?_none_ne_one hd
  have hd2 : d ≠ 2 := theorem7AsCore?_none_ne_two hd
  have hmd : theorem7Core r m ≠ d := by
    fin_cases m
    · exact fun h => hd0 h.symm
    · exact fun h => hd1 h.symm
    · exact fun h => hd2 h.symm
  have hselfM : mu.m_match d = some d :=
    theorem7Padded_dummy_self_match_base hstable hd0 hd1 hd2
  have hselfW : mu.w_match d = some d :=
    Assignment.w_match_eq_some_of_m_match_eq_some hselfM
  exact hmd (Option.some.inj (hwmatch.symm.trans hselfW))

private theorem theorem7Padded_core_woman_not_matched_dummy_base
    {r : ℕ} {mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r)}
    (hstable : paper_is_stable (theorem7PaddedMenProfile r)
      (theorem7PaddedWomenProfile r) mu)
    (w : Theorem3Agent) {d : Theorem7PaddedAgent r}
    (hd : theorem7AsCore? r d = none) :
    mu.w_match (theorem7Core r w) ≠ some d := by
  intro hmatch
  have hmatchM : mu.m_match d = some (theorem7Core r w) :=
    (mu.consistent_m d (theorem7Core r w)).2 hmatch
  have hd0 : d ≠ 0 := theorem7AsCore?_none_ne_zero hd
  have hd1 : d ≠ 1 := theorem7AsCore?_none_ne_one hd
  have hd2 : d ≠ 2 := theorem7AsCore?_none_ne_two hd
  have hdw : theorem7Core r w ≠ d := by
    fin_cases w
    · exact fun h => hd0 h.symm
    · exact fun h => hd1 h.symm
    · exact fun h => hd2 h.symm
  have hself : mu.m_match d = some d :=
    theorem7Padded_dummy_self_match_base hstable hd0 hd1 hd2
  exact hdw (Option.some.inj (hmatchM.symm.trans hself))

private theorem theorem7Padded_core_man_not_matched_dummy_woman_prime
    {r : ℕ} {mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r)}
    (hstable : paper_is_stable (theorem7PaddedMenProfile r)
      (theorem7PaddedWomenProfilePrime r) mu)
    (m : Theorem3Agent) {d : Theorem7PaddedAgent r}
    (hd : theorem7AsCore? r d = none) :
    mu.m_match (theorem7Core r m) ≠ some d := by
  intro hmatch
  have hwmatch : mu.w_match d = some (theorem7Core r m) :=
    Assignment.w_match_eq_some_of_m_match_eq_some hmatch
  have hd0 : d ≠ 0 := theorem7AsCore?_none_ne_zero hd
  have hd1 : d ≠ 1 := theorem7AsCore?_none_ne_one hd
  have hd2 : d ≠ 2 := theorem7AsCore?_none_ne_two hd
  have hmd : theorem7Core r m ≠ d := by
    fin_cases m
    · exact fun h => hd0 h.symm
    · exact fun h => hd1 h.symm
    · exact fun h => hd2 h.symm
  have hselfM : mu.m_match d = some d :=
    theorem7Padded_dummy_self_match_woman_prime hstable hd0 hd1 hd2
  have hselfW : mu.w_match d = some d :=
    Assignment.w_match_eq_some_of_m_match_eq_some hselfM
  exact hmd (Option.some.inj (hwmatch.symm.trans hselfW))

private theorem theorem7Padded_core_woman_not_matched_dummy_woman_prime
    {r : ℕ} {mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r)}
    (hstable : paper_is_stable (theorem7PaddedMenProfile r)
      (theorem7PaddedWomenProfilePrime r) mu)
    (w : Theorem3Agent) {d : Theorem7PaddedAgent r}
    (hd : theorem7AsCore? r d = none) :
    mu.w_match (theorem7Core r w) ≠ some d := by
  intro hmatch
  have hmatchM : mu.m_match d = some (theorem7Core r w) :=
    (mu.consistent_m d (theorem7Core r w)).2 hmatch
  have hd0 : d ≠ 0 := theorem7AsCore?_none_ne_zero hd
  have hd1 : d ≠ 1 := theorem7AsCore?_none_ne_one hd
  have hd2 : d ≠ 2 := theorem7AsCore?_none_ne_two hd
  have hdw : theorem7Core r w ≠ d := by
    fin_cases w
    · exact fun h => hd0 h.symm
    · exact fun h => hd1 h.symm
    · exact fun h => hd2 h.symm
  have hself : mu.m_match d = some d :=
    theorem7Padded_dummy_self_match_woman_prime hstable hd0 hd1 hd2
  exact hdw (Option.some.inj (hmatchM.symm.trans hself))

private theorem theorem7Padded_core_man_not_matched_dummy_man_double_prime
    {r : ℕ} {mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r)}
    (hstable : paper_is_stable (theorem7PaddedMenProfileDoublePrime r)
      (theorem7PaddedWomenProfile r) mu)
    (m : Theorem3Agent) {d : Theorem7PaddedAgent r}
    (hd : theorem7AsCore? r d = none) :
    mu.m_match (theorem7Core r m) ≠ some d := by
  intro hmatch
  have hwmatch : mu.w_match d = some (theorem7Core r m) :=
    Assignment.w_match_eq_some_of_m_match_eq_some hmatch
  have hd0 : d ≠ 0 := theorem7AsCore?_none_ne_zero hd
  have hd1 : d ≠ 1 := theorem7AsCore?_none_ne_one hd
  have hd2 : d ≠ 2 := theorem7AsCore?_none_ne_two hd
  have hmd : theorem7Core r m ≠ d := by
    fin_cases m
    · exact fun h => hd0 h.symm
    · exact fun h => hd1 h.symm
    · exact fun h => hd2 h.symm
  have hselfM : mu.m_match d = some d :=
    theorem7Padded_dummy_self_match_man_double_prime hstable hd0 hd1 hd2
  have hselfW : mu.w_match d = some d :=
    Assignment.w_match_eq_some_of_m_match_eq_some hselfM
  exact hmd (Option.some.inj (hwmatch.symm.trans hselfW))

private theorem theorem7Padded_core_woman_not_matched_dummy_man_double_prime
    {r : ℕ} {mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r)}
    (hstable : paper_is_stable (theorem7PaddedMenProfileDoublePrime r)
      (theorem7PaddedWomenProfile r) mu)
    (w : Theorem3Agent) {d : Theorem7PaddedAgent r}
    (hd : theorem7AsCore? r d = none) :
    mu.w_match (theorem7Core r w) ≠ some d := by
  intro hmatch
  have hmatchM : mu.m_match d = some (theorem7Core r w) :=
    (mu.consistent_m d (theorem7Core r w)).2 hmatch
  have hd0 : d ≠ 0 := theorem7AsCore?_none_ne_zero hd
  have hd1 : d ≠ 1 := theorem7AsCore?_none_ne_one hd
  have hd2 : d ≠ 2 := theorem7AsCore?_none_ne_two hd
  have hdw : theorem7Core r w ≠ d := by
    fin_cases w
    · exact fun h => hd0 h.symm
    · exact fun h => hd1 h.symm
    · exact fun h => hd2 h.symm
  have hself : mu.m_match d = some d :=
    theorem7Padded_dummy_self_match_man_double_prime hstable hd0 hd1 hd2
  exact hdw (Option.some.inj (hmatchM.symm.trans hself))

private theorem theorem7Padded_restrict_stable_base
    {r : ℕ} (mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r))
    (hstable : paper_is_stable (theorem7PaddedMenProfile r)
      (theorem7PaddedWomenProfile r) mu) :
    paper_is_stable theorem3MenProfile theorem3WomenProfile
      (theorem7RestrictAssignment r mu) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    cases hcur : (theorem7RestrictAssignment r mu).m_match m with
    | none =>
        simp [paper_matching_valM]
    | some w =>
        fin_cases m <;> fin_cases w <;>
          norm_num [paper_matching_valM, theorem3MenProfile]
  · intro w
    cases hcur : (theorem7RestrictAssignment r mu).w_match w with
    | none =>
        simp [paper_matching_valW]
    | some m =>
        fin_cases w <;> fin_cases m <;>
          norm_num [paper_matching_valW, theorem3WomenProfile]
  · intro m w hm hw
    have hmPad :
        paper_matching_valM (theorem7PaddedMenProfile r) (theorem7Core r m)
            (mu.m_match (theorem7Core r m)) <
          theorem7PaddedMenProfile r (theorem7Core r m) (theorem7Core r w) := by
      cases hcur : mu.m_match (theorem7Core r m) with
      | none =>
          have hRestrict : (theorem7RestrictAssignment r mu).m_match m = none := by
            simp [theorem7RestrictAssignment, hcur]
          rw [hRestrict] at hm
          fin_cases m <;> fin_cases w <;>
            simp [paper_matching_valM,
              theorem3MenProfile, theorem7PaddedMenProfile,
              theorem7PaddedMan0TrueReport] at hm ⊢
      | some p =>
          cases hp : theorem7AsCore? r p with
          | none =>
              exact False.elim
                ((theorem7Padded_core_man_not_matched_dummy_base hstable m hp) hcur)
          | some c =>
              have hRestrict : (theorem7RestrictAssignment r mu).m_match m = some c := by
                simp [theorem7RestrictAssignment, hcur, hp]
              rw [hRestrict] at hm
              have hpEq : p = theorem7Core r c := theorem7AsCore?_eq_some_iff.1 hp
              subst p
              fin_cases m <;> fin_cases c <;> fin_cases w <;>
                simp [paper_matching_valM,
                  theorem3MenProfile, theorem7PaddedMenProfile,
                  theorem7PaddedMan0TrueReport] at hm ⊢ <;> linarith
    have hwPad :
        paper_matching_valW (theorem7PaddedWomenProfile r) (theorem7Core r w)
            (mu.w_match (theorem7Core r w)) <
          theorem7PaddedWomenProfile r (theorem7Core r w) (theorem7Core r m) := by
      cases hcur : mu.w_match (theorem7Core r w) with
      | none =>
          have hRestrict : (theorem7RestrictAssignment r mu).w_match w = none := by
            simp [theorem7RestrictAssignment, hcur]
          rw [hRestrict] at hw
          fin_cases w <;> fin_cases m <;>
            simp [paper_matching_valW,
              theorem3WomenProfile, theorem7PaddedWomenProfile,
              theorem7PaddedWoman0TrueReport] at hw ⊢
      | some p =>
          cases hp : theorem7AsCore? r p with
          | none =>
              exact False.elim
                ((theorem7Padded_core_woman_not_matched_dummy_base hstable w hp) hcur)
          | some c =>
              have hRestrict : (theorem7RestrictAssignment r mu).w_match w = some c := by
                simp [theorem7RestrictAssignment, hcur, hp]
              rw [hRestrict] at hw
              have hpEq : p = theorem7Core r c := theorem7AsCore?_eq_some_iff.1 hp
              subst p
              fin_cases w <;> fin_cases c <;> fin_cases m <;>
                simp [paper_matching_valW,
                  theorem3WomenProfile, theorem7PaddedWomenProfile,
                  theorem7PaddedWoman0TrueReport] at hw ⊢ <;> linarith
    exact hstable.2.2 (theorem7Core r m) (theorem7Core r w) hmPad hwPad

private theorem theorem7Padded_restrict_stable_woman_prime
    {r : ℕ} (mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r))
    (hstable : paper_is_stable (theorem7PaddedMenProfile r)
      (theorem7PaddedWomenProfilePrime r) mu) :
    paper_is_stable theorem3MenProfile theorem3WomenProfilePrime
      (theorem7RestrictAssignment r mu) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    cases hcur : (theorem7RestrictAssignment r mu).m_match m with
    | none =>
        simp [paper_matching_valM]
    | some w =>
        fin_cases m <;> fin_cases w <;>
          norm_num [paper_matching_valM, theorem3MenProfile]
  · intro w
    cases hcur : (theorem7RestrictAssignment r mu).w_match w with
    | none =>
        simp [paper_matching_valW]
    | some m =>
        fin_cases w <;> fin_cases m <;>
          norm_num [paper_matching_valW, theorem3WomenProfilePrime,
            theorem3WomenProfile, theorem3Woman0PrimeReport]
  · intro m w hm hw
    have hmPad :
        paper_matching_valM (theorem7PaddedMenProfile r) (theorem7Core r m)
            (mu.m_match (theorem7Core r m)) <
          theorem7PaddedMenProfile r (theorem7Core r m) (theorem7Core r w) := by
      cases hcur : mu.m_match (theorem7Core r m) with
      | none =>
          have hRestrict : (theorem7RestrictAssignment r mu).m_match m = none := by
            simp [theorem7RestrictAssignment, hcur]
          rw [hRestrict] at hm
          fin_cases m <;> fin_cases w <;>
            simp [paper_matching_valM,
              theorem3MenProfile, theorem7PaddedMenProfile,
              theorem7PaddedMan0TrueReport] at hm ⊢
      | some p =>
          cases hp : theorem7AsCore? r p with
          | none =>
              exact False.elim
                ((theorem7Padded_core_man_not_matched_dummy_woman_prime hstable m hp) hcur)
          | some c =>
              have hRestrict : (theorem7RestrictAssignment r mu).m_match m = some c := by
                simp [theorem7RestrictAssignment, hcur, hp]
              rw [hRestrict] at hm
              have hpEq : p = theorem7Core r c := theorem7AsCore?_eq_some_iff.1 hp
              subst p
              fin_cases m <;> fin_cases c <;> fin_cases w <;>
                simp [paper_matching_valM,
                  theorem3MenProfile, theorem7PaddedMenProfile,
                  theorem7PaddedMan0TrueReport] at hm ⊢ <;> linarith
    have hwPad :
        paper_matching_valW (theorem7PaddedWomenProfilePrime r) (theorem7Core r w)
            (mu.w_match (theorem7Core r w)) <
          theorem7PaddedWomenProfilePrime r (theorem7Core r w) (theorem7Core r m) := by
      cases hcur : mu.w_match (theorem7Core r w) with
      | none =>
          have hRestrict : (theorem7RestrictAssignment r mu).w_match w = none := by
            simp [theorem7RestrictAssignment, hcur]
          rw [hRestrict] at hw
          fin_cases w <;> fin_cases m <;>
            simp [paper_matching_valW,
              theorem3WomenProfilePrime, theorem3WomenProfile, theorem3Woman0PrimeReport,
              theorem7PaddedWomenProfilePrime, theorem7PaddedWomenProfile,
              theorem7PaddedWoman0PrimeReport] at hw ⊢
      | some p =>
          cases hp : theorem7AsCore? r p with
          | none =>
              exact False.elim
                ((theorem7Padded_core_woman_not_matched_dummy_woman_prime hstable w hp) hcur)
          | some c =>
              have hRestrict : (theorem7RestrictAssignment r mu).w_match w = some c := by
                simp [theorem7RestrictAssignment, hcur, hp]
              rw [hRestrict] at hw
              have hpEq : p = theorem7Core r c := theorem7AsCore?_eq_some_iff.1 hp
              subst p
              fin_cases w <;> fin_cases c <;> fin_cases m <;>
                simp [paper_matching_valW,
                  theorem3WomenProfilePrime, theorem3WomenProfile,
                  theorem3Woman0PrimeReport, theorem7PaddedWomenProfilePrime,
                  theorem7PaddedWomenProfile, theorem7PaddedWoman0PrimeReport] at hw ⊢ <;> linarith
    exact hstable.2.2 (theorem7Core r m) (theorem7Core r w) hmPad hwPad

private theorem theorem7Padded_restrict_stable_man_double_prime
    {r : ℕ} (mu : Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r))
    (hstable : paper_is_stable (theorem7PaddedMenProfileDoublePrime r)
      (theorem7PaddedWomenProfile r) mu) :
    paper_is_stable theorem3MenProfileDoublePrime theorem3WomenProfile
      (theorem7RestrictAssignment r mu) := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    cases hcur : (theorem7RestrictAssignment r mu).m_match m with
    | none =>
        simp [paper_matching_valM]
    | some w =>
        fin_cases m <;> fin_cases w <;>
          norm_num [paper_matching_valM, theorem3MenProfileDoublePrime,
            theorem3MenProfile, theorem3Man0DoublePrimeReport]
  · intro w
    cases hcur : (theorem7RestrictAssignment r mu).w_match w with
    | none =>
        simp [paper_matching_valW]
    | some m =>
        fin_cases w <;> fin_cases m <;>
          norm_num [paper_matching_valW, theorem3WomenProfile]
  · intro m w hm hw
    have hmPad :
        paper_matching_valM (theorem7PaddedMenProfileDoublePrime r) (theorem7Core r m)
            (mu.m_match (theorem7Core r m)) <
          theorem7PaddedMenProfileDoublePrime r (theorem7Core r m) (theorem7Core r w) := by
      cases hcur : mu.m_match (theorem7Core r m) with
      | none =>
          have hRestrict : (theorem7RestrictAssignment r mu).m_match m = none := by
            simp [theorem7RestrictAssignment, hcur]
          rw [hRestrict] at hm
          fin_cases m <;> fin_cases w <;>
            simp [paper_matching_valM,
              theorem3MenProfileDoublePrime, theorem3MenProfile,
              theorem3Man0DoublePrimeReport, theorem7PaddedMenProfileDoublePrime,
              theorem7PaddedMenProfile, theorem7PaddedMan0DoublePrimeReport] at hm ⊢
      | some p =>
          cases hp : theorem7AsCore? r p with
          | none =>
              exact False.elim
                ((theorem7Padded_core_man_not_matched_dummy_man_double_prime hstable m hp) hcur)
          | some c =>
              have hRestrict : (theorem7RestrictAssignment r mu).m_match m = some c := by
                simp [theorem7RestrictAssignment, hcur, hp]
              rw [hRestrict] at hm
              have hpEq : p = theorem7Core r c := theorem7AsCore?_eq_some_iff.1 hp
              subst p
              fin_cases m <;> fin_cases c <;> fin_cases w <;>
                simp [paper_matching_valM,
                  theorem3MenProfileDoublePrime, theorem3MenProfile,
                  theorem3Man0DoublePrimeReport, theorem7PaddedMenProfileDoublePrime,
                  theorem7PaddedMenProfile, theorem7PaddedMan0DoublePrimeReport] at hm ⊢ <;> linarith
    have hwPad :
        paper_matching_valW (theorem7PaddedWomenProfile r) (theorem7Core r w)
            (mu.w_match (theorem7Core r w)) <
          theorem7PaddedWomenProfile r (theorem7Core r w) (theorem7Core r m) := by
      cases hcur : mu.w_match (theorem7Core r w) with
      | none =>
          have hRestrict : (theorem7RestrictAssignment r mu).w_match w = none := by
            simp [theorem7RestrictAssignment, hcur]
          rw [hRestrict] at hw
          fin_cases w <;> fin_cases m <;>
            simp [paper_matching_valW,
              theorem3WomenProfile, theorem7PaddedWomenProfile,
              theorem7PaddedWoman0TrueReport] at hw ⊢
      | some p =>
          cases hp : theorem7AsCore? r p with
          | none =>
              exact False.elim
                ((theorem7Padded_core_woman_not_matched_dummy_man_double_prime hstable w hp) hcur)
          | some c =>
              have hRestrict : (theorem7RestrictAssignment r mu).w_match w = some c := by
                simp [theorem7RestrictAssignment, hcur, hp]
              rw [hRestrict] at hw
              have hpEq : p = theorem7Core r c := theorem7AsCore?_eq_some_iff.1 hp
              subst p
              fin_cases w <;> fin_cases c <;> fin_cases m <;>
                simp [paper_matching_valW,
                  theorem3WomenProfile, theorem7PaddedWomenProfile,
                  theorem7PaddedWoman0TrueReport] at hw ⊢ <;> linarith
    exact hstable.2.2 (theorem7Core r m) (theorem7Core r w) hmPad hwPad

private theorem theorem7Padded_card_univ_erase_one_erase_two (r : ℕ) :
    (((Finset.univ : Finset (Theorem7PaddedAgent r)).erase 1).erase 2).card = r + 1 := by
  have h21 : (2 : Theorem7PaddedAgent r) ∈
      ((Finset.univ : Finset (Theorem7PaddedAgent r)).erase 1) := by
    simp
  rw [Finset.card_erase_of_mem h21,
    Finset.card_erase_of_mem (by simp : (1 : Theorem7PaddedAgent r) ∈
      (Finset.univ : Finset (Theorem7PaddedAgent r)))]
  simp [Fintype.card_fin]

private theorem theorem7Padded_card_univ_erase_zero_erase_two (r : ℕ) :
    (((Finset.univ : Finset (Theorem7PaddedAgent r)).erase 0).erase 2).card = r + 1 := by
  have h20 : (2 : Theorem7PaddedAgent r) ∈
      ((Finset.univ : Finset (Theorem7PaddedAgent r)).erase 0) := by
    simp
  rw [Finset.card_erase_of_mem h20,
    Finset.card_erase_of_mem (by simp : (0 : Theorem7PaddedAgent r) ∈
      (Finset.univ : Finset (Theorem7PaddedAgent r)))]
  simp [Fintype.card_fin]

private theorem theorem7Padded_card_univ_erase_two (r : ℕ) :
    ((Finset.univ : Finset (Theorem7PaddedAgent r)).erase 2).card = r + 2 := by
  rw [Finset.card_erase_of_mem (by simp : (2 : Theorem7PaddedAgent r) ∈
    (Finset.univ : Finset (Theorem7PaddedAgent r)))]
  simp [Fintype.card_fin]

private theorem theorem7Padded_card_univ_erase_zero (r : ℕ) :
    ((Finset.univ : Finset (Theorem7PaddedAgent r)).erase 0).card = r + 2 := by
  rw [Finset.card_erase_of_mem (by simp : (0 : Theorem7PaddedAgent r) ∈
    (Finset.univ : Finset (Theorem7PaddedAgent r)))]
  simp [Fintype.card_fin]

/--
In the padded family, woman `w₁`'s prime report misrepresents her `(r + 2)`nd
choice.
-/
theorem theorem7PaddedWoman0Prime_misrepresents_rank (r : ℕ) :
    paper_report_misrepresents_kth_choice
      (theorem7PaddedWomenProfile r (theorem7Core r 0))
      (theorem7PaddedWoman0PrimeReport r) (r + 2) := by
  refine ⟨theorem7Core r 2, ?_, ?_⟩
  · unfold paper_rank_of_choice
    have hfilter :
        ((Finset.univ : Finset (Theorem7PaddedAgent r)).filter fun b =>
          theorem7PaddedWomenProfile r (theorem7Core r 0) (theorem7Core r 2) <
            theorem7PaddedWomenProfile r (theorem7Core r 0) b) =
          ((Finset.univ : Finset (Theorem7PaddedAgent r)).erase 1).erase 2 := by
      ext b
      by_cases hb0 : b = (0 : Theorem7PaddedAgent r)
      · subst b
        simp [theorem7PaddedWomenProfile, theorem7PaddedWoman0TrueReport]
        norm_num
      · by_cases hb1 : b = (1 : Theorem7PaddedAgent r)
        · subst b
          simp [theorem7PaddedWomenProfile, theorem7PaddedWoman0TrueReport]
        · by_cases hb2 : b = (2 : Theorem7PaddedAgent r)
          · subst b
            simp [theorem7PaddedWomenProfile, theorem7PaddedWoman0TrueReport]
          · simp [theorem7PaddedWomenProfile, theorem7PaddedWoman0TrueReport,
              hb0, hb1, hb2]
            exact theorem7InterposedScore_gt_two r b
    rw [hfilter, theorem7Padded_card_univ_erase_one_erase_two]
  · have hrank :
        paper_rank_of_choice (theorem7PaddedWoman0PrimeReport r)
          (theorem7Core r 2) = r + 3 := by
      unfold paper_rank_of_choice
      have hfilter :
          ((Finset.univ : Finset (Theorem7PaddedAgent r)).filter fun b =>
            theorem7PaddedWoman0PrimeReport r (theorem7Core r 2) <
              theorem7PaddedWoman0PrimeReport r b) =
            (Finset.univ : Finset (Theorem7PaddedAgent r)).erase 2 := by
        ext b
        by_cases hb0 : b = (0 : Theorem7PaddedAgent r)
        · subst b
          simp [theorem7PaddedWoman0PrimeReport]
        · by_cases hb1 : b = (1 : Theorem7PaddedAgent r)
          · subst b
            simp [theorem7PaddedWoman0PrimeReport]
          · by_cases hb2 : b = (2 : Theorem7PaddedAgent r)
            · subst b
              simp [theorem7PaddedWoman0PrimeReport]
            · simp [theorem7PaddedWoman0PrimeReport, hb0, hb1, hb2]
              exact lt_trans (by norm_num : (1 : ℝ) < 2)
                (theorem7InterposedScore_gt_two r b)
      rw [hfilter, theorem7Padded_card_univ_erase_two]
    rw [hrank]
    omega

/--
In the padded family, man `m₁`'s double-prime report misrepresents his
`(r + 2)`nd choice.
-/
theorem theorem7PaddedMan0DoublePrime_misrepresents_rank (r : ℕ) :
    paper_report_misrepresents_kth_choice
      (theorem7PaddedMenProfile r (theorem7Core r 0))
      (theorem7PaddedMan0DoublePrimeReport r) (r + 2) := by
  refine ⟨theorem7Core r 0, ?_, ?_⟩
  · unfold paper_rank_of_choice
    have hfilter :
        ((Finset.univ : Finset (Theorem7PaddedAgent r)).filter fun b =>
          theorem7PaddedMenProfile r (theorem7Core r 0) (theorem7Core r 0) <
            theorem7PaddedMenProfile r (theorem7Core r 0) b) =
          ((Finset.univ : Finset (Theorem7PaddedAgent r)).erase 0).erase 2 := by
      ext b
      by_cases hb0 : b = (0 : Theorem7PaddedAgent r)
      · subst b
        simp [theorem7PaddedMenProfile, theorem7PaddedMan0TrueReport]
      · by_cases hb1 : b = (1 : Theorem7PaddedAgent r)
        · subst b
          simp [theorem7PaddedMenProfile, theorem7PaddedMan0TrueReport]
          norm_num
        · by_cases hb2 : b = (2 : Theorem7PaddedAgent r)
          · subst b
            simp [theorem7PaddedMenProfile, theorem7PaddedMan0TrueReport]
          · simp [theorem7PaddedMenProfile, theorem7PaddedMan0TrueReport,
              hb0, hb1, hb2]
            exact theorem7InterposedScore_gt_two r b
    rw [hfilter, theorem7Padded_card_univ_erase_zero_erase_two]
  · have hrank :
        paper_rank_of_choice (theorem7PaddedMan0DoublePrimeReport r)
          (theorem7Core r 0) = r + 3 := by
      unfold paper_rank_of_choice
      have hfilter :
          ((Finset.univ : Finset (Theorem7PaddedAgent r)).filter fun b =>
            theorem7PaddedMan0DoublePrimeReport r (theorem7Core r 0) <
              theorem7PaddedMan0DoublePrimeReport r b) =
            (Finset.univ : Finset (Theorem7PaddedAgent r)).erase 0 := by
        ext b
        by_cases hb0 : b = (0 : Theorem7PaddedAgent r)
        · subst b
          simp [theorem7PaddedMan0DoublePrimeReport]
        · by_cases hb1 : b = (1 : Theorem7PaddedAgent r)
          · subst b
            simp [theorem7PaddedMan0DoublePrimeReport]
          · by_cases hb2 : b = (2 : Theorem7PaddedAgent r)
            · subst b
              simp [theorem7PaddedMan0DoublePrimeReport]
            · simp [theorem7PaddedMan0DoublePrimeReport, hb0, hb1, hb2]
              exact lt_trans (by norm_num : (1 : ℝ) < 2)
                (theorem7InterposedScore_gt_two r b)
      rw [hfilter, theorem7Padded_card_univ_erase_zero]
    rw [hrank]
    omega

/--
The padded Theorem 3 family gives a profitable `(r + 2)`nd-choice
misrepresentation for every stable procedure.
-/
theorem theorem7Padded_counterexample_has_profitable_rank_misreport
    (r : ℕ)
    (mechanism :
      (Theorem7PaddedAgent r → Theorem7PaddedAgent r → ℝ) →
        (Theorem7PaddedAgent r → Theorem7PaddedAgent r → ℝ) →
          Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r))
    (hstableProc : paper_stable_matching_procedure mechanism) :
    paper_stable_procedure_has_profitable_kth_choice_misreport (r + 2) mechanism := by
  let muBase := mechanism (theorem7PaddedMenProfile r) (theorem7PaddedWomenProfile r)
  let muWomanPrime := mechanism (theorem7PaddedMenProfile r) (theorem7PaddedWomenProfilePrime r)
  let muManDoublePrime := mechanism (theorem7PaddedMenProfileDoublePrime r)
    (theorem7PaddedWomenProfile r)
  have hbase :
      theorem7RestrictAssignment r muBase = theorem3OutcomeX ∨
        theorem7RestrictAssignment r muBase = theorem3OutcomeY := by
    exact theorem3_stable_base_eq_x_or_y
      (theorem7RestrictAssignment r muBase)
      (theorem7Padded_restrict_stable_base
        (mu := muBase)
        (hstableProc (theorem7PaddedMenProfile r) (theorem7PaddedWomenProfile r)))
  have hwomanPrime :
      theorem7RestrictAssignment r muWomanPrime = theorem3OutcomeY := by
    exact theorem3_stable_woman_prime_eq_y
      (theorem7RestrictAssignment r muWomanPrime)
      (theorem7Padded_restrict_stable_woman_prime
        (mu := muWomanPrime)
        (hstableProc (theorem7PaddedMenProfile r) (theorem7PaddedWomenProfilePrime r)))
  have hmanDoublePrime :
      theorem7RestrictAssignment r muManDoublePrime = theorem3OutcomeX := by
    exact theorem3_stable_man_double_prime_eq_x
      (theorem7RestrictAssignment r muManDoublePrime)
      (theorem7Padded_restrict_stable_man_double_prime
        (mu := muManDoublePrime)
        (hstableProc (theorem7PaddedMenProfileDoublePrime r) (theorem7PaddedWomenProfile r)))
  refine ⟨theorem7PaddedMenProfile r, theorem7PaddedWomenProfile r, ?_⟩
  rcases hbase with hbaseX | hbaseY
  · right
    refine ⟨theorem7Core r 0, theorem7PaddedWoman0PrimeReport r,
      theorem7PaddedWoman0Prime_misrepresents_rank r, ?_⟩
    unfold paper_profitable_woman_misreport
    have hupdate :
        Function.update (theorem7PaddedWomenProfile r) (theorem7Core r 0)
            (theorem7PaddedWoman0PrimeReport r) =
          theorem7PaddedWomenProfilePrime r := by
      ext w m
      simp [theorem7PaddedWomenProfilePrime]
    have hbaseCore :
        (theorem7RestrictAssignment r muBase).w_match 0 = some 2 := by
      rw [hbaseX]
      simp [theorem3OutcomeX]
    have hbaseW :
        muBase.w_match (theorem7Core r 0) = some (theorem7Core r 2) :=
      theorem7Restrict_w_match_eq_some hbaseCore
    have hprimeCore :
        (theorem7RestrictAssignment r muWomanPrime).w_match 0 = some 0 := by
      rw [hwomanPrime]
      simp [theorem3OutcomeY]
    have hprimeW :
        muWomanPrime.w_match (theorem7Core r 0) = some (theorem7Core r 0) :=
      theorem7Restrict_w_match_eq_some hprimeCore
    change
      paper_matching_valW (theorem7PaddedWomenProfile r) (theorem7Core r 0)
          (muBase.w_match (theorem7Core r 0)) <
        paper_matching_valW (theorem7PaddedWomenProfile r) (theorem7Core r 0)
          ((mechanism (theorem7PaddedMenProfile r)
            (Function.update (theorem7PaddedWomenProfile r) (theorem7Core r 0)
              (theorem7PaddedWoman0PrimeReport r))).w_match (theorem7Core r 0))
    rw [hupdate]
    change
      paper_matching_valW (theorem7PaddedWomenProfile r) (theorem7Core r 0)
          (muBase.w_match (theorem7Core r 0)) <
        paper_matching_valW (theorem7PaddedWomenProfile r) (theorem7Core r 0)
          (muWomanPrime.w_match (theorem7Core r 0))
    rw [hbaseW, hprimeW]
    norm_num [paper_matching_valW, theorem7PaddedWomenProfile,
      theorem7PaddedWoman0TrueReport]
  · left
    refine ⟨theorem7Core r 0, theorem7PaddedMan0DoublePrimeReport r,
      theorem7PaddedMan0DoublePrime_misrepresents_rank r, ?_⟩
    unfold paper_profitable_man_misreport
    have hupdate :
        Function.update (theorem7PaddedMenProfile r) (theorem7Core r 0)
            (theorem7PaddedMan0DoublePrimeReport r) =
          theorem7PaddedMenProfileDoublePrime r := by
      ext m w
      simp [theorem7PaddedMenProfileDoublePrime]
    have hbaseCore :
        (theorem7RestrictAssignment r muBase).m_match 0 = some 0 := by
      rw [hbaseY]
      simp [theorem3OutcomeY]
    have hbaseM :
        muBase.m_match (theorem7Core r 0) = some (theorem7Core r 0) :=
      theorem7Restrict_m_match_eq_some hbaseCore
    have hdoubleCore :
        (theorem7RestrictAssignment r muManDoublePrime).m_match 0 = some 1 := by
      rw [hmanDoublePrime]
      simp [theorem3OutcomeX]
    have hdoubleM :
        muManDoublePrime.m_match (theorem7Core r 0) = some (theorem7Core r 1) :=
      theorem7Restrict_m_match_eq_some hdoubleCore
    change
      paper_matching_valM (theorem7PaddedMenProfile r) (theorem7Core r 0)
          (muBase.m_match (theorem7Core r 0)) <
        paper_matching_valM (theorem7PaddedMenProfile r) (theorem7Core r 0)
          ((mechanism
            (Function.update (theorem7PaddedMenProfile r) (theorem7Core r 0)
              (theorem7PaddedMan0DoublePrimeReport r))
            (theorem7PaddedWomenProfile r)).m_match (theorem7Core r 0))
    rw [hupdate]
    change
      paper_matching_valM (theorem7PaddedMenProfile r) (theorem7Core r 0)
          (muBase.m_match (theorem7Core r 0)) <
        paper_matching_valM (theorem7PaddedMenProfile r) (theorem7Core r 0)
          (muManDoublePrime.m_match (theorem7Core r 0))
    rw [hbaseM, hdoubleM]
    norm_num [paper_matching_valM, theorem7PaddedMenProfile,
      theorem7PaddedMan0TrueReport]

/--
Complete strict-marriage version of the padded Theorem 7 family: the true
profile and the unilateral reported profile are both legal source profiles.
-/
theorem theorem7Padded_counterexample_has_profitable_strict_rank_misreport
    (r : ℕ)
    (mechanism :
      (Theorem7PaddedAgent r → Theorem7PaddedAgent r → ℝ) →
        (Theorem7PaddedAgent r → Theorem7PaddedAgent r → ℝ) →
          Assignment (Theorem7PaddedAgent r) (Theorem7PaddedAgent r))
    (hstableProc : paper_stable_matching_procedure_on_strict_marriage_domain mechanism) :
    paper_stable_procedure_has_profitable_strict_kth_choice_misreport
      (r + 2) mechanism := by
  let muBase := mechanism (theorem7PaddedMenProfile r) (theorem7PaddedWomenProfile r)
  let muWomanPrime := mechanism (theorem7PaddedMenProfile r) (theorem7PaddedWomenProfilePrime r)
  let muManDoublePrime := mechanism (theorem7PaddedMenProfileDoublePrime r)
    (theorem7PaddedWomenProfile r)
  have hbase :
      theorem7RestrictAssignment r muBase = theorem3OutcomeX ∨
        theorem7RestrictAssignment r muBase = theorem3OutcomeY := by
    exact theorem3_stable_base_eq_x_or_y
      (theorem7RestrictAssignment r muBase)
      (theorem7Padded_restrict_stable_base
        (mu := muBase)
        (hstableProc (theorem7PaddedMenProfile r) (theorem7PaddedWomenProfile r)
          (theorem7Padded_base_strict_marriage_domain r)))
  have hwomanPrime :
      theorem7RestrictAssignment r muWomanPrime = theorem3OutcomeY := by
    exact theorem3_stable_woman_prime_eq_y
      (theorem7RestrictAssignment r muWomanPrime)
      (theorem7Padded_restrict_stable_woman_prime
        (mu := muWomanPrime)
        (hstableProc (theorem7PaddedMenProfile r) (theorem7PaddedWomenProfilePrime r)
          (theorem7Padded_woman_prime_strict_marriage_domain r)))
  have hmanDoublePrime :
      theorem7RestrictAssignment r muManDoublePrime = theorem3OutcomeX := by
    exact theorem3_stable_man_double_prime_eq_x
      (theorem7RestrictAssignment r muManDoublePrime)
      (theorem7Padded_restrict_stable_man_double_prime
        (mu := muManDoublePrime)
        (hstableProc (theorem7PaddedMenProfileDoublePrime r) (theorem7PaddedWomenProfile r)
          (theorem7Padded_man_double_prime_strict_marriage_domain r)))
  refine ⟨theorem7PaddedMenProfile r, theorem7PaddedWomenProfile r,
    theorem7Padded_base_strict_marriage_domain r, ?_⟩
  rcases hbase with hbaseX | hbaseY
  · right
    refine ⟨theorem7Core r 0, theorem7PaddedWoman0PrimeReport r, ?_,
      theorem7PaddedWoman0Prime_misrepresents_rank r, ?_⟩
    · simpa [theorem7PaddedWomenProfilePrime] using
        theorem7Padded_woman_prime_strict_marriage_domain r
    · unfold paper_profitable_woman_misreport
      have hupdate :
          Function.update (theorem7PaddedWomenProfile r) (theorem7Core r 0)
              (theorem7PaddedWoman0PrimeReport r) =
            theorem7PaddedWomenProfilePrime r := by
        ext w m
        simp [theorem7PaddedWomenProfilePrime]
      have hbaseCore :
          (theorem7RestrictAssignment r muBase).w_match 0 = some 2 := by
        rw [hbaseX]
        simp [theorem3OutcomeX]
      have hbaseW :
          muBase.w_match (theorem7Core r 0) = some (theorem7Core r 2) :=
        theorem7Restrict_w_match_eq_some hbaseCore
      have hprimeCore :
          (theorem7RestrictAssignment r muWomanPrime).w_match 0 = some 0 := by
        rw [hwomanPrime]
        simp [theorem3OutcomeY]
      have hprimeW :
          muWomanPrime.w_match (theorem7Core r 0) = some (theorem7Core r 0) :=
        theorem7Restrict_w_match_eq_some hprimeCore
      change
        paper_matching_valW (theorem7PaddedWomenProfile r) (theorem7Core r 0)
            (muBase.w_match (theorem7Core r 0)) <
          paper_matching_valW (theorem7PaddedWomenProfile r) (theorem7Core r 0)
            ((mechanism (theorem7PaddedMenProfile r)
              (Function.update (theorem7PaddedWomenProfile r) (theorem7Core r 0)
                (theorem7PaddedWoman0PrimeReport r))).w_match (theorem7Core r 0))
      rw [hupdate]
      change
        paper_matching_valW (theorem7PaddedWomenProfile r) (theorem7Core r 0)
            (muBase.w_match (theorem7Core r 0)) <
          paper_matching_valW (theorem7PaddedWomenProfile r) (theorem7Core r 0)
            (muWomanPrime.w_match (theorem7Core r 0))
      rw [hbaseW, hprimeW]
      norm_num [paper_matching_valW, theorem7PaddedWomenProfile,
        theorem7PaddedWoman0TrueReport]
  · left
    refine ⟨theorem7Core r 0, theorem7PaddedMan0DoublePrimeReport r, ?_,
      theorem7PaddedMan0DoublePrime_misrepresents_rank r, ?_⟩
    · simpa [theorem7PaddedMenProfileDoublePrime] using
        theorem7Padded_man_double_prime_strict_marriage_domain r
    · unfold paper_profitable_man_misreport
      have hupdate :
          Function.update (theorem7PaddedMenProfile r) (theorem7Core r 0)
              (theorem7PaddedMan0DoublePrimeReport r) =
            theorem7PaddedMenProfileDoublePrime r := by
        ext m w
        simp [theorem7PaddedMenProfileDoublePrime]
      have hbaseCore :
          (theorem7RestrictAssignment r muBase).m_match 0 = some 0 := by
        rw [hbaseY]
        simp [theorem3OutcomeY]
      have hbaseM :
          muBase.m_match (theorem7Core r 0) = some (theorem7Core r 0) :=
        theorem7Restrict_m_match_eq_some hbaseCore
      have hdoubleCore :
          (theorem7RestrictAssignment r muManDoublePrime).m_match 0 = some 1 := by
        rw [hmanDoublePrime]
        simp [theorem3OutcomeX]
      have hdoubleM :
          muManDoublePrime.m_match (theorem7Core r 0) = some (theorem7Core r 1) :=
        theorem7Restrict_m_match_eq_some hdoubleCore
      change
        paper_matching_valM (theorem7PaddedMenProfile r) (theorem7Core r 0)
            (muBase.m_match (theorem7Core r 0)) <
          paper_matching_valM (theorem7PaddedMenProfile r) (theorem7Core r 0)
            ((mechanism
              (Function.update (theorem7PaddedMenProfile r) (theorem7Core r 0)
                (theorem7PaddedMan0DoublePrimeReport r))
              (theorem7PaddedWomenProfile r)).m_match (theorem7Core r 0))
      rw [hupdate]
      change
        paper_matching_valM (theorem7PaddedMenProfile r) (theorem7Core r 0)
            (muBase.m_match (theorem7Core r 0)) <
          paper_matching_valM (theorem7PaddedMenProfile r) (theorem7Core r 0)
            (muManDoublePrime.m_match (theorem7Core r 0))
      rw [hbaseM, hdoubleM]
      norm_num [paper_matching_valM, theorem7PaddedMenProfile,
        theorem7PaddedMan0TrueReport]

/--
In Roth's finite counterexample, woman `w₁`'s report keeps her first choice but
swaps her true second and third choices.
-/
def theorem3Woman0PrimeIsSecondChoiceMisreport : Prop :=
  theorem3WomenProfile 0 0 > theorem3WomenProfile 0 2 ∧
    theorem3WomenProfile 0 2 > theorem3WomenProfile 0 1 ∧
    theorem3Woman0PrimeReport 0 > theorem3Woman0PrimeReport 1 ∧
    theorem3Woman0PrimeReport 1 > theorem3Woman0PrimeReport 2

/-- The woman-side Theorem 3 report misrepresents the second choice in rank form. -/
theorem theorem3Woman0Prime_misrepresents_second_choice_rank :
    paper_report_misrepresents_kth_choice (theorem3WomenProfile 0)
      theorem3Woman0PrimeReport 2 := by
  refine ⟨2, ?_, ?_⟩
  · unfold paper_rank_of_choice
    have hfilter :
        ((Finset.univ : Finset Theorem3Agent).filter fun b =>
          theorem3WomenProfile 0 2 < theorem3WomenProfile 0 b) =
          ({0} : Finset Theorem3Agent) := by
      ext b
      fin_cases b
      · norm_num [theorem3WomenProfile]
      · simp [theorem3WomenProfile]
      · simp [theorem3WomenProfile]
    rw [hfilter]
    norm_num
  · have hrank :
        paper_rank_of_choice theorem3Woman0PrimeReport 2 = 3 := by
      unfold paper_rank_of_choice
      have hfilter :
          ((Finset.univ : Finset Theorem3Agent).filter fun b =>
            theorem3Woman0PrimeReport 2 < theorem3Woman0PrimeReport b) =
            ({0, 1} : Finset Theorem3Agent) := by
        ext b
        fin_cases b <;> simp [theorem3Woman0PrimeReport]
      rw [hfilter]
      decide
    rw [hrank]
    norm_num

/-- The woman-side Theorem 3 report is a second-choice misrepresentation. -/
theorem theorem3Woman0Prime_second_choice_misreport :
    theorem3Woman0PrimeIsSecondChoiceMisreport := by
  norm_num [theorem3Woman0PrimeIsSecondChoiceMisreport, theorem3WomenProfile,
    theorem3Woman0PrimeReport]

/-- The woman-side Theorem 3 report also misrepresents the third choice in rank form. -/
theorem theorem3Woman0Prime_misrepresents_third_choice_rank :
    paper_report_misrepresents_kth_choice (theorem3WomenProfile 0)
      theorem3Woman0PrimeReport 3 := by
  refine ⟨1, ?_, ?_⟩
  · unfold paper_rank_of_choice
    have hfilter :
        ((Finset.univ : Finset Theorem3Agent).filter fun b =>
          theorem3WomenProfile 0 1 < theorem3WomenProfile 0 b) =
          (Finset.univ.erase (1 : Theorem3Agent)) := by
      ext b
      fin_cases b <;> simp [theorem3WomenProfile]
    rw [hfilter]
    simp
  · have hrank :
        paper_rank_of_choice theorem3Woman0PrimeReport 1 = 2 := by
      unfold paper_rank_of_choice
      have hfilter :
          ((Finset.univ : Finset Theorem3Agent).filter fun b =>
            theorem3Woman0PrimeReport 1 < theorem3Woman0PrimeReport b) =
            ({0} : Finset Theorem3Agent) := by
        ext b
        fin_cases b
        · norm_num [theorem3Woman0PrimeReport]
        · simp [theorem3Woman0PrimeReport]
        · simp [theorem3Woman0PrimeReport]
      rw [hfilter]
      norm_num
    rw [hrank]
    norm_num

/--
In Roth's finite counterexample, man `m₁`'s report keeps his first choice but
swaps his true second and third choices.
-/
def theorem3Man0DoublePrimeIsSecondChoiceMisreport : Prop :=
  theorem3MenProfile 0 1 > theorem3MenProfile 0 0 ∧
    theorem3MenProfile 0 0 > theorem3MenProfile 0 2 ∧
    theorem3Man0DoublePrimeReport 1 > theorem3Man0DoublePrimeReport 2 ∧
    theorem3Man0DoublePrimeReport 2 > theorem3Man0DoublePrimeReport 0

/-- The man-side Theorem 3 report misrepresents the second choice in rank form. -/
theorem theorem3Man0DoublePrime_misrepresents_second_choice_rank :
    paper_report_misrepresents_kth_choice (theorem3MenProfile 0)
      theorem3Man0DoublePrimeReport 2 := by
  refine ⟨0, ?_, ?_⟩
  · unfold paper_rank_of_choice
    have hfilter :
        ((Finset.univ : Finset Theorem3Agent).filter fun b =>
          theorem3MenProfile 0 0 < theorem3MenProfile 0 b) =
          ({1} : Finset Theorem3Agent) := by
      ext b
      fin_cases b
      · simp [theorem3MenProfile]
      · norm_num [theorem3MenProfile]
      · simp [theorem3MenProfile]
    rw [hfilter]
    norm_num
  · have hrank :
        paper_rank_of_choice theorem3Man0DoublePrimeReport 0 = 3 := by
      unfold paper_rank_of_choice
      have hfilter :
          ((Finset.univ : Finset Theorem3Agent).filter fun b =>
            theorem3Man0DoublePrimeReport 0 < theorem3Man0DoublePrimeReport b) =
            ({1, 2} : Finset Theorem3Agent) := by
        ext b
        fin_cases b <;> simp [theorem3Man0DoublePrimeReport]
      rw [hfilter]
      decide
    rw [hrank]
    norm_num

/-- The man-side Theorem 3 report is a second-choice misrepresentation. -/
theorem theorem3Man0DoublePrime_second_choice_misreport :
    theorem3Man0DoublePrimeIsSecondChoiceMisreport := by
  norm_num [theorem3Man0DoublePrimeIsSecondChoiceMisreport, theorem3MenProfile,
    theorem3Man0DoublePrimeReport]

/--
The man-side Theorem 3 report also misrepresents the third choice in rank form.
-/
theorem theorem3Man0DoublePrime_misrepresents_third_choice_rank :
    paper_report_misrepresents_kth_choice (theorem3MenProfile 0)
      theorem3Man0DoublePrimeReport 3 := by
  refine ⟨2, ?_, ?_⟩
  · unfold paper_rank_of_choice
    have hfilter :
        ((Finset.univ : Finset Theorem3Agent).filter fun b =>
          theorem3MenProfile 0 2 < theorem3MenProfile 0 b) =
          (Finset.univ.erase (2 : Theorem3Agent)) := by
      ext b
      fin_cases b <;> simp [theorem3MenProfile]
    rw [hfilter]
    simp
  · have hrank :
        paper_rank_of_choice theorem3Man0DoublePrimeReport 2 = 2 := by
      unfold paper_rank_of_choice
      have hfilter :
          ((Finset.univ : Finset Theorem3Agent).filter fun b =>
            theorem3Man0DoublePrimeReport 2 < theorem3Man0DoublePrimeReport b) =
            ({1} : Finset Theorem3Agent) := by
        ext b
        fin_cases b
        · simp [theorem3Man0DoublePrimeReport]
        · norm_num [theorem3Man0DoublePrimeReport]
        · simp [theorem3Man0DoublePrimeReport]
      rw [hfilter]
      norm_num
    rw [hrank]
    norm_num

/--
Roth Theorem 7 finite witness (`k = 2` or `k = 3`): at the Theorem 3
counterexample domain, some agent has a profitable `k`th-choice
misrepresentation.

The full paper theorem states an arbitrary `k ≠ 1` family; this declaration
records the verified rank instances supplied directly by the Theorem 3 profile.
-/
def Theorem7RankManipulationCounterexample
    (k : ℕ)
    (mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent) : Prop :=
  (paper_report_misrepresents_kth_choice (theorem3WomenProfile 0)
      theorem3Woman0PrimeReport k ∧
    paper_profitable_woman_misreport mechanism theorem3MenProfile theorem3WomenProfile
      0 theorem3Woman0PrimeReport) ∨
  (paper_report_misrepresents_kth_choice (theorem3MenProfile 0)
      theorem3Man0DoublePrimeReport k ∧
    paper_profitable_man_misreport mechanism theorem3MenProfile theorem3WomenProfile
      0 theorem3Man0DoublePrimeReport)

/-- Backwards-compatible name for the verified `k = 2` Theorem 7 witness. -/
def Theorem7SecondChoiceManipulationCounterexample
    (mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent) : Prop :=
  Theorem7RankManipulationCounterexample 2 mechanism

/--
Theorem 7 (`k = 2` counterexample wrapper): any stable procedure on Roth's
three-by-three counterexample domain gives some agent a profitable second-choice
misrepresentation.
-/
theorem paper_roth82_theorem7_second_choice_counterexample
    (mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent)
    (hstableProc : paper_stable_matching_procedure mechanism) :
    Theorem7SecondChoiceManipulationCounterexample mechanism := by
  have hprofit := theorem3_counterexample_has_profitable_misreport mechanism
    (theorem3_counterexample_stable_behavior_of_stable_procedure
      mechanism hstableProc)
  rcases hprofit with hprofit | hprofit
  · exact Or.inl ⟨theorem3Woman0Prime_misrepresents_second_choice_rank, hprofit⟩
  · exact Or.inr ⟨theorem3Man0DoublePrime_misrepresents_second_choice_rank, hprofit⟩

/--
Theorem 7 (`k = 3` counterexample wrapper): the same finite counterexample also
forces a profitable third-choice misrepresentation.
-/
theorem paper_roth82_theorem7_third_choice_counterexample
    (mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent)
    (hstableProc : paper_stable_matching_procedure mechanism) :
    Theorem7RankManipulationCounterexample 3 mechanism := by
  have hprofit := theorem3_counterexample_has_profitable_misreport mechanism
    (theorem3_counterexample_stable_behavior_of_stable_procedure
      mechanism hstableProc)
  rcases hprofit with hprofit | hprofit
  · exact Or.inl ⟨theorem3Woman0Prime_misrepresents_third_choice_rank, hprofit⟩
  · exact Or.inr ⟨theorem3Man0DoublePrime_misrepresents_third_choice_rank, hprofit⟩

/--
Theorem 7 finite-rank wrapper: for the ranks generated inside Roth's
three-by-three counterexample (`k = 2` or `k = 3`), any stable procedure gives
some agent a profitable `k`th-choice misrepresentation.
-/
theorem paper_roth82_theorem7_second_or_third_choice_counterexample
    (k : ℕ)
    (mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent)
    (hstableProc : paper_stable_matching_procedure mechanism)
    (hk : k = 2 ∨ k = 3) :
    Theorem7RankManipulationCounterexample k mechanism := by
  rcases hk with rfl | rfl
  · exact paper_roth82_theorem7_second_choice_counterexample mechanism hstableProc
  · exact paper_roth82_theorem7_third_choice_counterexample mechanism hstableProc

/--
Theorem 7 compatibility finite-domain statement for the verified ranks: on
Roth's three-by-three counterexample domain, no stable procedure avoids
profitable `k`th-choice manipulation for `k = 2` or `k = 3`, without explicit
strict-profile hypotheses.
-/
theorem paper_roth82_theorem7_second_or_third_choice_source_statement
    (k : ℕ) (hk : k = 2 ∨ k = 3) :
    paper_no_stable_procedure_avoids_kth_choice_manipulation_on
      Theorem3Agent Theorem3Agent k := by
  intro mechanism hstableProc
  refine ⟨theorem3MenProfile, theorem3WomenProfile, ?_⟩
  have hcounter :=
    paper_roth82_theorem7_second_or_third_choice_counterexample
      k mechanism hstableProc hk
  rcases hcounter with hwoman | hman
  · right
    exact ⟨0, theorem3Woman0PrimeReport, hwoman.1, hwoman.2⟩
  · left
    exact ⟨0, theorem3Man0DoublePrimeReport, hman.1, hman.2⟩

/--
Theorem 7 verified-family wrapper: the arbitrary-family statement is closed for
the ranks supplied by the three-by-three counterexample, namely `k = 2` and
`k = 3`.
-/
theorem paper_roth82_theorem7_second_or_third_choice_family_statement
    (k : ℕ) (hk : k = 2 ∨ k = 3) :
    ∃ n : ℕ,
      paper_no_stable_procedure_avoids_kth_choice_manipulation_on
        (Fin n) (Fin n) k := by
  refine ⟨3, ?_⟩
  simpa [Theorem3Agent] using
    paper_roth82_theorem7_second_or_third_choice_source_statement k hk

/--
Compatibility Theorem 7 arbitrary-family statement: for every rank `k > 1`, a
padded Theorem 3 counterexample domain forces some profitable `k`th-choice
misrepresentation under any stable procedure, without explicit strict-profile
hypotheses.
-/
theorem paper_roth82_theorem7_arbitrary_k_family_statement :
    PaperTheorem7ArbitraryKFamilyCertificate := by
  intro k hk
  let r := k - 2
  refine ⟨r + 3, ?_⟩
  intro mechanism hstableProc
  have hr : r + 2 = k := by
    dsimp [r]
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hk)
  have hcounter :=
    theorem7Padded_counterexample_has_profitable_rank_misreport
      r mechanism hstableProc
  simpa [hr] using hcounter

/--
Theorem 7 arbitrary-family statement on strict profiles: for every rank `k > 1`,
a padded strict Theorem 3 counterexample domain forces some profitable
`k`th-choice misrepresentation under any procedure stable on strict profiles.
-/
theorem paper_roth82_theorem7_strict_arbitrary_k_family_statement :
    PaperTheorem7StrictArbitraryKFamilyCertificate := by
  intro k hk
  let r := k - 2
  refine ⟨r + 3, ?_⟩
  intro mechanism hstableProc
  have hr : r + 2 = k := by
    dsimp [r]
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hk)
  have hcounter :=
    theorem7Padded_counterexample_has_profitable_strict_rank_misreport
      r mechanism hstableProc
  simpa [hr] using hcounter

/--
Roth Theorem 7 compatibility arbitrary-`k` wrapper without explicit
strict-profile hypotheses.
-/
theorem paper_roth82_theorem7_arbitrary_k :
    ∀ k, 1 < k →
      ∃ n : ℕ,
        paper_no_stable_procedure_avoids_kth_choice_manipulation_on
          (Fin n) (Fin n) k :=
  paper_roth82_theorem7_arbitrary_k_family_statement

/--
Roth Theorem 7 on the source strict-preference domain.
-/
theorem paper_roth82_theorem7_arbitrary_k_on_strict_profiles :
    ∀ k, 1 < k →
      ∃ n : ℕ,
        paper_no_stable_procedure_avoids_strict_kth_choice_manipulation_on
          (Fin n) (Fin n) k :=
  paper_roth82_theorem7_strict_arbitrary_k_family_statement

/--
Theorem 7 arbitrary-`k` compatibility wrapper: Roth's full arbitrary family
follows from a construction certificate for every rank `k > 1`.
-/
theorem paper_roth82_theorem7_arbitrary_k_of_family_certificate
    (hcert : PaperTheorem7ArbitraryKFamilyCertificate) :
    ∀ k, 1 < k →
      ∃ n : ℕ,
        paper_no_stable_procedure_avoids_kth_choice_manipulation_on
          (Fin n) (Fin n) k := by
  exact hcert

/--
Theorem 7 arbitrary-`k` strict-profile compatibility wrapper.
-/
theorem paper_roth82_theorem7_arbitrary_k_of_strict_family_certificate
    (hcert : PaperTheorem7StrictArbitraryKFamilyCertificate) :
    ∀ k, 1 < k →
      ∃ n : ℕ,
        paper_no_stable_procedure_avoids_strict_kth_choice_manipulation_on
          (Fin n) (Fin n) k := by
  exact hcert


end Roth82StableMatching
