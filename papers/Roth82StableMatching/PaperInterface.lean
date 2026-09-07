import Roth82StableMatching.GeneralMatching
import Roth82StableMatching.Assumptions

/-!
# Paper Interface: Roth 1982 Stable Matching

This is the compact human-facing Lean surface for Roth's
*The Economics of Matching: Stability and Incentives*. It exposes the paper's
core definitions and direct named-result statements. The long deferred-
acceptance trace proofs, counterexample enumerations, compatibility wrappers,
and exhaustive proof-seam aliases live in `MainTheorems.lean` and
`PostPaperAudit.lean`.

The source's batched proposal stages and indexed serial-dictatorship procedure
are exposed below together with refinement theorems to the compact outcome
selectors used by the main proofs.
-/

namespace Roth82StableMatching
namespace PaperInterface

open AppliedModelingLib.Matching

universe u v

/-! ## Paper Definitions -/

/-- Roth preference profile `P`: strict ordinal reports by every agent on both sides. -/
def preferenceProfile (M : Type u) (W : Type v) : Type (max u v) :=
  { profile : (M → W → ℝ) × (W → M → ℝ) //
    (∀ m w w', profile.1 m w = profile.1 m w' → w = w') ∧
      (∀ w m m', profile.2 w m = profile.2 w m' → m = m') }

/--
Marriage-problem outcome: a complete one-to-one matching.
Source status: direct paper definition.
-/
def completeMarriageOutcome {M W : Type*} (mu : Assignment M W) : Prop :=
  (∀ m, ∃ w, mu.m_match m = some w) ∧
    (∀ w, ∃ m, mu.w_match w = some m)

/-- A source matching procedure maps every legal profile to a complete outcome. -/
def matchingProcedure (M : Type u) (W : Type v) : Type (max u v) :=
  preferenceProfile M W →
    { mu : Assignment M W // completeMarriageOutcome mu }

/--
Operational stability used by the reusable deferred-acceptance library:
individual rationality plus no blocking pair.  The exact source definition of
a stable *marriage outcome*, including completeness, is exposed separately as
`sourceStableMarriage` below.
-/
def stable {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  (∀ m, 0 ≤ (match mu.m_match m with
    | none => 0
    | some w => val_m m w)) ∧
    (∀ w, 0 ≤ (match mu.w_match w with
      | none => 0
      | some m => val_w w m)) ∧
      (∀ m w,
        (match mu.m_match m with
          | none => 0
          | some w' => val_m m w') < val_m m w →
        val_w w m ≤
          (match mu.w_match w with
            | none => 0
            | some m' => val_w w m'))

/-- A blocking pair in the exact prose sense used in Roth's Section 2. -/
def unstableMarriage {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  ∃ m w,
    (match mu.m_match m with
      | none => 0
      | some w' => val_m m w') < val_m m w ∧
    (match mu.w_match w with
      | none => 0
      | some m' => val_w w m') < val_w w m

/--
Roth's exact stable-marriage definition: a complete one-to-one outcome with
no man and woman who both strictly prefer one another to their partners.
-/
def sourceStableMarriage {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  completeMarriageOutcome mu ∧ ¬ unstableMarriage val_m val_w mu

/--
Strict marriage domain: each side has strict rankings over the opposite side,
and every potential pair is strictly preferred to being unmatched.
Source status: direct paper model condition.
-/
def strictMarriageDomain {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  (∀ m w w', val_m m w = val_m m w' → w = w') ∧
    (∀ w m m', val_w w m = val_w w m' → m = m') ∧
      (∀ m w, 0 < val_m m w) ∧
        (∀ w m, 0 < val_w w m)

/-- Roth's strict-preference condition, independent of the unmatched-option encoding. -/
def strictPreferenceProfile {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  (∀ m w w', val_m m w = val_m m w' → w = w') ∧
    (∀ w m m', val_w w m = val_w w m' → m = m')

/-- The source marriage model has balanced sides and strict preferences. -/
def sourceMarriageModel {M W : Type*} [Fintype M] [Fintype W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  Fintype.card M = Fintype.card W ∧ strictPreferenceProfile val_m val_w

/-! ## Exact source-definition specifications -/

def preferenceProfile_eq_source_definitionSpec : Prop :=
  ∀ (M : Type u) (W : Type v),
    preferenceProfile M W =
      { profile : (M → W → ℝ) × (W → M → ℝ) //
        (∀ m w w', profile.1 m w = profile.1 m w' → w = w') ∧
          (∀ w m m', profile.2 w m = profile.2 w m' → m = m') }

theorem preferenceProfile_eq_source_definition :
    preferenceProfile_eq_source_definitionSpec := by
  intro M W
  rfl

def matchingProcedure_eq_source_definitionSpec : Prop :=
  ∀ (M : Type u) (W : Type v),
    matchingProcedure M W =
      (preferenceProfile M W →
        { mu : Assignment M W // completeMarriageOutcome mu })

theorem matchingProcedure_eq_source_definition :
    matchingProcedure_eq_source_definitionSpec := by
  intro M W
  rfl

def strictPreferenceProfile_iff_source_definitionSpec : Prop :=
  ∀ {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    strictPreferenceProfile val_m val_w ↔
      (∀ m w w', val_m m w = val_m m w' → w = w') ∧
        (∀ w m m', val_w w m = val_w w m' → m = m')

theorem strictPreferenceProfile_iff_source_definition :
    strictPreferenceProfile_iff_source_definitionSpec := by
  intro M W val_m val_w
  rfl

def sourceMarriageModel_iff_source_definitionSpec : Prop :=
  ∀ {M W : Type*} [Fintype M] [Fintype W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    sourceMarriageModel val_m val_w ↔
      Fintype.card M = Fintype.card W ∧
        (∀ m w w', val_m m w = val_m m w' → w = w') ∧
          (∀ w m m', val_w w m = val_w w m' → m = m')

theorem sourceMarriageModel_iff_source_definition :
    sourceMarriageModel_iff_source_definitionSpec := by
  intro M W _ _ val_m val_w
  rfl

def completeMarriageOutcome_iff_source_definitionSpec : Prop :=
  ∀ {M W : Type*} (mu : Assignment M W),
    completeMarriageOutcome mu ↔
      (∀ m, ∃ w, mu.m_match m = some w) ∧
        (∀ w, ∃ m, mu.w_match w = some m)

theorem completeMarriageOutcome_iff_source_definition :
    completeMarriageOutcome_iff_source_definitionSpec := by
  intro M W mu
  rfl

def sourceStableMarriage_iff_source_definitionSpec : Prop :=
  ∀ {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W),
    sourceStableMarriage val_m val_w mu ↔
      completeMarriageOutcome mu ∧
        ¬ ∃ m w,
          (match mu.m_match m with
            | none => 0
            | some w' => val_m m w') < val_m m w ∧
          (match mu.w_match w with
            | none => 0
            | some m' => val_w w m') < val_w w m

theorem sourceStableMarriage_iff_source_definition :
    sourceStableMarriage_iff_source_definitionSpec := by
  intro M W val_m val_w mu
  rfl

/-- On the encoded complete domain, exact source stability implies operational stability. -/
theorem sourceStableMarriage_implies_operational
    {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W)
    (hdomain : strictMarriageDomain val_m val_w)
    (hstable : sourceStableMarriage val_m val_w mu) :
    stable val_m val_w mu := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    rcases hstable.1.1 m with ⟨w, hw⟩
    simp [hw, le_of_lt (hdomain.2.2.1 m w)]
  · intro w
    rcases hstable.1.2 w with ⟨m, hm⟩
    simp [hm, le_of_lt (hdomain.2.2.2 w m)]
  · intro m w hm
    by_contra hw
    apply hstable.2
    exact ⟨m, w, hm, lt_of_not_ge hw⟩

/-- A complete operationally stable outcome satisfies Roth's exact source definition. -/
theorem operational_and_complete_implies_sourceStableMarriage
    {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W)
    (hstable : stable val_m val_w mu)
    (hcomplete : completeMarriageOutcome mu) :
    sourceStableMarriage val_m val_w mu := by
  refine ⟨hcomplete, ?_⟩
  rintro ⟨m, w, hm, hw⟩
  exact (not_lt_of_ge (hstable.2.2 m w hm)) hw

/-- Operational stability is complete on Roth's balanced all-pairs-feasible domain. -/
theorem operationalStable_complete_on_strict_domain_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w)
    (hstable : stable val_m val_w mu) :
    completeMarriageOutcome mu := by
  have hstable' : IsStable val_m val_w mu := by
    refine ⟨hstable.1, hstable.2.1, ?_⟩
    intro m w hm hw
    exact (not_lt_of_ge (hstable.2.2 m w hm)) hw
  constructor
  · exact
      GS62CollegeAdmissions.stable_left_complete_of_card_le_all_pairs_acceptable
        val_m val_w mu (Nat.le_of_eq hcard)
          ⟨hdomain.2.2.1, hdomain.2.2.2⟩ hstable'
  · exact
      GS62CollegeAdmissions.stable_right_complete_of_card_le_all_pairs_acceptable
        val_m val_w mu (Nat.le_of_eq hcard.symm)
          ⟨hdomain.2.2.1, hdomain.2.2.2⟩ hstable'

/--
The stable-outcome set `C(P)` for a reported preference profile.
Source status: direct paper definition.
-/
def stableOutcomes {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Set (Assignment M W) :=
  {mu | stable val_m val_w mu}

/--
A stable matching is men-optimal if every man weakly prefers it to any stable matching.
Source status: direct paper definition.
-/
def menOptimal {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  stable val_m val_w mu ∧
    ∀ mu', stable val_m val_w mu' →
      ∀ m, (match mu'.m_match m with
        | none => 0
        | some w => val_m m w) ≤
        (match mu.m_match m with
          | none => 0
          | some w => val_m m w)

/--
Women-optimal stable matching, with the symmetric weak-preference condition.
Source status: direct paper definition.
-/
def womenOptimal {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  stable val_m val_w mu ∧
    ∀ mu', stable val_m val_w mu' →
      ∀ w, (match mu'.w_match w with
        | none => 0
        | some m => val_w w m) ≤
        (match mu.w_match w with
          | none => 0
          | some m => val_w w m)

/-- Exact source-side optimality among complete stable marriage outcomes. -/
def sourceMenOptimal {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  sourceStableMarriage val_m val_w mu ∧
    ∀ mu', sourceStableMarriage val_m val_w mu' →
      ∀ m, (match mu'.m_match m with
        | none => 0
        | some w => val_m m w) ≤
        (match mu.m_match m with
          | none => 0
          | some w => val_m m w)

/-- Exact symmetric source-side optimality for women. -/
def sourceWomenOptimal {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  sourceStableMarriage val_m val_w mu ∧
    ∀ mu', sourceStableMarriage val_m val_w mu' →
      ∀ w, (match mu'.w_match w with
        | none => 0
        | some m => val_w w m) ≤
        (match mu.w_match w with
          | none => 0
          | some m => val_w w m)

def sideOptimalStableOutcome_iff_source_definitionSpec : Prop :=
  ∀ {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W),
    (sourceMenOptimal val_m val_w mu ↔
      sourceStableMarriage val_m val_w mu ∧
        ∀ mu', sourceStableMarriage val_m val_w mu' →
          ∀ m, (match mu'.m_match m with
            | none => 0
            | some w => val_m m w) ≤
            (match mu.m_match m with
              | none => 0
              | some w => val_m m w)) ∧
    (sourceWomenOptimal val_m val_w mu ↔
      sourceStableMarriage val_m val_w mu ∧
        ∀ mu', sourceStableMarriage val_m val_w mu' →
          ∀ w, (match mu'.w_match w with
            | none => 0
            | some m => val_w w m) ≤
            (match mu.w_match w with
              | none => 0
              | some m => val_w w m))

theorem sideOptimalStableOutcome_iff_source_definition :
    sideOptimalStableOutcome_iff_source_definitionSpec := by
  intro M W val_m val_w mu
  exact ⟨Iff.rfl, Iff.rfl⟩

/--
A woman is possible for a man if some stable outcome matches them.
Source status: direct proof definition used in Theorem 2.
-/
def possibleForMan {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M) (w : W) : Prop :=
  ∃ mu, stable val_m val_w mu ∧ mu.m_match m = some w

/--
Stable matching procedure on strict reported preference profiles.
Source status: direct paper definition on the strict marriage specialization.
-/
def stableMatchingProcedure {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ val_m val_w,
    strictMarriageDomain val_m val_w →
      stable val_m val_w (mechanism val_m val_w)

/-- Exact Section 4 stable-procedure definition on complete marriage outcomes. -/
def sourceStableMatchingProcedure {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ val_m val_w,
    strictMarriageDomain val_m val_w →
      sourceStableMarriage val_m val_w (mechanism val_m val_w)

/--
Truthful revelation is dominant for both sides on strict true and reported profiles.
Source status: direct paper definition on the strict marriage specialization.
-/
def truthfulForAllAgents {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  (∀ val_m val_w,
    strictMarriageDomain val_m val_w →
      ∀ m report_m,
        strictMarriageDomain (Function.update val_m m report_m) val_w →
            (match (mechanism (Function.update val_m m report_m) val_w).m_match m with
              | none => 0
              | some w => val_m m w) ≤
            (match (mechanism val_m val_w).m_match m with
              | none => 0
              | some w => val_m m w)) ∧
    (∀ val_m val_w,
      strictMarriageDomain val_m val_w →
        ∀ w report_w,
          strictMarriageDomain val_m (Function.update val_w w report_w) →
              (match (mechanism val_m (Function.update val_w w report_w)).w_match w with
                | none => 0
                | some m => val_w w m) ≤
              (match (mechanism val_m val_w).w_match w with
                | none => 0
                | some m => val_w w m))

def sourceStableMatchingProcedure_iff_source_definitionSpec : Prop :=
  ∀ {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W),
    sourceStableMatchingProcedure mechanism ↔
      ∀ val_m val_w,
        strictMarriageDomain val_m val_w →
          sourceStableMarriage val_m val_w (mechanism val_m val_w)

theorem sourceStableMatchingProcedure_iff_source_definition :
    sourceStableMatchingProcedure_iff_source_definitionSpec := by
  intro M W mechanism
  rfl

def truthfulForAllAgents_iff_source_definitionSpec : Prop :=
  ∀ {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W),
    truthfulForAllAgents mechanism ↔
      ((∀ val_m val_w,
        strictMarriageDomain val_m val_w →
          ∀ m report_m,
            strictMarriageDomain (Function.update val_m m report_m) val_w →
              (match (mechanism (Function.update val_m m report_m) val_w).m_match m with
                | none => 0
                | some w => val_m m w) ≤
              (match (mechanism val_m val_w).m_match m with
                | none => 0
                | some w => val_m m w)) ∧
        (∀ val_m val_w,
          strictMarriageDomain val_m val_w →
            ∀ w report_w,
              strictMarriageDomain val_m (Function.update val_w w report_w) →
                (match (mechanism val_m
                    (Function.update val_w w report_w)).w_match w with
                  | none => 0
                  | some m => val_w w m) ≤
                (match (mechanism val_m val_w).w_match w with
                  | none => 0
                  | some m => val_w w m)))

theorem truthfulForAllAgents_iff_source_definition :
    truthfulForAllAgents_iff_source_definitionSpec := by
  intro M W _ _ mechanism
  rfl

/--
Men-proposing deferred-acceptance outcome corresponding to Roth's `g(P)`.
Source status: direct outcome selector; `sourceBatchedMenDeferredAcceptance`
below is the source-stage runner and is proved to return this outcome.
-/
noncomputable def menDeferredAcceptance
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W :=
  deferredAcceptance val_m val_w

/--
Women-proposing deferred acceptance, represented on the original `(M, W)`
sides by reversing roles and swapping the resulting assignment back.
Source status: direct outcome selector, with the symmetric source-stage runner
and refinement theorem below.
-/
noncomputable def womenDeferredAcceptance
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W :=
  (deferredAcceptance (M := W) (W := M) val_w val_m).swap

/--
Roth's men-proposing `G(P)`: at each stage exactly the men rejected at the
start of the stage propose once. A man rejected during the stage waits until
the following stage.
Source status: direct algorithm formalization.
-/
noncomputable def sourceBatchedMenDeferredAcceptance
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W :=
  paper_batched_deferredAcceptance val_m val_w

/-- The finite source-stage run reaches a state with no active proposer. -/
theorem sourceBatchedMenDeferredAcceptance_terminates
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    ¬ ∃ m, IsActiveMan val_m
      (paper_batched_deferredAcceptanceState val_m val_w) m :=
  paper_batched_deferredAcceptanceState_terminated val_m val_w

/-- The source men-proposing stages terminate and refine `g(P)`. -/
theorem sourceBatchedMenDeferredAcceptance_refines
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w) :
    sourceBatchedMenDeferredAcceptance val_m val_w =
      menDeferredAcceptance val_m val_w := by
  exact paper_batched_deferredAcceptance_eq_deferredAcceptance
    val_m val_w hcard hdomain

/-- Women-proposing source stages, obtained by reversing the two sides. -/
noncomputable def sourceBatchedWomenDeferredAcceptance
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Assignment M W :=
  paper_women_batched_deferredAcceptance val_m val_w

/-- The source women-proposing stages refine the women-optimal selector. -/
theorem sourceBatchedWomenDeferredAcceptance_refines
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w) :
    sourceBatchedWomenDeferredAcceptance val_m val_w =
      womenDeferredAcceptance val_m val_w := by
  exact paper_women_batched_deferredAcceptance_eq_women_deferredAcceptance
    val_m val_w hcard hdomain

/--
Pareto-optimal complete matching among complete matchings.
Source status: direct paper definition.
-/
def paretoOptimal {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  completeMarriageOutcome mu ∧
    ¬ ∃ nu, completeMarriageOutcome nu ∧
      (∀ m, (match mu.m_match m with
          | none => 0
          | some w => val_m m w) ≤
        (match nu.m_match m with
          | none => 0
          | some w => val_m m w)) ∧
      (∀ w, (match mu.w_match w with
          | none => 0
          | some m => val_w w m) ≤
        (match nu.w_match w with
          | none => 0
          | some m => val_w w m)) ∧
      ((∃ m, (match mu.m_match m with
          | none => 0
          | some w => val_m m w) <
        (match nu.m_match m with
          | none => 0
          | some w => val_m m w)) ∨
      (∃ w, (match mu.w_match w with
          | none => 0
          | some m => val_w w m) <
        (match nu.w_match w with
          | none => 0
          | some m => val_w w m)))

/--
Efficient procedure: every legal complete strict reported preference profile
returns a Pareto-optimal matching. Source status: direct paper definition.
-/
def efficientMatchingProcedure {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) : Prop :=
  ∀ val_m val_w, strictMarriageDomain val_m val_w →
    paretoOptimal val_m val_w (mechanism val_m val_w)

def efficientMatchingProcedure_iff_source_definitionSpec : Prop :=
  ∀ {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W),
    efficientMatchingProcedure mechanism ↔
      ∀ val_m val_w, strictMarriageDomain val_m val_w →
        paretoOptimal val_m val_w (mechanism val_m val_w)

theorem efficientMatchingProcedure_iff_source_definition :
    efficientMatchingProcedure_iff_source_definitionSpec := by
  intro M W mechanism
  rfl

/--
The serial-dictatorship outcome selector constructed in Roth's Theorem 4 route.
Source status: direct outcome selector. The source's indexed remaining-woman
trace and its refinement to this selector are exposed immediately below.
-/
noncomputable def serialDictatorshipMechanism {n : ℕ} :
    (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) → Assignment (Fin n) (Fin n) :=
  paper_serial_dictatorship_mechanism (n := n)

/--
The serial-dictatorship mechanism chooses its permutation from the men's
reported preferences and matches each man to `p m` and each woman to `p.symm w`.
Source status: direct extensional outcome formula for the paper's construction;
it is not an executable-runner refinement.
-/
theorem serialDictatorshipMechanism_matches {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (val_w : Fin n → Fin n → ℝ)
    (m w : Fin n) :
    (serialDictatorshipMechanism val_m val_w).m_match m =
        some (paper_serial_dictatorship_perm val_m m) ∧
      (serialDictatorshipMechanism val_m val_w).w_match w =
        some ((paper_serial_dictatorship_perm val_m).symm w) := by
  exact ⟨rfl, rfl⟩

/-- Women remaining immediately before priority man `i` acts. -/
noncomputable def serialRemainingWomen {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (i : Fin n) : Finset (Fin n) :=
  paper_serial_dictatorship_remaining val_m i.val

/-- The woman selected by priority man `i`. -/
noncomputable def serialChoice {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (i : Fin n) : Fin n :=
  paper_serial_dictatorship_choice val_m i

/-- Each indexed man selects a best woman among those remaining. -/
theorem serialChoice_best_remaining {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (i : Fin n) (w : Fin n)
    (hw : w ∈ serialRemainingWomen val_m i) :
    val_m i w ≤ val_m i (serialChoice val_m i) :=
  paper_serial_dictatorship_choice_is_best_remaining val_m i w hw

/-- The selected woman is removed before the next indexed step. -/
theorem serialRemainingWomen_next {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (i : Fin n) :
    paper_serial_dictatorship_remaining val_m (i.val + 1) =
      (serialRemainingWomen val_m i).erase (serialChoice val_m i) :=
  paper_serial_dictatorship_remaining_succ val_m i

/-- The serial trace's choices are exactly the mechanism's matches. -/
theorem serialTrace_refines_mechanism {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (val_w : Fin n → Fin n → ℝ)
    (i : Fin n) :
    (serialDictatorshipMechanism val_m val_w).m_match i =
      some (serialChoice val_m i) := by
  rfl

/--
A simple report strictly ranks the obtained partner first.
Source status: direct paper definition used by Lemma 1.
-/
def manReportStrictlyRanksPartnerFirst {W : Type*} (report_m : W → ℝ)
    (wstar : W) : Prop :=
  ∀ w, w ≠ wstar → report_m w < report_m wstar

/--
A report changes the identity of some alternative that was truly ranked `k`.
Source status: direct paper definition
-/
def reportMisrepresentsKthChoice {A : Type*} [Fintype A] [DecidableEq A]
    (true_score report_score : A → ℝ) (k : ℕ) : Prop :=
  ∃ a,
    ((Finset.univ : Finset A).filter fun b => true_score a < true_score b).card + 1 = k ∧
      ((Finset.univ : Finset A).filter fun b => report_score a < report_score b).card + 1 ≠ k

/--
A man's misrepresentation is successful exactly when, under his true ranking,
the reported-profile outcome gives him a strictly preferred partner.
Source status: direct Section 5 definition.
-/
def successfulMisrepresentation {M W : Type*} [DecidableEq M]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W)
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (report_m : W → ℝ) : Prop :=
  (match (mechanism val_m val_w).m_match m with
    | none => 0
    | some w => val_m m w) <
  (match (mechanism (Function.update val_m m report_m) val_w).m_match m with
    | none => 0
    | some w => val_m m w)

def manReportStrictlyRanksPartnerFirst_iff_source_definitionSpec : Prop :=
  ∀ {W : Type*} (report_m : W → ℝ) (wstar : W),
    manReportStrictlyRanksPartnerFirst report_m wstar ↔
      ∀ w, w ≠ wstar → report_m w < report_m wstar

theorem manReportStrictlyRanksPartnerFirst_iff_source_definition :
    manReportStrictlyRanksPartnerFirst_iff_source_definitionSpec := by
  intro W report_m wstar
  rfl

def successfulMisrepresentation_iff_source_definitionSpec : Prop :=
  ∀ {M W : Type*} [DecidableEq M]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W)
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (report_m : W → ℝ),
    successfulMisrepresentation mechanism val_m val_w m report_m ↔
      (match (mechanism val_m val_w).m_match m with
        | none => 0
        | some w => val_m m w) <
      (match (mechanism (Function.update val_m m report_m) val_w).m_match m with
        | none => 0
        | some w => val_m m w)

theorem successfulMisrepresentation_iff_source_definition :
    successfulMisrepresentation_iff_source_definitionSpec := by
  intro M W _ mechanism val_m val_w m report_m
  rfl

/-! ## Proved source-definition formulas

The underlying predicates remain convenient implementation vocabulary.  The
paper-facing review surface uses these theorem-valued formulas so each source
definition is exposed as a proved equivalence or equality rather than receiving
proof credit merely from a `Prop`-valued declaration.
-/

/--
The complete-marriage predicate has exactly the paper's two-sided coverage formula.
Source status: proved formula for the direct Section 2 definition.
-/
theorem completeMarriageOutcome_formula {M W : Type*} (mu : Assignment M W) :
    completeMarriageOutcome mu ↔
      (∀ m, ∃ w, mu.m_match m = some w) ∧
        (∀ w, ∃ m, mu.w_match w = some m) := by
  rfl

/--
Stability is exactly acceptability plus absence of a strict blocking pair.
Source status: proved formula for the direct Section 2 definition.
-/
theorem stable_formula {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) :
    stable val_m val_w mu ↔
      (∀ m, 0 ≤ (match mu.m_match m with
        | none => 0
        | some w => val_m m w)) ∧
        (∀ w, 0 ≤ (match mu.w_match w with
          | none => 0
          | some m => val_w w m)) ∧
          (∀ m w,
            (match mu.m_match m with
              | none => 0
              | some w' => val_m m w') < val_m m w →
            val_w w m ≤
              (match mu.w_match w with
                | none => 0
                | some m' => val_w w m')) := by
  rfl

/--
The strict marriage domain is exactly strictness and acceptability on both sides.
Source status: proved formula for the direct Section 2 model condition.
-/
theorem strictMarriageDomain_formula {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    strictMarriageDomain val_m val_w ↔
      (∀ m w w', val_m m w = val_m m w' → w = w') ∧
        (∀ w m m', val_w w m = val_w w m' → m = m') ∧
          (∀ m w, 0 < val_m m w) ∧
            (∀ w m, 0 < val_w w m) := by
  rfl

/--
`C(P)` is exactly the set of outcomes satisfying the stability formula.
Source status: proved equality for the direct stable-outcome-set definition.
-/
theorem stableOutcomes_formula {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    stableOutcomes val_m val_w = {mu | stable val_m val_w mu} := by
  rfl

/--
Men-optimality is stability plus weak dominance over every stable outcome.
Source status: proved formula for the direct definition preceding Theorem 2.
-/
theorem menOptimal_formula {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) :
    menOptimal val_m val_w mu ↔
      stable val_m val_w mu ∧
        ∀ mu', stable val_m val_w mu' →
          ∀ m, (match mu'.m_match m with
            | none => 0
            | some w => val_m m w) ≤
            (match mu.m_match m with
              | none => 0
              | some w => val_m m w) := by
  rfl

/--
Women-optimality is the symmetric weak-dominance formula.
Source status: proved formula for the symmetric direct definition.
-/
theorem womenOptimal_formula {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) :
    womenOptimal val_m val_w mu ↔
      stable val_m val_w mu ∧
        ∀ mu', stable val_m val_w mu' →
          ∀ w, (match mu'.w_match w with
            | none => 0
            | some m => val_w w m) ≤
            (match mu.w_match w with
              | none => 0
              | some m => val_w w m) := by
  rfl

/--
A possible partner is exactly one realized by some stable outcome.
Source status: proved formula for the definition used in Theorem 2's proof.
-/
theorem possibleForMan_formula {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M) (w : W) :
    possibleForMan val_m val_w m w ↔
      ∃ mu, stable val_m val_w mu ∧ mu.m_match m = some w := by
  rfl

/--
A stable procedure returns a stable outcome at every strict reported profile.
Source status: proved formula for the direct Section 4 definition.
-/
theorem stableMatchingProcedure_formula {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) :
    stableMatchingProcedure mechanism ↔
      ∀ val_m val_w,
        strictMarriageDomain val_m val_w →
          stable val_m val_w (mechanism val_m val_w) := by
  rfl

/--
Dominant-strategy truthfulness is exactly the two unilateral-report inequalities.
Source status: proved formula for the direct Section 4 definition.
-/
theorem truthfulForAllAgents_formula {M W : Type*} [DecidableEq M] [DecidableEq W]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) :
    truthfulForAllAgents mechanism ↔
      (∀ val_m val_w,
        strictMarriageDomain val_m val_w →
          ∀ m report_m,
            strictMarriageDomain (Function.update val_m m report_m) val_w →
                (match (mechanism (Function.update val_m m report_m) val_w).m_match m with
                  | none => 0
                  | some w => val_m m w) ≤
                (match (mechanism val_m val_w).m_match m with
                  | none => 0
                  | some w => val_m m w)) ∧
        (∀ val_m val_w,
          strictMarriageDomain val_m val_w →
            ∀ w report_w,
              strictMarriageDomain val_m (Function.update val_w w report_w) →
                  (match (mechanism val_m (Function.update val_w w report_w)).w_match w with
                    | none => 0
                    | some m => val_w w m) ≤
                  (match (mechanism val_m val_w).w_match w with
                    | none => 0
                    | some m => val_w w m)) := by
  rfl

/--
Pareto optimality is exactly completeness plus absence of a Pareto improvement.
Source status: proved formula for the direct definition before Theorem 4.
-/
theorem paretoOptimal_formula {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) :
    paretoOptimal val_m val_w mu ↔
      completeMarriageOutcome mu ∧
        ¬ ∃ nu, completeMarriageOutcome nu ∧
          (∀ m, (match mu.m_match m with
              | none => 0
              | some w => val_m m w) ≤
            (match nu.m_match m with
              | none => 0
              | some w => val_m m w)) ∧
          (∀ w, (match mu.w_match w with
              | none => 0
              | some m => val_w w m) ≤
            (match nu.w_match w with
              | none => 0
              | some m => val_w w m)) ∧
          ((∃ m, (match mu.m_match m with
              | none => 0
              | some w => val_m m w) <
            (match nu.m_match m with
              | none => 0
              | some w => val_m m w)) ∨
          (∃ w, (match mu.w_match w with
              | none => 0
              | some m => val_w w m) <
            (match nu.w_match w with
              | none => 0
              | some m => val_w w m))) := by
  rfl

/--
Efficiency means that every legal complete strict reported profile returns a
Pareto-optimal outcome.
Source status: proved formula for the direct definition before Theorem 4.
-/
theorem efficientMatchingProcedure_formula {M W : Type*}
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W) :
    efficientMatchingProcedure mechanism ↔
      ∀ val_m val_w, strictMarriageDomain val_m val_w →
        paretoOptimal val_m val_w (mechanism val_m val_w) := by
  rfl

/--
A simple report ranks the obtained partner strictly above every alternative.
Source status: proved formula for the direct Section 5 simple-report definition.
-/
theorem manReportStrictlyRanksPartnerFirst_formula {W : Type*}
    (report_m : W → ℝ) (wstar : W) :
    manReportStrictlyRanksPartnerFirst report_m wstar ↔
      ∀ w, w ≠ wstar → report_m w < report_m wstar := by
  rfl

/--
Kth-choice misrepresentation is exactly the displayed rank-change formula.
Source status: proved formula for the direct Section 6 rank vocabulary.
-/
theorem reportMisrepresentsKthChoice_formula {A : Type*} [Fintype A] [DecidableEq A]
    (true_score report_score : A → ℝ) (k : ℕ) :
    reportMisrepresentsKthChoice true_score report_score k ↔
      ∃ a,
        ((Finset.univ : Finset A).filter fun b => true_score a < true_score b).card + 1 = k ∧
          ((Finset.univ : Finset A).filter fun b => report_score a < report_score b).card + 1 ≠ k := by
  rfl

/--
Successful misrepresentation is exactly strict true-value improvement.
Source status: proved formula for the direct Section 5 definition.
-/
theorem successfulMisrepresentation_formula {M W : Type*} [DecidableEq M]
    (mechanism : (M → W → ℝ) → (W → M → ℝ) → Assignment M W)
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (report_m : W → ℝ) :
    successfulMisrepresentation mechanism val_m val_w m report_m ↔
      (match (mechanism val_m val_w).m_match m with
        | none => 0
        | some w => val_m m w) <
      (match (mechanism (Function.update val_m m report_m) val_w).m_match m with
        | none => 0
        | some w => val_m m w) := by
  rfl

/-! ## General quotas and dummy agents -/

/--
An outcome in Roth's broad general matching model: each agent has a set of
partners, and the two side views agree on every pair.
-/
structure ManyToManyQuotaAssignment (M W : Type*) where
  partnersM : M → Set W
  partnersW : W → Set M
  consistent : ∀ m w, w ∈ partnersM m ↔ m ∈ partnersW w

/-- Every agent receives a finite set containing exactly that agent's quota of partners. -/
def fillsIndividualQuotas {M W : Type*}
    (quotaM : M → ℕ) (quotaW : W → ℕ)
    (mu : ManyToManyQuotaAssignment M W) : Prop :=
  (∀ m, (mu.partnersM m).Finite ∧ (mu.partnersM m).ncard = quotaM m) ∧
    ∀ w, (mu.partnersW w).Finite ∧ (mu.partnersW w).ncard = quotaW w

def fillsIndividualQuotas_iff_source_definitionSpec : Prop :=
  ∀ {M W : Type*} (quotaM : M → ℕ) (quotaW : W → ℕ)
    (mu : ManyToManyQuotaAssignment M W),
    fillsIndividualQuotas quotaM quotaW mu ↔
      (∀ m, (mu.partnersM m).Finite ∧ (mu.partnersM m).ncard = quotaM m) ∧
        ∀ w, (mu.partnersW w).Finite ∧ (mu.partnersW w).ncard = quotaW w

theorem fillsIndividualQuotas_iff_source_definition :
    fillsIndividualQuotas_iff_source_definitionSpec := by
  intro M W quotaM quotaW mu
  rfl

/-- Responsive arbitrary-quota individual/institution assignments. -/
abbrev quotaAssignment (Applicants Colleges : Type*) :=
  GeneralQuota.QuotaAssignment Applicants Colleges

/-- Strict responsive preference domain for the source's quota extension. -/
def strictQuotaDomain {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ) : Prop :=
  GeneralQuota.strictDomain val_applicant val_college

/-- Source stability for a feasible arbitrary-quota assignment. -/
def stableQuotaAssignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : quotaAssignment Applicants Colleges) : Prop :=
  GeneralQuota.stable quota val_applicant val_college mu

/-- Applicant-optimality among all stable assignments in the quota market. -/
def applicantOptimalQuotaAssignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : quotaAssignment Applicants Colleges) : Prop :=
  GeneralQuota.applicantOptimal quota val_applicant val_college mu

/-- Roth's full-quota batched waiting-list outcome. -/
noncomputable def quotaBatchedDeferredAcceptance
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictQuotaDomain val_applicant val_college) :
    quotaAssignment Applicants Colleges :=
  GeneralQuota.batchedApplicantOutcome quota val_applicant val_college hdomain

/--
The quota footnote's top-`q` waiting-list runner refines cloned-seat DA.
Source status: direct algorithm-semantics theorem.
-/
theorem quotaBatchedDeferredAcceptance_refines_applicant_da
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictQuotaDomain val_applicant val_college) :
    quotaBatchedDeferredAcceptance quota val_applicant val_college hdomain =
      GS62CollegeAdmissions.ManyToOneOptimality.refinedDeferredAcceptanceManyToOne
        quota val_applicant val_college hdomain.1.2 :=
  GeneralQuota.batchedApplicantOutcome_refines_applicant_da
    quota val_applicant val_college hdomain

/--
Theorems 1 and 2 for arbitrary institution quotas: the source batched outcome
is stable and applicant-optimal, while the inverted procedure gives the unique
responsive institution-optimal stable assignment.
Source status: direct responsive quota specialization emphasized by Roth.
-/
theorem generalQuota_stable_and_both_side_optimal
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictQuotaDomain val_applicant val_college) :
    stableQuotaAssignment quota val_applicant val_college
        (quotaBatchedDeferredAcceptance quota val_applicant val_college hdomain) ∧
      applicantOptimalQuotaAssignment quota val_applicant val_college
        (quotaBatchedDeferredAcceptance quota val_applicant val_college hdomain) ∧
      ∃! mu : quotaAssignment Applicants Colleges,
        GS62CollegeAdmissions.ManyToOneOptimality.gs_college_optimal_college_assignment
            quota val_applicant val_college hdomain.1.2 mu ∧
          GS62CollegeAdmissions.ManyToOneOptimality.gs_responsive_college_optimal_assignment
            quota val_applicant val_college mu :=
  GeneralQuota.stable_and_both_side_optimal
    quota val_applicant val_college hdomain

/--
Every partial outcome becomes a complete balanced marriage after adding
personal dummy agents; real pairs and unmatched outcomes are preserved exactly.
Source status: direct dummy-agent representation.
-/
theorem dummyAgents_complete_optional_assignment {M W : Type*}
    [Fintype M] [Fintype W] (mu : Assignment M W) :
    Fintype.card (M ⊕ W) = Fintype.card (W ⊕ M) ∧
      ((∀ x, ∃ y, (paper_dummy_completion mu).m_match x = some y) ∧
        ∀ y, ∃ x, (paper_dummy_completion mu).w_match y = some x) ∧
      (∀ m w,
        (paper_dummy_completion mu).m_match (Sum.inl m) = some (Sum.inl w) ↔
          mu.m_match m = some w) ∧
      (∀ m,
        (paper_dummy_completion mu).m_match (Sum.inl m) = some (Sum.inr m) ↔
          mu.m_match m = none) ∧
      ∀ w,
        (paper_dummy_completion mu).w_match (Sum.inl w) = some (Sum.inr w) ↔
          mu.w_match w = none := by
  exact ⟨paper_dummy_completion_balanced,
    paper_dummy_completion_complete mu,
    paper_dummy_completion_real_pair_iff mu,
    paper_dummy_completion_man_dummy_iff mu,
    paper_dummy_completion_woman_dummy_iff mu⟩

/-! ## Source Theorems -/

/--
Theorem 1: on an equal-size strict marriage domain, a stable complete outcome
exists.
Source status: direct marriage theorem; the advertised quota result is exposed
separately by `generalQuota_stable_and_both_side_optimal`.
-/
theorem theorem1_stable_complete_outcome_exists_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w) :
    ∃ mu : Assignment M W, stable val_m val_w mu ∧ completeMarriageOutcome mu := by
  simpa [strictMarriageDomain, stable, completeMarriageOutcome,
    paper_strict_marriage_domain, paper_is_stable, paper_is_complete_matching,
    paper_matching_valM, paper_matching_valW] using
    paper_roth82_theorem1_stable_complete_outcome_exists_on_strict_marriage_domain
      val_m val_w hcard hdomain

/--
Theorem 2: men-optimal and women-optimal stable outcomes exist on the strict marriage domain.
Source status: direct marriage theorem, with the responsive arbitrary-quota
extension exposed above.
-/
theorem theorem2_optimal_stable_outcomes_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hdomain : strictMarriageDomain val_m val_w) :
    (∃ mu : Assignment M W, menOptimal val_m val_w mu) ∧
      (∃ nu : Assignment M W, womenOptimal val_m val_w nu) := by
  simpa [menOptimal, womenOptimal, stable, strictMarriageDomain,
    paper_is_men_optimal, paper_is_women_optimal, paper_is_stable,
    paper_matching_valM, paper_matching_valW, paper_strict_marriage_domain] using
    paper_roth82_theorem2_optimal_stable_outcomes_on_strict_marriage_domain
      val_m val_w hdomain

/--
Theorem 3: on Roth's strict 3-by-3 counterexample domain, no procedure stable
on strict profiles is truthful for both sides.
Source status: direct source counterexample sufficient for the paper's general impossibility.
-/
theorem theorem3_no_stable_truthful_procedure_on_strict_profiles :
    ¬ ∃ mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent,
      stableMatchingProcedure mechanism ∧ truthfulForAllAgents mechanism := by
  rintro ⟨mechanism, hstable, htruthful⟩
  rcases htruthful with ⟨hmenTruth, hwomenTruth⟩
  apply paper_roth82_theorem3_no_stable_truthful_procedure_on_strict_marriage_domain
  refine ⟨mechanism, ?_, ?_, ?_⟩
  · intro val_m val_w hdomain
    have hdomain' : strictMarriageDomain val_m val_w := by
      simpa [strictMarriageDomain, paper_strict_marriage_domain] using hdomain
    simpa [stable, paper_is_stable, paper_matching_valM, paper_matching_valW] using
      hstable val_m val_w hdomain'
  · intro val_m val_w hdomain m report_m hreport
    have hdomain' : strictMarriageDomain val_m val_w := by
      simpa [strictMarriageDomain, paper_strict_marriage_domain] using hdomain
    have hreport' :
        strictMarriageDomain (Function.update val_m m report_m) val_w := by
      simpa [strictMarriageDomain, paper_strict_marriage_domain] using hreport
    simpa [paper_matching_valM] using
      hmenTruth val_m val_w hdomain' m report_m hreport'
  · intro val_m val_w hdomain w report_w hreport
    have hdomain' : strictMarriageDomain val_m val_w := by
      simpa [strictMarriageDomain, paper_strict_marriage_domain] using hdomain
    have hreport' :
        strictMarriageDomain val_m (Function.update val_w w report_w) := by
      simpa [strictMarriageDomain, paper_strict_marriage_domain] using hreport
    simpa [paper_matching_valW] using
      hwomenTruth val_m val_w hdomain' w report_w hreport'

/--
Theorem 4: Roth's constructed serial-dictatorship procedure is efficient on
strict men-side profiles, truthful for men on that strict men-side domain, and
truthful for women.
Source status: direct mathematical theorem; the step-by-step procedure refinement is separate.
-/
theorem theorem4_serial_dictatorship_constructed {n : ℕ} :
    (∀ val_m val_w,
      (∀ m w w', val_m m w = val_m m w' → w = w') →
        paretoOptimal val_m val_w
          (serialDictatorshipMechanism (n := n) val_m val_w)) ∧
      (∀ val_m val_w,
        (∀ m w w', val_m m w = val_m m w' → w = w') →
          ∀ m report_m,
            (match (serialDictatorshipMechanism (n := n)
                (Function.update val_m m report_m) val_w).m_match m with
              | none => 0
              | some w => val_m m w) ≤
            (match (serialDictatorshipMechanism (n := n) val_m val_w).m_match m with
              | none => 0
              | some w => val_m m w)) ∧
      (∀ val_m val_w w report_w,
        (match (serialDictatorshipMechanism (n := n) val_m
            (Function.update val_w w report_w)).w_match w with
          | none => 0
          | some m => val_w w m) ≤
        (match (serialDictatorshipMechanism (n := n) val_m val_w).w_match w with
          | none => 0
          | some m => val_w w m)) := by
  simpa [serialDictatorshipMechanism, paretoOptimal, completeMarriageOutcome,
    paper_efficient_matching_procedure_on_strict_men,
    paper_truthful_for_men_on_strict_men, paper_truthful_for_women,
    paper_men_strict_preferences, paper_is_pareto_optimal,
    paper_pareto_improves, paper_pareto_dominates, paper_is_complete_matching,
    paper_matching_valM, paper_matching_valW] using
    paper_roth82_theorem4_serial_dictatorship_constructed (n := n)

/--
Theorem 5: side-optimal deferred-acceptance procedures are strategyproof on
equal-size strict marriage domains.
Source status: direct source proof domain. The source itself reduces the
incentive proof to marriage; the batched outcome equivalence is explicit above.
-/
theorem theorem5_optimal_side_truthful_on_strict_domain_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
      Fintype.card M = Fintype.card W →
        strictMarriageDomain val_m val_w →
          (∀ (m : M) (report_m : W → ℝ),
            (match (menDeferredAcceptance
                (Function.update val_m m report_m) val_w).m_match m with
              | none => 0
              | some w => val_m m w) ≤
            (match (menDeferredAcceptance val_m val_w).m_match m with
              | none => 0
              | some w => val_m m w)) ∧
          (∀ (w : W) (report_w : M → ℝ),
            (match (womenDeferredAcceptance val_m
                (Function.update val_w w report_w)).w_match w with
              | none => 0
              | some m => val_w w m) ≤
            (match (womenDeferredAcceptance val_m val_w).w_match w with
              | none => 0
              | some m => val_w w m)) := by
  simpa [strictMarriageDomain, menDeferredAcceptance, womenDeferredAcceptance,
    paper_women_deferredAcceptance, paper_strict_marriage_domain,
    paper_matching_valM, paper_matching_valW] using
    (paper_roth82_theorem5_optimal_side_truthful_on_strict_domain_of_card_eq
      (M := M) (W := W))

/--
Corollary 5.1: under each side-optimal DA procedure, the non-proposing side can
match any legal report's outcome with a legal report preserving its true first choice.
Source status: direct paper statement on the marriage proof domain used in
Section 5.
-/
theorem corollary5_1_no_need_to_misrepresent_first_choice
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M] [Nonempty W] :
    (∀ val_m val_w, strictMarriageDomain val_m val_w →
      ∀ (w : W) (report_w : M → ℝ),
        strictMarriageDomain val_m (Function.update val_w w report_w) →
        ∃ report_w' : M → ℝ,
          strictMarriageDomain val_m (Function.update val_w w report_w') ∧
          (∀ mstar, (∀ m, m ≠ mstar → val_w w m < val_w w mstar) →
            ∀ m, m ≠ mstar → report_w' m < report_w' mstar) ∧
          (match (menDeferredAcceptance val_m
              (Function.update val_w w report_w)).w_match w with
            | none => 0
            | some m => val_w w m) ≤
          (match (menDeferredAcceptance val_m
              (Function.update val_w w report_w')).w_match w with
            | none => 0
            | some m => val_w w m)) ∧
      (∀ val_m val_w, strictMarriageDomain val_m val_w →
        ∀ (m : M) (report_m : W → ℝ),
          strictMarriageDomain (Function.update val_m m report_m) val_w →
          ∃ report_m' : W → ℝ,
            strictMarriageDomain (Function.update val_m m report_m') val_w ∧
            (∀ wstar, (∀ w, w ≠ wstar → val_m m w < val_m m wstar) →
              ∀ w, w ≠ wstar → report_m' w < report_m' wstar) ∧
            (match (womenDeferredAcceptance
                (Function.update val_m m report_m) val_w).m_match m with
              | none => 0
              | some w => val_m m w) ≤
            (match (womenDeferredAcceptance
                (Function.update val_m m report_m') val_w).m_match m with
              | none => 0
              | some w => val_m m w)) := by
  constructor
  · simpa [menDeferredAcceptance, strictMarriageDomain,
      paper_no_need_to_misrepresent_first_choice_for_women_on_strict_domain,
      paper_woman_report_preserves_first_choice,
      paper_is_strict_top_choice_for_woman, paper_woman_weakly_prefers_outcome,
      paper_strict_marriage_domain, paper_matching_valW] using
      paper_roth82_corollary5_1_no_need_to_misrepresent_first_choice_on_strict_domain
        (M := M) (W := W)
  · simpa [womenDeferredAcceptance, strictMarriageDomain,
      paper_no_need_to_misrepresent_first_choice_for_men_on_strict_domain,
      paper_man_report_preserves_first_choice, paper_is_strict_top_choice_for_man,
      paper_man_weakly_prefers_outcome, paper_strict_marriage_domain,
      paper_matching_valM, paper_women_deferredAcceptance] using
      paper_roth82_corollary5_1_role_reversed_no_need_to_misrepresent_first_choice_on_strict_domain
        (M := M) (W := W)

/--
Lemma 1: Roth's strict simple-misrepresentation same-partner route.
Source status: direct paper lemma on the strict marriage specialization.
-/
theorem lemma1_strict_simple_misrepresentation_same_partner
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M)
    (report_m simple_report_m : W → ℝ) (wstar : W)
    (hdomainSimple :
      strictMarriageDomain (Function.update val_m m simple_report_m) val_w)
    (hyPartner :
      (menDeferredAcceptance (Function.update val_m m report_m) val_w).m_match m =
        some wstar)
    (hfirst : ∀ w, w ≠ wstar → simple_report_m w < simple_report_m wstar) :
    (menDeferredAcceptance (Function.update val_m m simple_report_m) val_w).m_match m =
      (menDeferredAcceptance (Function.update val_m m report_m) val_w).m_match m := by
  simpa [menDeferredAcceptance, strictMarriageDomain, paper_strict_marriage_domain] using
    paper_roth82_lemma1_strict_simple_misrepresentation_same_partner
      val_m val_w m report_m simple_report_m wstar hdomainSimple hyPartner hfirst

/--
Lemma 2: a strict simple misrepresentation cannot harm any other man on the strict marriage domain.
Source status: direct paper lemma on the strict marriage specialization.
-/
theorem lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (simple_report_m : W → ℝ) (ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w)
    (hdomainReport :
      strictMarriageDomain
        (Function.update val_m m simple_report_m) val_w)
    (hy :
      (menDeferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hweakM :
      (match (menDeferredAcceptance val_m val_w).m_match m with
        | none => 0
        | some w => val_m m w) ≤
      (match (menDeferredAcceptance
          (Function.update val_m m simple_report_m) val_w).m_match m with
        | none => 0
        | some w => val_m m w))
    (hfirst : manReportStrictlyRanksPartnerFirst simple_report_m ystar) :
    ∀ m',
      (match (menDeferredAcceptance val_m val_w).m_match m' with
        | none => 0
        | some w => val_m m' w) ≤
      (match (menDeferredAcceptance
          (Function.update val_m m simple_report_m) val_w).m_match m' with
        | none => 0
        | some w => val_m m' w) := by
  simpa [menDeferredAcceptance, strictMarriageDomain, paper_strict_marriage_domain,
    paper_man_weakly_prefers_outcome, manReportStrictlyRanksPartnerFirst,
    paper_man_report_strictly_ranks_partner_first, paper_matching_valM] using
    paper_roth82_lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain
      val_m val_w m simple_report_m ystar hcard hdomain hdomainReport hy hweakM hfirst

/-!
The Section 6 source profile reuses the exact finite profile already used in
the Theorem 3 proof.  The PDF's displayed `g(P')` equation is present on printed
page 626 even though it is lost by plain-text extraction.
-/

/--
Section 6 beneficial-bystander example: truth gives `y`; after `m₂` reports
`w₃ > w₁ > w₂`, the source batched procedure gives `x`. The manipulator
keeps `w₃`, while `m₁` and `m₃` strictly improve under their true rankings.
Source status: direct numerical example.
-/
theorem section6_beneficial_bystander_example :
    sourceBatchedMenDeferredAcceptance theorem3MenProfile
        theorem3WomenProfilePrime = theorem3OutcomeY ∧
      sourceBatchedMenDeferredAcceptance paper_roth82_section6_reported_men
        theorem3WomenProfilePrime = theorem3OutcomeX ∧
      paper_matching_valM theorem3MenProfile 1
          (theorem3OutcomeY.m_match 1) =
        paper_matching_valM theorem3MenProfile 1
          (theorem3OutcomeX.m_match 1) ∧
      paper_matching_valM theorem3MenProfile 0
          (theorem3OutcomeY.m_match 0) <
        paper_matching_valM theorem3MenProfile 0
          (theorem3OutcomeX.m_match 0) ∧
      paper_matching_valM theorem3MenProfile 2
          (theorem3OutcomeY.m_match 2) <
        paper_matching_valM theorem3MenProfile 2
          (theorem3OutcomeX.m_match 2) := by
  exact ⟨paper_roth82_section6_truthful_batched_eq_y,
    paper_roth82_section6_reported_batched_eq_x,
    paper_roth82_section6_beneficial_bystanders⟩

/--
Theorem 6: the men-optimal stable outcome is weakly Pareto optimal on the strict marriage domain.
Source status: direct paper theorem on the strict marriage specialization.
-/
theorem theorem6_weak_pareto_for_men_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w) :
    ¬ ∃ nu : Assignment M W, completeMarriageOutcome nu ∧
      ∀ m, (match (menDeferredAcceptance val_m val_w).m_match m with
        | none => 0
        | some w => val_m m w) <
        (match nu.m_match m with
          | none => 0
          | some w => val_m m w) := by
  simpa [menDeferredAcceptance, completeMarriageOutcome,
    paper_weakly_pareto_optimal_for_men, paper_strictly_better_for_all_men,
    paper_is_complete_matching, paper_matching_valM, strictMarriageDomain,
    paper_strict_marriage_domain] using
    paper_roth82_theorem6_on_strict_marriage_domain
      val_m val_w hcard hdomain

/--
Theorem 7: for any `k > 1`, some finite balanced strict-profile market admits a
profitable stable-procedure `k`th-choice manipulation.
Source status: direct paper statement; the finite marriage counterexample is
sufficient for the paper's general nonexistence claim.
-/
theorem theorem7_arbitrary_k_on_strict_profiles :
    ∀ k, 1 < k →
      ∃ n : ℕ,
        paper_no_stable_procedure_avoids_strict_kth_choice_manipulation_on
          (Fin n) (Fin n) k :=
  paper_roth82_theorem7_arbitrary_k_on_strict_profiles

/-! ## Closed source-result specifications

These closed `Prop` declarations are the semantic audit surface.  The paired
theorems below prove them; implementation helpers and procedure refinements
above receive no independent source-coverage credit.
-/

def theorem1_stable_outcome_existsSpec : Prop :=
  ∀ {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    Fintype.card M = Fintype.card W →
      strictMarriageDomain val_m val_w →
        ∃ mu : Assignment M W, sourceStableMarriage val_m val_w mu

theorem theorem1_stable_outcome_exists : theorem1_stable_outcome_existsSpec := by
  intro M W _ _ _ _ val_m val_w hcard hdomain
  rcases theorem1_stable_complete_outcome_exists_on_strict_marriage_domain
      val_m val_w hcard hdomain with ⟨mu, hstable, hcomplete⟩
  exact ⟨mu,
    operational_and_complete_implies_sourceStableMarriage
      val_m val_w mu hstable hcomplete⟩

def theorem2_side_optimal_stable_outcomesSpec : Prop :=
  ∀ {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    Fintype.card M = Fintype.card W →
      strictMarriageDomain val_m val_w →
        (∃ mu : Assignment M W,
          sourceMenOptimal val_m val_w mu) ∧
        (∃ nu : Assignment M W,
          sourceWomenOptimal val_m val_w nu)

theorem theorem2_side_optimal_stable_outcomes :
    theorem2_side_optimal_stable_outcomesSpec := by
  intro M W _ _ _ _ val_m val_w hcard hdomain
  rcases theorem2_optimal_stable_outcomes_on_strict_marriage_domain
      val_m val_w hdomain with ⟨⟨mu, hmen⟩, ⟨nu, hwomen⟩⟩
  refine ⟨⟨mu, ?_⟩, ⟨nu, ?_⟩⟩
  · refine ⟨operational_and_complete_implies_sourceStableMarriage
        val_m val_w mu hmen.1
        (operationalStable_complete_on_strict_domain_of_card_eq
          val_m val_w mu hcard hdomain hmen.1), ?_⟩
    intro mu' hsource
    exact hmen.2 mu'
      (sourceStableMarriage_implies_operational val_m val_w mu' hdomain hsource)
  · refine ⟨operational_and_complete_implies_sourceStableMarriage
        val_m val_w nu hwomen.1
        (operationalStable_complete_on_strict_domain_of_card_eq
          val_m val_w nu hcard hdomain hwomen.1), ?_⟩
    intro nu' hsource
    exact hwomen.2 nu'
      (sourceStableMarriage_implies_operational val_m val_w nu' hdomain hsource)

def theorem3_no_stable_truthful_procedureSpec : Prop :=
  ¬ ∃ mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent,
    sourceStableMatchingProcedure mechanism ∧ truthfulForAllAgents mechanism

theorem theorem3_no_stable_truthful_procedure :
    theorem3_no_stable_truthful_procedureSpec := by
  rintro ⟨mechanism, hstable, htruthful⟩
  apply theorem3_no_stable_truthful_procedure_on_strict_profiles
  refine ⟨mechanism, ?_, htruthful⟩
  intro val_m val_w hdomain
  exact sourceStableMarriage_implies_operational
    val_m val_w (mechanism val_m val_w) hdomain
      (hstable val_m val_w hdomain)

def theorem4_efficient_truthful_procedure_existsSpec : Prop :=
  ∀ n : ℕ,
    ∃ mechanism :
        (Fin n → Fin n → ℝ) → (Fin n → Fin n → ℝ) →
          Assignment (Fin n) (Fin n),
      efficientMatchingProcedure mechanism ∧ truthfulForAllAgents mechanism

theorem theorem4_efficient_truthful_procedure_exists :
    theorem4_efficient_truthful_procedure_existsSpec := by
  intro n
  rcases theorem4_serial_dictatorship_constructed (n := n) with
    ⟨hefficient, htruthfulMen, htruthfulWomen⟩
  refine ⟨serialDictatorshipMechanism (n := n), ?_, ?_⟩
  · intro val_m val_w hdomain
    exact hefficient val_m val_w hdomain.1
  · constructor
    · intro val_m val_w hdomain m report_m _hdomainReport
      exact htruthfulMen val_m val_w hdomain.1 m report_m
    · intro val_m val_w _hdomain w report_w _hdomainReport
      exact htruthfulWomen val_m val_w w report_w

def theorem5_optimal_side_truthfulSpec : Prop :=
  ∀ {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    Fintype.card M = Fintype.card W →
      strictMarriageDomain val_m val_w →
        (sourceMenOptimal val_m val_w (menDeferredAcceptance val_m val_w) ∧
          ∀ (m : M) (report_m : W → ℝ),
            strictMarriageDomain (Function.update val_m m report_m) val_w →
              (match (menDeferredAcceptance
                  (Function.update val_m m report_m) val_w).m_match m with
                | none => 0
                | some w => val_m m w) ≤
              (match (menDeferredAcceptance val_m val_w).m_match m with
                | none => 0
                | some w => val_m m w)) ∧
        (sourceWomenOptimal val_m val_w (womenDeferredAcceptance val_m val_w) ∧
          ∀ (w : W) (report_w : M → ℝ),
            strictMarriageDomain val_m (Function.update val_w w report_w) →
              (match (womenDeferredAcceptance val_m
                  (Function.update val_w w report_w)).w_match w with
                | none => 0
                | some m => val_w w m) ≤
              (match (womenDeferredAcceptance val_m val_w).w_match w with
                | none => 0
                | some m => val_w w m))

theorem theorem5_optimal_side_truthful : theorem5_optimal_side_truthfulSpec := by
  intro M W _ _ _ _ val_m val_w hcard hdomain
  have htruth := theorem5_optimal_side_truthful_on_strict_domain_of_card_eq
    (M := M) (W := W) val_m val_w hcard hdomain
  have hdomainPaper : paper_strict_marriage_domain val_m val_w := by
    simpa [strictMarriageDomain, paper_strict_marriage_domain] using hdomain
  have hmen : menOptimal val_m val_w (menDeferredAcceptance val_m val_w) := by
    simpa [menOptimal, stable, menDeferredAcceptance, paper_is_men_optimal,
      paper_is_stable, paper_matching_valM, paper_matching_valW] using
      paper_da_is_men_optimal_on_strict_marriage_domain
        val_m val_w hdomainPaper
  have hwomen : womenOptimal val_m val_w (womenDeferredAcceptance val_m val_w) := by
    simpa [womenOptimal, stable, womenDeferredAcceptance,
      paper_women_deferredAcceptance, paper_is_women_optimal, paper_is_stable,
      paper_matching_valM, paper_matching_valW] using
      paper_da_is_women_optimal_on_strict_marriage_domain
        val_m val_w hdomainPaper
  have hmenComplete := operationalStable_complete_on_strict_domain_of_card_eq
    val_m val_w (menDeferredAcceptance val_m val_w) hcard hdomain hmen.1
  have hwomenComplete := operationalStable_complete_on_strict_domain_of_card_eq
    val_m val_w (womenDeferredAcceptance val_m val_w) hcard hdomain hwomen.1
  have hsourceMen :
      sourceMenOptimal val_m val_w (menDeferredAcceptance val_m val_w) := by
    refine ⟨operational_and_complete_implies_sourceStableMarriage
      val_m val_w (menDeferredAcceptance val_m val_w) hmen.1 hmenComplete, ?_⟩
    intro mu hmu
    exact hmen.2 mu
      (sourceStableMarriage_implies_operational val_m val_w mu hdomain hmu)
  have hsourceWomen :
      sourceWomenOptimal val_m val_w (womenDeferredAcceptance val_m val_w) := by
    refine ⟨operational_and_complete_implies_sourceStableMarriage
      val_m val_w (womenDeferredAcceptance val_m val_w) hwomen.1 hwomenComplete, ?_⟩
    intro mu hmu
    exact hwomen.2 mu
      (sourceStableMarriage_implies_operational val_m val_w mu hdomain hmu)
  exact ⟨⟨hsourceMen, fun m report_m _ => htruth.1 m report_m⟩,
    ⟨hsourceWomen, fun w report_w _ => htruth.2 w report_w⟩⟩

def corollary5_1_first_choice_need_not_be_misrepresentedSpec : Prop :=
  ∀ {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M] [Nonempty W],
    Fintype.card M = Fintype.card W →
      (∀ val_m val_w, strictMarriageDomain val_m val_w →
        sourceMenOptimal val_m val_w (menDeferredAcceptance val_m val_w) ∧
        ∀ (w : W) (report_w : M → ℝ),
          strictMarriageDomain val_m (Function.update val_w w report_w) →
          ∃ report_w' : M → ℝ,
            strictMarriageDomain val_m (Function.update val_w w report_w') ∧
            (∀ mstar, (∀ m, m ≠ mstar → val_w w m < val_w w mstar) →
              ∀ m, m ≠ mstar → report_w' m < report_w' mstar) ∧
          (match (menDeferredAcceptance val_m
              (Function.update val_w w report_w)).w_match w with
            | none => 0
            | some m => val_w w m) ≤
          (match (menDeferredAcceptance val_m
              (Function.update val_w w report_w')).w_match w with
            | none => 0
            | some m => val_w w m)) ∧
      (∀ val_m val_w, strictMarriageDomain val_m val_w →
        sourceWomenOptimal val_m val_w (womenDeferredAcceptance val_m val_w) ∧
        ∀ (m : M) (report_m : W → ℝ),
          strictMarriageDomain (Function.update val_m m report_m) val_w →
          ∃ report_m' : W → ℝ,
            strictMarriageDomain (Function.update val_m m report_m') val_w ∧
            (∀ wstar, (∀ w, w ≠ wstar → val_m m w < val_m m wstar) →
              ∀ w, w ≠ wstar → report_m' w < report_m' wstar) ∧
          (match (womenDeferredAcceptance
              (Function.update val_m m report_m) val_w).m_match m with
            | none => 0
            | some w => val_m m w) ≤
          (match (womenDeferredAcceptance
              (Function.update val_m m report_m') val_w).m_match m with
            | none => 0
            | some w => val_m m w))

theorem corollary5_1_first_choice_need_not_be_misrepresented :
    corollary5_1_first_choice_need_not_be_misrepresentedSpec := by
  intro M W _ _ _ _ _ _ hcard
  have hcor := corollary5_1_no_need_to_misrepresent_first_choice
    (M := M) (W := W)
  constructor
  · intro val_m val_w hdomain
    have htheorem5 := theorem5_optimal_side_truthful
      (M := M) (W := W) val_m val_w hcard hdomain
    exact ⟨htheorem5.1.1, hcor.1 val_m val_w hdomain⟩
  · intro val_m val_w hdomain
    have htheorem5 := theorem5_optimal_side_truthful
      (M := M) (W := W) val_m val_w hcard hdomain
    exact ⟨htheorem5.2.1, hcor.2 val_m val_w hdomain⟩

def lemma1_simple_report_same_partnerSpec : Prop :=
  ∀ {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M)
    (report_m simple_report_m : W → ℝ) (wstar : W),
    strictMarriageDomain (Function.update val_m m report_m) val_w →
      strictMarriageDomain (Function.update val_m m simple_report_m) val_w →
        (menDeferredAcceptance (Function.update val_m m report_m) val_w).m_match m =
            some wstar →
        (∀ w, w ≠ wstar → simple_report_m w < simple_report_m wstar) →
          (menDeferredAcceptance
              (Function.update val_m m simple_report_m) val_w).m_match m =
            (menDeferredAcceptance
              (Function.update val_m m report_m) val_w).m_match m

theorem lemma1_simple_report_same_partner : lemma1_simple_report_same_partnerSpec := by
  intro M W _ _ _ _ val_m val_w m report_m simple_report_m wstar
    _hdomainReport hdomainSimple hyPartner hfirst
  exact lemma1_strict_simple_misrepresentation_same_partner
    val_m val_w m report_m simple_report_m wstar hdomainSimple hyPartner hfirst

def lemma2_simple_report_harms_no_manSpec : Prop :=
  ∀ {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (simple_report_m : W → ℝ) (ystar : W),
    Fintype.card M = Fintype.card W →
      strictMarriageDomain val_m val_w →
      strictMarriageDomain (Function.update val_m m simple_report_m) val_w →
      (menDeferredAcceptance
          (Function.update val_m m simple_report_m) val_w).m_match m = some ystar →
      (match (menDeferredAcceptance val_m val_w).m_match m with
        | none => 0
        | some w => val_m m w) ≤
        (match (menDeferredAcceptance
            (Function.update val_m m simple_report_m) val_w).m_match m with
          | none => 0
          | some w => val_m m w) →
      manReportStrictlyRanksPartnerFirst simple_report_m ystar →
        ∀ m',
          (match (menDeferredAcceptance val_m val_w).m_match m' with
            | none => 0
            | some w => val_m m' w) ≤
          (match (menDeferredAcceptance
              (Function.update val_m m simple_report_m) val_w).m_match m' with
            | none => 0
            | some w => val_m m' w)

theorem lemma2_simple_report_harms_no_man : lemma2_simple_report_harms_no_manSpec := by
  intro M W _ _ _ _ val_m val_w m simple_report_m ystar hcard hdomain
    hdomainReport hy hweakM hfirst
  exact lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain
    val_m val_w m simple_report_m ystar hcard hdomain hdomainReport hy hweakM hfirst

def theorem6_no_outcome_strictly_better_for_all_menSpec : Prop :=
  ∀ {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ),
    Fintype.card M = Fintype.card W →
      strictMarriageDomain val_m val_w →
        ¬ ∃ nu : Assignment M W, completeMarriageOutcome nu ∧
          ∀ m,
            (match (menDeferredAcceptance val_m val_w).m_match m with
              | none => 0
              | some w => val_m m w) <
            (match nu.m_match m with
              | none => 0
              | some w => val_m m w)

theorem theorem6_no_outcome_strictly_better_for_all_men :
    theorem6_no_outcome_strictly_better_for_all_menSpec := by
  intro M W _ _ _ _ _ val_m val_w hcard hdomain
  exact theorem6_weak_pareto_for_men_on_strict_marriage_domain
    val_m val_w hcard hdomain

def theorem7_later_choice_manipulation_unavoidableSpec : Prop :=
  ∀ k, 1 < k →
    ∃ n : ℕ,
      paper_no_stable_procedure_avoids_strict_kth_choice_manipulation_on
        (Fin n) (Fin n) k

theorem theorem7_later_choice_manipulation_unavoidable :
    theorem7_later_choice_manipulation_unavoidableSpec :=
  theorem7_arbitrary_k_on_strict_profiles

end PaperInterface
end Roth82StableMatching
