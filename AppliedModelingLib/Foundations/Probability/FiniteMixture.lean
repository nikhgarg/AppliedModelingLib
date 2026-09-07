import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open scoped BigOperators ENNReal

namespace AppliedModelingLib

noncomputable section

/-!
# Finite PMF Mixtures and Event Shares

## Main declarations

- `binaryMixturePMF`: Bernoulli mixture of two PMFs.
- `pmfEventShare`: finite event probability packaged as an `NNReal`.
- `pmfEventShare_event_mass_of_full_support_exists`,
  `indexedPMFEventShare_event_mass_of_full_support_exists`: full support turns
  ordinary event existence into positive-mass event witnesses.
- `indexedEventPositiveOrBlank_of_mass`,
  `indexedEventPositiveOrBlank_of_full_support_exists`: positive-mass event
  witnesses, or full support plus ordinary event existence, discharge indexed
  positive-event-or-blank splits.
- `indexedValueBlankOnZeroEventShare`: use a default indexed value exactly
  when an indexed event has zero finite share.
- `pmf_mixture_cancel_right`, `extensional_law_mixture_cancel_right`:
  positive-share cancellation for binary mixture identities.
- `indexedBinaryMixturePMF_no_positive_event_raw_relevance_iff_selected_eq_unselected_on_positive_event`:
  no positive-event raw binary-mixture relevance is exactly selected/unselected
  equality on positive-event profiles.
- `indexedBinaryMixturePMF_positive_event_of_raw_relevance`:
  raw binary-mixture relevance forces a positive-mass selected event.
- `pmf_map_apply_toReal_pos_of_pos`, `pmf_map_pos_exists_preimage`:
  positive-mass support lemmas for PMF pushforwards.
-/

/-- Binary mixture of two finite laws with mixture share `p`. -/
def binaryMixturePMF
    {α : Type*} (p : NNReal) (hp : p ≤ 1)
    (selected unselected : PMF α) : PMF α :=
  (PMF.bernoulli p hp).bind
    (fun takeSelected => if takeSelected then selected else unselected)

/-- Finite event probability packaged as an `NNReal`. -/
def pmfEventShare
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] : NNReal :=
  ⟨pmfProb μ p, pmfProb_nonneg μ p⟩

@[simp] theorem pmfEventShare_toReal
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    (pmfEventShare μ p).toReal = pmfProb μ p :=
  rfl

/-- A finite PMF event share is at most one. -/
theorem pmfEventShare_le_one
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    pmfEventShare μ p ≤ 1 := by
  change pmfProb μ p ≤ (1 : ℝ)
  exact pmfProb_le_one μ p

/-- A finite PMF event share is positive when the event contains a positive-mass atom. -/
theorem pmfEventShare_pos_of_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (a₀ : α)
    (hp : p a₀) (hmass : 0 < (μ a₀).toReal) :
    0 < (pmfEventShare μ p).toReal := by
  simpa using pmfProb_pos_of_mass μ p a₀ hp hmass

/--
Full support turns an ordinary event witness into the positive-mass witness
needed to prove that a finite event share is positive.
-/
theorem pmfEventShare_event_mass_of_full_support_exists
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (hfull_support : ∀ a, 0 < (μ a).toReal)
    (hexists : ∃ a, p a) :
    ∃ a, p a ∧ 0 < (μ a).toReal := by
  rcases hexists with ⟨a, hp⟩
  exact ⟨a, hp, hfull_support a⟩

/--
With full support, a finite event share is positive whenever the event is
nonempty.
-/
theorem pmfEventShare_pos_of_full_support_exists
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (hfull_support : ∀ a, 0 < (μ a).toReal)
    (hexists : ∃ a, p a) :
    0 < (pmfEventShare μ p).toReal := by
  rcases
    pmfEventShare_event_mass_of_full_support_exists
      μ p hfull_support hexists with
    ⟨a, hp, hmass⟩
  exact pmfEventShare_pos_of_mass μ p a hp hmass

/--
A finite event share is positive exactly when the event contains a
positive-mass atom.
-/
theorem pmfEventShare_pos_iff_exists_pos_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    0 < (pmfEventShare μ p).toReal ↔
      ∃ a, p a ∧ 0 < (μ a).toReal := by
  simpa [pmfEventShare_toReal] using
    (pmfProb_pos_iff_exists_pos_mass μ p)

/--
If a finite event has no positive-mass atom, then its event share is zero.
-/
theorem pmfEventShare_eq_zero_of_no_positive_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (hno_positive : ¬ ∃ a, p a ∧ 0 < (μ a).toReal) :
    (pmfEventShare μ p).toReal = 0 := by
  have hnot_share_pos : ¬ 0 < (pmfEventShare μ p).toReal := by
    intro hshare_pos
    exact hno_positive
      ((pmfEventShare_pos_iff_exists_pos_mass μ p).1 hshare_pos)
  exact le_antisymm (le_of_not_gt hnot_share_pos)
    (by exact pmfProb_nonneg μ p)

/--
A finite event share is zero exactly when the event has no positive-mass atom.
-/
theorem pmfEventShare_eq_zero_iff_no_positive_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    (pmfEventShare μ p).toReal = 0 ↔
      ¬ ∃ a, p a ∧ 0 < (μ a).toReal := by
  constructor
  · intro hzero hpositive
    have hshare_pos :
        0 < (pmfEventShare μ p).toReal :=
      (pmfEventShare_pos_iff_exists_pos_mass μ p).2 hpositive
    rw [hzero] at hshare_pos
    exact (lt_irrefl 0 hshare_pos)
  · exact pmfEventShare_eq_zero_of_no_positive_mass μ p

/--
A finite PMF event share is nonzero exactly when the event contains a
positive-mass atom.
-/
theorem pmfEventShare_ne_zero_iff_exists_pos_mass
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] :
    (pmfEventShare μ p).toReal ≠ 0 ↔
      ∃ a, p a ∧ 0 < (μ a).toReal := by
  constructor
  · intro hne
    by_contra hno_positive
    exact hne
      ((pmfEventShare_eq_zero_iff_no_positive_mass μ p).2 hno_positive)
  · intro hpositive hzero
    exact (pmfEventShare_eq_zero_iff_no_positive_mass μ p).1 hzero hpositive

/--
A finite PMF event share is strictly below one when the complement contains a
positive-mass atom.
-/
theorem pmfEventShare_lt_one_of_mass_not
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p] (a₀ : α)
    (hp : ¬p a₀) (hmass : 0 < (μ a₀).toReal) :
    pmfEventShare μ p < 1 := by
  change pmfProb μ p < (1 : ℝ)
  exact pmfProb_lt_one_of_mass_not μ p a₀ hp hmass

/--
With full support, a finite event share is strictly below one whenever the
event does not contain every atom.
-/
theorem pmfEventShare_lt_one_of_full_support_not_all
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (p : α → Prop) [DecidablePred p]
    (hfull_support : ∀ a, 0 < (μ a).toReal)
    (hnot_all : ∃ a, ¬ p a) :
    pmfEventShare μ p < 1 := by
  rcases hnot_all with ⟨a, hnot⟩
  exact pmfEventShare_lt_one_of_mass_not μ p a hnot (hfull_support a)

/-- Two-index family of finite event shares. -/
def indexedPMFEventShare
    {ι κ α : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k)) :
    ι → κ → NNReal :=
  fun i k => @pmfEventShare α _ _ (μ i k) (event i k) (decEvent i k)

/-- Two-index finite event shares are at most one. -/
theorem indexedPMFEventShare_le_one
    {ι κ α : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k)) :
    ∀ i k, indexedPMFEventShare μ event decEvent i k ≤ 1 := by
  intro i k
  dsimp [indexedPMFEventShare]
  exact @pmfEventShare_le_one α _ _ (μ i k) (event i k) (decEvent i k)

/--
Two-index finite event shares are positive whenever each indexed event
contains a positive-mass atom.
-/
theorem indexedPMFEventShare_pos_of_mass
    {ι κ α : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (hwitness :
      ∀ i k, ∃ a, event i k a ∧ 0 < (μ i k a).toReal) :
    ∀ i k, 0 < (indexedPMFEventShare μ event decEvent i k).toReal := by
  intro i k
  rcases hwitness i k with ⟨a, hevent, hmass⟩
  dsimp [indexedPMFEventShare]
  exact @pmfEventShare_pos_of_mass α _ _ (μ i k)
    (event i k) (decEvent i k) a hevent hmass

/--
Full support turns ordinary indexed event witnesses into the positive-mass
witnesses needed for indexed finite event-share positivity.
-/
theorem indexedPMFEventShare_event_mass_of_full_support_exists
    {ι κ α : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (hfull_support : ∀ i k a, 0 < (μ i k a).toReal)
    (hexists : ∀ i k, ∃ a, event i k a) :
    ∀ i k, ∃ a, event i k a ∧ 0 < (μ i k a).toReal := by
  intro i k
  rcases hexists i k with ⟨a, hevent⟩
  exact ⟨a, hevent, hfull_support i k a⟩

/--
With full support, indexed finite event shares are positive whenever each
indexed event is nonempty.
-/
theorem indexedPMFEventShare_pos_of_full_support_exists
    {ι κ α : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (hfull_support : ∀ i k a, 0 < (μ i k a).toReal)
    (hexists : ∀ i k, ∃ a, event i k a) :
    ∀ i k, 0 < (indexedPMFEventShare μ event decEvent i k).toReal :=
  indexedPMFEventShare_pos_of_mass μ event decEvent
    (indexedPMFEventShare_event_mass_of_full_support_exists
      μ event hfull_support hexists)

/--
Two-index finite event shares are positive exactly when the indexed event
contains a positive-mass atom.
-/
theorem indexedPMFEventShare_pos_iff_exists_pos_mass
    {ι κ α : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k)) :
    ∀ i k,
      0 < (indexedPMFEventShare μ event decEvent i k).toReal ↔
        ∃ a, event i k a ∧ 0 < (μ i k a).toReal := by
  intro i k
  dsimp [indexedPMFEventShare]
  exact @pmfEventShare_pos_iff_exists_pos_mass α _ _
    (μ i k) (event i k) (decEvent i k)

/--
If an indexed event has no positive-mass atom, then its finite event share is
zero.
-/
theorem indexedPMFEventShare_eq_zero_of_no_positive_mass
    {ι κ α : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (i : ι) (k : κ)
    (hno_positive : ¬ ∃ a, event i k a ∧ 0 < (μ i k a).toReal) :
    (indexedPMFEventShare μ event decEvent i k).toReal = 0 := by
  dsimp [indexedPMFEventShare]
  exact
    @pmfEventShare_eq_zero_of_no_positive_mass α _ _
      (μ i k) (event i k) (decEvent i k) hno_positive

/--
An indexed finite event share is zero exactly when that indexed event has no
positive-mass atom.
-/
theorem indexedPMFEventShare_eq_zero_iff_no_positive_mass
    {ι κ α : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k)) :
    ∀ i k,
      (indexedPMFEventShare μ event decEvent i k).toReal = 0 ↔
        ¬ ∃ a, event i k a ∧ 0 < (μ i k a).toReal := by
  intro i k
  dsimp [indexedPMFEventShare]
  exact
    @pmfEventShare_eq_zero_iff_no_positive_mass α _ _
      (μ i k) (event i k) (decEvent i k)

/--
An indexed finite event share is nonzero exactly when that indexed event
contains a positive-mass atom.
-/
theorem indexedPMFEventShare_ne_zero_iff_exists_pos_mass
    {ι κ α : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k)) :
    ∀ i k,
      (indexedPMFEventShare μ event decEvent i k).toReal ≠ 0 ↔
        ∃ a, event i k a ∧ 0 < (μ i k a).toReal := by
  intro i k
  dsimp [indexedPMFEventShare]
  exact
    @pmfEventShare_ne_zero_iff_exists_pos_mass α _ _
      (μ i k) (event i k) (decEvent i k)

/--
All indexed finite event shares are zero exactly when no indexed event has a
positive-mass atom.
-/
theorem indexedPMFEventShare_all_zero_iff_no_positive_mass
    {ι κ α : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k)) :
    (∀ i k, (indexedPMFEventShare μ event decEvent i k).toReal = 0) ↔
      ∀ i k, ¬ ∃ a, event i k a ∧ 0 < (μ i k a).toReal := by
  constructor
  · intro hzero i k
    exact
      (indexedPMFEventShare_eq_zero_iff_no_positive_mass
        μ event decEvent i k).1 (hzero i k)
  · intro hno_positive i k
    exact
      (indexedPMFEventShare_eq_zero_iff_no_positive_mass
        μ event decEvent i k).2 (hno_positive i k)

/--
Two-index finite event shares are strictly below one whenever each indexed
event has a positive-mass atom outside it.
-/
theorem indexedPMFEventShare_lt_one_of_mass_not
    {ι κ α : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (hwitness :
      ∀ i k, ∃ a, ¬ event i k a ∧ 0 < (μ i k a).toReal) :
    ∀ i k, indexedPMFEventShare μ event decEvent i k < 1 := by
  intro i k
  rcases hwitness i k with ⟨a, hnot_event, hmass⟩
  dsimp [indexedPMFEventShare]
  exact @pmfEventShare_lt_one_of_mass_not α _ _ (μ i k)
    (event i k) (decEvent i k) a hnot_event hmass

/--
Full support turns an ordinary complement witness into the positive-mass
complement witness needed for indexed finite event-share bounds.
-/
theorem indexedPMFEventShare_complement_mass_of_full_support_not_all
    {ι κ α : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (hfull_support : ∀ i k a, 0 < (μ i k a).toReal)
    (hnot_all : ∀ i k, ∃ a, ¬ event i k a) :
    ∀ i k, ∃ a, ¬ event i k a ∧ 0 < (μ i k a).toReal := by
  intro i k
  rcases hnot_all i k with ⟨a, hnot_event⟩
  exact ⟨a, hnot_event, hfull_support i k a⟩

/--
With full support, an indexed finite event share is strictly below one whenever
the event does not contain every atom.
-/
theorem indexedPMFEventShare_lt_one_of_full_support_not_all
    {ι κ α : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (hfull_support : ∀ i k a, 0 < (μ i k a).toReal)
    (hnot_all : ∀ i k, ∃ a, ¬ event i k a) :
    ∀ i k, indexedPMFEventShare μ event decEvent i k < 1 :=
  indexedPMFEventShare_lt_one_of_mass_not μ event decEvent
    (indexedPMFEventShare_complement_mass_of_full_support_not_all
      μ event hfull_support hnot_all)

/--
Indexed case split: at each `(i, k)`, either the indexed event has a
positive-mass atom or the indexed value is blank for every test/index value.
-/
def indexedEventPositiveOrBlank
    {ι κ τ α Value : Type*}
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (baseValue : ι → κ → Value)
    (fullValue : ι → κ → τ → Value) : Prop :=
  ∀ i k,
    (∃ a, event i k a ∧ 0 < (μ i k a).toReal) ∨
      ∀ t, baseValue i k = fullValue i k t

/--
Positive-mass event witnesses discharge the indexed positive-event-or-blank
case split directly.
-/
theorem indexedEventPositiveOrBlank_of_mass
    {ι κ τ α Value : Type*}
    {μ : ι → κ → PMF α}
    {event : ι → κ → α → Prop}
    {baseValue : ι → κ → Value}
    {fullValue : ι → κ → τ → Value}
    (hwitness :
      ∀ i k, ∃ a, event i k a ∧ 0 < (μ i k a).toReal) :
    indexedEventPositiveOrBlank μ event baseValue fullValue := by
  intro i k
  exact Or.inl (hwitness i k)

/--
With full support, ordinary indexed event witnesses discharge the indexed
positive-event-or-blank case split directly.
-/
theorem indexedEventPositiveOrBlank_of_full_support_exists
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (baseValue : ι → κ → Value)
    (fullValue : ι → κ → τ → Value)
    (hfull_support : ∀ i k a, 0 < (μ i k a).toReal)
    (hexists : ∀ i k, ∃ a, event i k a) :
    indexedEventPositiveOrBlank μ event baseValue fullValue :=
  indexedEventPositiveOrBlank_of_mass
    (indexedPMFEventShare_event_mass_of_full_support_exists
      μ event hfull_support hexists)

/--
If every profile with no positive-mass event atom is blank, then the indexed
positive-event-or-blank case split holds.
-/
theorem indexedEventPositiveOrBlank_of_no_positive_event_implies_blank
    {ι κ τ α Value : Type*}
    {μ : ι → κ → PMF α}
    {event : ι → κ → α → Prop}
    {baseValue : ι → κ → Value}
    {fullValue : ι → κ → τ → Value}
    (hblank_of_no_positive :
      ∀ i k,
        (¬ ∃ a, event i k a ∧ 0 < (μ i k a).toReal) →
          ∀ t, baseValue i k = fullValue i k t) :
    indexedEventPositiveOrBlank μ event baseValue fullValue := by
  intro i k
  by_cases hpositive :
      ∃ a, event i k a ∧ 0 < (μ i k a).toReal
  · exact Or.inl hpositive
  · exact Or.inr (hblank_of_no_positive i k hpositive)

/--
Zero indexed event share is enough for the indexed positive-event-or-blank
case split.
-/
theorem indexedEventPositiveOrBlank_of_zero_event_share_implies_blank
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    {μ : ι → κ → PMF α}
    {event : ι → κ → α → Prop}
    (decEvent : ∀ i k, DecidablePred (event i k))
    {baseValue : ι → κ → Value}
    {fullValue : ι → κ → τ → Value}
    (hblank_of_zero_share :
      ∀ i k,
        (indexedPMFEventShare μ event decEvent i k).toReal = 0 →
          ∀ t, baseValue i k = fullValue i k t) :
    indexedEventPositiveOrBlank μ event baseValue fullValue := by
  refine indexedEventPositiveOrBlank_of_no_positive_event_implies_blank ?_
  intro i k hno_positive
  exact hblank_of_zero_share i k
    (indexedPMFEventShare_eq_zero_of_no_positive_mass
      μ event decEvent i k hno_positive)

/--
Indexed value that equals `baseValue` when the indexed finite event share is
zero and otherwise equals a supplied raw indexed value.
-/
def indexedValueBlankOnZeroEventShare
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value) :
    ι → κ → τ → Value :=
  fun i k t =>
    if (indexedPMFEventShare μ event decEvent i k).toReal = 0 then
      baseValue i k
    else
      rawValue i k t

/--
The blank-on-zero-share indexed value is equal to the base value at every
zero-share profile.
-/
theorem indexedValueBlankOnZeroEventShare_eq_base_of_zero_share
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value)
    (i : ι) (k : κ)
    (hzero : (indexedPMFEventShare μ event decEvent i k).toReal = 0)
    (t : τ) :
    indexedValueBlankOnZeroEventShare μ event decEvent baseValue rawValue
      i k t =
        baseValue i k := by
  simp [indexedValueBlankOnZeroEventShare, hzero]

/--
If the blank-on-zero-share indexed value differs from the base value, then the
indexed event share is nonzero.
-/
theorem indexedValueBlankOnZeroEventShare_nonzero_share_of_ne_base
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value)
    (i : ι) (k : κ) (t : τ)
    (hne :
      baseValue i k ≠
        indexedValueBlankOnZeroEventShare μ event decEvent baseValue rawValue
          i k t) :
    (indexedPMFEventShare μ event decEvent i k).toReal ≠ 0 := by
  intro hzero
  exact hne
    (indexedValueBlankOnZeroEventShare_eq_base_of_zero_share
      μ event decEvent baseValue rawValue i k hzero t).symm

/--
If the blank-on-zero-share indexed value differs from the base value, then the
indexed event contains a positive-mass atom.
-/
theorem indexedValueBlankOnZeroEventShare_positive_event_of_ne_base
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value)
    (i : ι) (k : κ) (t : τ)
    (hne :
      baseValue i k ≠
        indexedValueBlankOnZeroEventShare μ event decEvent baseValue rawValue
          i k t) :
    ∃ a, event i k a ∧ 0 < (μ i k a).toReal := by
  by_contra hno_positive
  have hzero :
      (indexedPMFEventShare μ event decEvent i k).toReal = 0 :=
    (indexedPMFEventShare_eq_zero_iff_no_positive_mass
      μ event decEvent i k).2 hno_positive
  exact hne
    (indexedValueBlankOnZeroEventShare_eq_base_of_zero_share
      μ event decEvent baseValue rawValue i k hzero t).symm

/--
The blank-on-zero-share indexed value preserves the supplied raw value at every
nonzero-share profile.
-/
theorem indexedValueBlankOnZeroEventShare_eq_raw_of_nonzero_share
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value)
    (i : ι) (k : κ)
    (hshare : (indexedPMFEventShare μ event decEvent i k).toReal ≠ 0)
    (t : τ) :
    indexedValueBlankOnZeroEventShare μ event decEvent baseValue rawValue
      i k t =
        rawValue i k t := by
  simp [indexedValueBlankOnZeroEventShare, hshare]

/--
Pointwise relevance for the blank-on-zero-share value is exactly raw relevance
at a nonzero-share profile.
-/
theorem indexedValueBlankOnZeroEventShare_ne_base_iff_nonzero_share_and_raw_ne
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value)
    (i : ι) (k : κ) (t : τ) :
    baseValue i k ≠
        indexedValueBlankOnZeroEventShare μ event decEvent baseValue rawValue
          i k t ↔
      (indexedPMFEventShare μ event decEvent i k).toReal ≠ 0 ∧
        baseValue i k ≠ rawValue i k t := by
  constructor
  · intro hne
    have hshare :
        (indexedPMFEventShare μ event decEvent i k).toReal ≠ 0 :=
      indexedValueBlankOnZeroEventShare_nonzero_share_of_ne_base
        μ event decEvent baseValue rawValue i k t hne
    refine ⟨hshare, ?_⟩
    intro hbase_raw
    exact hne
      (hbase_raw.trans
        (indexedValueBlankOnZeroEventShare_eq_raw_of_nonzero_share
          μ event decEvent baseValue rawValue i k hshare t).symm)
  · rintro ⟨hshare, hraw_ne⟩ hbase_blank
    exact hraw_ne
      (hbase_blank.trans
        (indexedValueBlankOnZeroEventShare_eq_raw_of_nonzero_share
          μ event decEvent baseValue rawValue i k hshare t))

/--
Pointwise relevance for the blank-on-zero-share value is exactly raw relevance
at a profile whose indexed event contains a positive-mass atom.
-/
theorem indexedValueBlankOnZeroEventShare_ne_base_iff_positive_event_and_raw_ne
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value)
    (i : ι) (k : κ) (t : τ) :
    baseValue i k ≠
        indexedValueBlankOnZeroEventShare μ event decEvent baseValue rawValue
          i k t ↔
      (∃ a, event i k a ∧ 0 < (μ i k a).toReal) ∧
        baseValue i k ≠ rawValue i k t := by
  rw [indexedValueBlankOnZeroEventShare_ne_base_iff_nonzero_share_and_raw_ne,
    (indexedPMFEventShare_ne_zero_iff_exists_pos_mass μ event decEvent i k)]

/--
Existential relevance for the blank-on-zero-share value is exactly raw
relevance at a profile whose indexed event contains a positive-mass atom.
-/
theorem indexedValueBlankOnZeroEventShare_exists_ne_base_iff_exists_positive_event_and_raw_ne
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value) :
    (∃ i k t,
      baseValue i k ≠
        indexedValueBlankOnZeroEventShare μ event decEvent baseValue rawValue
          i k t) ↔
      ∃ i k a t,
        event i k a ∧ 0 < (μ i k a).toReal ∧
          baseValue i k ≠ rawValue i k t := by
  constructor
  · rintro ⟨i, k, t, hne⟩
    rcases
        (indexedValueBlankOnZeroEventShare_ne_base_iff_positive_event_and_raw_ne
          μ event decEvent baseValue rawValue i k t).1 hne with
      ⟨⟨a, hevent, hmass⟩, hraw_ne⟩
    exact ⟨i, k, a, t, hevent, hmass, hraw_ne⟩
  · rintro ⟨i, k, a, t, hevent, hmass, hraw_ne⟩
    exact
      ⟨i, k, t,
        (indexedValueBlankOnZeroEventShare_ne_base_iff_positive_event_and_raw_ne
          μ event decEvent baseValue rawValue i k t).2
          ⟨⟨a, hevent, hmass⟩, hraw_ne⟩⟩

/--
The blank-on-zero-share indexed value preserves the supplied raw value at every
profile whose event contains a positive-mass atom.
-/
theorem indexedValueBlankOnZeroEventShare_eq_raw_of_positive_event
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value)
    (i : ι) (k : κ) (a : α)
    (hevent : event i k a)
    (hmass : 0 < (μ i k a).toReal)
    (t : τ) :
    indexedValueBlankOnZeroEventShare μ event decEvent baseValue rawValue
      i k t =
        rawValue i k t := by
  have hshare_pos :
      0 < (indexedPMFEventShare μ event decEvent i k).toReal :=
    (indexedPMFEventShare_pos_iff_exists_pos_mass μ event decEvent i k).2
      ⟨a, hevent, hmass⟩
  exact
    indexedValueBlankOnZeroEventShare_eq_raw_of_nonzero_share
      μ event decEvent baseValue rawValue i k (ne_of_gt hshare_pos) t

/--
If the blank-on-zero-share normalized value has no raw relevance, then the raw
value has no relevance at nonzero-share profiles.
-/
theorem indexedValueBlankOnZeroEventShare_no_raw_relevance_of_no_normalized_relevance
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value)
    (hnormalized :
      ¬ ∃ i k t,
        baseValue i k ≠
          indexedValueBlankOnZeroEventShare
            μ event decEvent baseValue rawValue i k t) :
    ¬ ∃ i k t,
      (indexedPMFEventShare μ event decEvent i k).toReal ≠ 0 ∧
        baseValue i k ≠ rawValue i k t := by
  rintro ⟨i, k, t, hshare, hraw⟩
  exact hnormalized ⟨i, k, t, by
    intro hnorm
    have hnorm_raw :=
      indexedValueBlankOnZeroEventShare_eq_raw_of_nonzero_share
        μ event decEvent baseValue rawValue i k hshare t
    exact hraw (hnorm.trans hnorm_raw)⟩

/--
If the blank-on-zero-share normalized value has no raw relevance, then the raw
value has no relevance at any positive-mass event profile.
-/
theorem indexedValueBlankOnZeroEventShare_no_raw_relevance_of_positive_event
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value)
    (hnormalized :
      ¬ ∃ i k t,
        baseValue i k ≠
          indexedValueBlankOnZeroEventShare
            μ event decEvent baseValue rawValue i k t) :
    ¬ ∃ i k a t,
      event i k a ∧
        0 < (μ i k a).toReal ∧
          baseValue i k ≠ rawValue i k t := by
  rintro ⟨i, k, a, t, hevent, hmass, hraw⟩
  exact hnormalized ⟨i, k, t, by
    intro hnorm
    have hnorm_raw :=
      indexedValueBlankOnZeroEventShare_eq_raw_of_positive_event
        μ event decEvent baseValue rawValue i k a hevent hmass t
    exact hraw (hnorm.trans hnorm_raw)⟩

/--
For the blank-on-zero-share indexed value, no normalized relevance is
equivalent to no raw relevance on nonzero-share profiles.
-/
theorem indexedValueBlankOnZeroEventShare_no_normalized_relevance_iff_no_raw_relevance_on_nonzero_share
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value) :
    (¬ ∃ i k t,
      baseValue i k ≠
        indexedValueBlankOnZeroEventShare
          μ event decEvent baseValue rawValue i k t) ↔
      ¬ ∃ i k t,
        (indexedPMFEventShare μ event decEvent i k).toReal ≠ 0 ∧
          baseValue i k ≠ rawValue i k t := by
  constructor
  · intro hnormalized
    exact
      indexedValueBlankOnZeroEventShare_no_raw_relevance_of_no_normalized_relevance
        μ event decEvent baseValue rawValue hnormalized
  · intro hraw
    rintro ⟨i, k, t, hnormalized_witness⟩
    by_cases hshare :
        (indexedPMFEventShare μ event decEvent i k).toReal = 0
    · have hblank :=
        indexedValueBlankOnZeroEventShare_eq_base_of_zero_share
          μ event decEvent baseValue rawValue i k hshare t
      exact hnormalized_witness hblank.symm
    · have hnorm_raw :=
        indexedValueBlankOnZeroEventShare_eq_raw_of_nonzero_share
          μ event decEvent baseValue rawValue i k hshare t
      exact hraw ⟨i, k, t, hshare, by
        intro hbase_raw
        exact hnormalized_witness (hbase_raw.trans hnorm_raw.symm)⟩

/--
For the blank-on-zero-share indexed value, no normalized relevance is
equivalent to no raw relevance at positive-mass event profiles.
-/
theorem indexedValueBlankOnZeroEventShare_no_normalized_relevance_iff_no_raw_relevance_on_positive_event
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value) :
    (¬ ∃ i k t,
      baseValue i k ≠
        indexedValueBlankOnZeroEventShare
          μ event decEvent baseValue rawValue i k t) ↔
      ¬ ∃ i k a t,
        event i k a ∧
          0 < (μ i k a).toReal ∧
            baseValue i k ≠ rawValue i k t := by
  constructor
  · intro hnormalized
    exact
      indexedValueBlankOnZeroEventShare_no_raw_relevance_of_positive_event
        μ event decEvent baseValue rawValue hnormalized
  · intro hraw
    rintro ⟨i, k, t, hnormalized_witness⟩
    by_cases hshare :
        (indexedPMFEventShare μ event decEvent i k).toReal = 0
    · have hblank :=
        indexedValueBlankOnZeroEventShare_eq_base_of_zero_share
          μ event decEvent baseValue rawValue i k hshare t
      exact hnormalized_witness hblank.symm
    · have hpositive :
          ∃ a, event i k a ∧ 0 < (μ i k a).toReal := by
        by_contra hno_positive
        exact hshare
          (indexedPMFEventShare_eq_zero_of_no_positive_mass
            μ event decEvent i k hno_positive)
      rcases hpositive with ⟨a, hevent, hmass⟩
      have hnorm_raw :=
        indexedValueBlankOnZeroEventShare_eq_raw_of_positive_event
          μ event decEvent baseValue rawValue i k a hevent hmass t
      exact hraw ⟨i, k, a, t, hevent, hmass, by
        intro hbase_raw
        exact hnormalized_witness (hbase_raw.trans hnorm_raw.symm)⟩

/--
The blank-on-zero-share indexed value discharges the positive-event-or-blank
case split by construction.
-/
theorem indexedEventPositiveOrBlank_of_blankOnZeroEventShare
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value) :
    indexedEventPositiveOrBlank μ event baseValue
      (indexedValueBlankOnZeroEventShare
        μ event decEvent baseValue rawValue) := by
  exact
    indexedEventPositiveOrBlank_of_zero_event_share_implies_blank
      decEvent
      (by
        intro i k hzero t
        exact
          indexedValueBlankOnZeroEventShare_eq_base_of_zero_share
            μ event decEvent baseValue rawValue i k hzero t |>.symm)

/--
If every indexed event share is zero, then the blank-on-zero-share indexed
value is everywhere equal to the base value.
-/
theorem indexedValueBlankOnZeroEventShare_eq_base_of_all_zero_share
    {ι κ τ α Value : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (baseValue : ι → κ → Value)
    (rawValue : ι → κ → τ → Value)
    (hzero : ∀ i k,
      (indexedPMFEventShare μ event decEvent i k).toReal = 0) :
    ∀ i k t,
      baseValue i k =
        indexedValueBlankOnZeroEventShare
          μ event decEvent baseValue rawValue i k t := by
  intro i k t
  exact
    (indexedValueBlankOnZeroEventShare_eq_base_of_zero_share
      μ event decEvent baseValue rawValue i k (hzero i k) t).symm

/--
Positive-share cancellation for finite PMF mixtures. If
`D0 = λ D1 + (1 - λ) D0` pointwise in real mass and `λ > 0`, then `D1 = D0`.
-/
theorem pmf_mixture_cancel_right
    {α : Type*} {lambda : ℝ} (hlambda : 0 < lambda)
    {selected unselected : PMF α}
    (hmix :
      ∀ a,
        (unselected a).toReal =
          lambda * (selected a).toReal +
            (1 - lambda) * (unselected a).toReal) :
    selected = unselected := by
  apply PMF.ext
  intro a
  apply (ENNReal.toReal_eq_toReal_iff'
    (selected.apply_ne_top a)
    (unselected.apply_ne_top a)).mp
  have h := hmix a
  nlinarith

/--
Positive-share cancellation for laws represented by an extensional real-mass
functional.
-/
theorem extensional_law_mixture_cancel_right
    {Outcome Law : Type*} {lambda : ℝ} (hlambda : 0 < lambda)
    (mass : Law → Outcome → ℝ)
    (law_ext :
      ∀ {L1 L0 : Law}, (∀ outcome, mass L1 outcome = mass L0 outcome) →
        L1 = L0)
    {selected unselected : Law}
    (hmix :
      ∀ outcome,
        mass unselected outcome =
          lambda * mass selected outcome +
            (1 - lambda) * mass unselected outcome) :
    selected = unselected := by
  apply law_ext
  intro outcome
  have h := hmix outcome
  nlinarith

/--
Positive mass survives pushing a PMF forward to the image point.
-/
theorem pmf_map_apply_toReal_pos_of_pos
    {α β : Type*} (μ : PMF α) (f : α → β) (a : α)
    (hmass : 0 < (μ a).toReal) :
    0 < ((μ.map f) (f a)).toReal := by
  have ha_support : a ∈ μ.support := by
    rw [PMF.mem_support_iff]
    exact ne_of_gt (ENNReal.toReal_pos_iff.mp hmass).1
  have hfa_support : f a ∈ (μ.map f).support := by
    exact (PMF.mem_support_map_iff f μ (f a)).mpr
      ⟨a, ha_support, rfl⟩
  exact ENNReal.toReal_pos
    ((PMF.mem_support_iff (μ.map f) (f a)).mp hfa_support)
    ((μ.map f).apply_ne_top (f a))

/--
Every positive-mass atom of a pushforward PMF has a positive-mass preimage.
-/
theorem pmf_map_pos_exists_preimage
    {α β : Type*} (μ : PMF α) (f : α → β) (b : β)
    (hmass : 0 < ((μ.map f) b).toReal) :
    ∃ a, f a = b ∧ 0 < (μ a).toReal := by
  have hb_support : b ∈ (μ.map f).support := by
    rw [PMF.mem_support_iff]
    exact ne_of_gt (ENNReal.toReal_pos_iff.mp hmass).1
  rcases (PMF.mem_support_map_iff f μ b).mp hb_support with
    ⟨a, ha_support, hfa⟩
  have hμ_ne : μ a ≠ 0 := (PMF.mem_support_iff μ a).mp ha_support
  exact ⟨a, hfa,
    ENNReal.toReal_pos hμ_ne (μ.apply_ne_top a)⟩

/-- Point-mass PMFs are equal exactly when their atoms are equal. -/
theorem pmf_pure_eq_iff
    {α : Type*} [DecidableEq α] {x y : α} :
    PMF.pure x = PMF.pure y ↔ x = y := by
  constructor
  · intro h
    by_contra hne
    have hmass : PMF.pure x x = PMF.pure y x := by
      simpa using congrArg (fun μ : PMF α => μ x) h
    have hleft : PMF.pure x x = (1 : ℝ≥0∞) := by
      simp [PMF.pure_apply]
    have hright : PMF.pure y x = (0 : ℝ≥0∞) := by
      simp [PMF.pure_apply, hne]
    rw [hleft, hright] at hmass
    exact one_ne_zero hmass
  · intro h
    subst h
    rfl

/-- Distinct atoms give distinct point-mass PMFs. -/
theorem pmf_pure_ne_of_ne
    {α : Type*} {x y : α} (hne : x ≠ y) :
    PMF.pure x ≠ PMF.pure y := by
  intro h
  have hx : x ∈ (PMF.pure x).support := by
    simpa using ((PMF.mem_support_pure_iff (a := x) (a' := x)).2 rfl)
  have hy : x ∈ (PMF.pure y).support := by
    simpa [h] using hx
  exact hne ((PMF.mem_support_pure_iff (a := y) (a' := x)).1 hy)

/--
Support-aware point-mass exclusion implies support-aware value exclusion.
This removes Dirac PMF wrappers from finite point-estimate no-relevance
statements.
-/
theorem not_exists_pos_mass_value_ne_of_not_exists_pos_mass_pmf_pure_ne
    {ι α β γ : Type*}
    (μ : ι → α → PMF β)
    (baseValue : ι → α → γ)
    (fullValue : ι → α → β → γ)
    (hno_pure :
      ¬ ∃ i a b,
        0 < (μ i a b).toReal ∧
          PMF.pure (baseValue i a) ≠ PMF.pure (fullValue i a b)) :
    ¬ ∃ i a b,
      0 < (μ i a b).toReal ∧
        baseValue i a ≠ fullValue i a b := by
  rintro ⟨i, a, b, hmass, hne⟩
  exact
    hno_pure
      ⟨i, a, b, hmass, pmf_pure_ne_of_ne hne⟩

/--
Point-mass exclusion implies value exclusion.  This is the ordinary
no-relevance version of
`not_exists_pos_mass_value_ne_of_not_exists_pos_mass_pmf_pure_ne`.
-/
theorem not_exists_value_ne_of_not_exists_pmf_pure_ne
    {ι α β γ : Type*}
    (baseValue : ι → α → γ)
    (fullValue : ι → α → β → γ)
    (hno_pure :
      ¬ ∃ i a b,
        PMF.pure (baseValue i a) ≠ PMF.pure (fullValue i a b)) :
    ¬ ∃ i a b,
      baseValue i a ≠ fullValue i a b := by
  rintro ⟨i, a, b, hne⟩
  exact
    hno_pure
      ⟨i, a, b, pmf_pure_ne_of_ne hne⟩

/--
Full support upgrades support-aware Dirac-law exclusion to ordinary value
exclusion.  This is a common final step for finite point-estimate
no-relevance endpoints.
-/
theorem not_exists_value_ne_of_not_exists_pos_mass_pmf_pure_ne_of_full_support
    {ι α β γ : Type*}
    (μ : ι → α → PMF β)
    (baseValue : ι → α → γ)
    (fullValue : ι → α → β → γ)
    (hfull_support : ∀ i a b, 0 < (μ i a b).toReal)
    (hno_pure :
      ¬ ∃ i a b,
        0 < (μ i a b).toReal ∧
          PMF.pure (baseValue i a) ≠ PMF.pure (fullValue i a b)) :
    ¬ ∃ i a b,
      baseValue i a ≠ fullValue i a b := by
  exact
    not_exists_of_not_exists_pos_mass_of_full_support μ
      (fun i a b => baseValue i a ≠ fullValue i a b)
      hfull_support
      (not_exists_pos_mass_value_ne_of_not_exists_pos_mass_pmf_pure_ne
        μ baseValue fullValue hno_pure)

/-- Pointwise real-mass formula for `binaryMixturePMF`. -/
theorem binaryMixturePMF_apply_toReal
    {α : Type*} (p : NNReal) (hp : p ≤ 1)
    (selected unselected : PMF α) (a : α) :
    (binaryMixturePMF p hp selected unselected a).toReal =
      p.toReal * (selected a).toReal +
        (1 - p.toReal) * (unselected a).toReal := by
  rw [binaryMixturePMF, PMF.bind_apply]
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [PMF.bernoulli_apply, Bool.cond_true, Bool.cond_false, if_true]
  rw [if_neg (by decide : ¬ false = true)]
  have hleft_ne :
      ↑p * selected a ≠ (∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (selected.apply_ne_top a)
  have hright_ne :
      ↑(1 - p) * unselected a ≠ (∞ : ℝ≥0∞) :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top
      (unselected.apply_ne_top a)
  rw [ENNReal.toReal_add hleft_ne hright_ne]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  have hsub_toReal :
      (↑(1 - p) : ℝ≥0∞).toReal = 1 - p.toReal := by
    change ((1 - p : NNReal) : ℝ) = 1 - (p : ℝ)
    exact NNReal.coe_sub hp
  rw [hsub_toReal]
  simp

/-- A finite expectation is affine in a binary mixture of its sampling law. -/
theorem pmfExp_binaryMixturePMF
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : NNReal) (hp : p ≤ 1) (selected unselected : PMF α) (f : α → ℝ) :
    pmfExp (binaryMixturePMF p hp selected unselected) f =
      p.toReal * pmfExp selected f + (1 - p.toReal) * pmfExp unselected f := by
  unfold pmfExp
  simp_rw [binaryMixturePMF_apply_toReal, add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- A pairwise expectation is affine in its first sampling law. -/
theorem pmfPairExp_binaryMixturePMF_left
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (p : NNReal) (hp : p ≤ 1) (selected unselected : PMF α) (right : PMF β)
    (f : α → β → ℝ) :
    pmfPairExp (binaryMixturePMF p hp selected unselected) right f =
      p.toReal * pmfPairExp selected right f +
        (1 - p.toReal) * pmfPairExp unselected right f :=
  pmfExp_binaryMixturePMF p hp selected unselected
    (fun left => pmfExp right (fun right => f left right))

/-- A pairwise expectation is affine in its second sampling law. -/
theorem pmfPairExp_binaryMixturePMF_right
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (p : NNReal) (hp : p ≤ 1) (left : PMF α) (selected unselected : PMF β)
    (f : α → β → ℝ) :
    pmfPairExp left (binaryMixturePMF p hp selected unselected) f =
      p.toReal * pmfPairExp left selected f +
        (1 - p.toReal) * pmfPairExp left unselected f := by
  unfold pmfPairExp
  calc
    pmfExp left (fun first =>
        pmfExp (binaryMixturePMF p hp selected unselected) (fun second => f first second)) =
      pmfExp left (fun first =>
        p.toReal * pmfExp selected (fun second => f first second) +
          (1 - p.toReal) * pmfExp unselected (fun second => f first second)) := by
        refine pmfExp_congr left fun first => ?_
        exact pmfExp_binaryMixturePMF p hp selected unselected (f first)
    _ = p.toReal * pmfExp left (fun first => pmfExp selected (fun second => f first second)) +
          (1 - p.toReal) *
            pmfExp left (fun first => pmfExp unselected (fun second => f first second)) := by
          rw [pmfExp_add, pmfExp_const_mul, pmfExp_const_mul]

/--
When the selected share is zero, a binary PMF mixture is the unselected law.
-/
theorem binaryMixturePMF_eq_unselected_of_zero
    {α : Type*} (p : NNReal) (hp : p ≤ 1)
    (selected unselected : PMF α)
    (hzero : p.toReal = 0) :
    binaryMixturePMF p hp selected unselected = unselected := by
  apply PMF.ext
  intro a
  apply (ENNReal.toReal_eq_toReal_iff'
    ((binaryMixturePMF p hp selected unselected).apply_ne_top a)
    (unselected.apply_ne_top a)).mp
  rw [binaryMixturePMF_apply_toReal, hzero]
  ring

/--
If the selected and unselected component laws agree, a binary PMF mixture
collapses to that common law.
-/
theorem binaryMixturePMF_eq_unselected_of_selected_eq_unselected
    {α : Type*} (p : NNReal) (hp : p ≤ 1)
    (selected unselected : PMF α)
    (heq : selected = unselected) :
    binaryMixturePMF p hp selected unselected = unselected := by
  subst selected
  apply PMF.ext
  intro a
  apply (ENNReal.toReal_eq_toReal_iff'
    ((binaryMixturePMF p hp unselected unselected).apply_ne_top a)
    (unselected.apply_ne_top a)).mp
  rw [binaryMixturePMF_apply_toReal]
  ring

/--
With positive selected share, a binary PMF mixture equals the unselected law
only if the selected and unselected laws are equal.
-/
theorem selected_eq_unselected_of_binaryMixturePMF_eq_unselected
    {α : Type*} (p : NNReal) (hp : p ≤ 1)
    (selected unselected : PMF α)
    (hpos : 0 < p.toReal)
    (hmix : binaryMixturePMF p hp selected unselected = unselected) :
    selected = unselected := by
  refine pmf_mixture_cancel_right hpos ?_
  intro a
  have hpoint :
      (unselected a).toReal =
        (binaryMixturePMF p hp selected unselected a).toReal := by
    simpa [hmix]
  simpa [binaryMixturePMF_apply_toReal] using hpoint

/--
With positive selected share, a binary PMF mixture equals the unselected law
exactly when the selected and unselected laws are equal.
-/
theorem binaryMixturePMF_eq_unselected_iff_of_pos
    {α : Type*} (p : NNReal) (hp : p ≤ 1)
    (selected unselected : PMF α)
    (hpos : 0 < p.toReal) :
    binaryMixturePMF p hp selected unselected = unselected ↔
      selected = unselected :=
  ⟨selected_eq_unselected_of_binaryMixturePMF_eq_unselected
      p hp selected unselected hpos,
    binaryMixturePMF_eq_unselected_of_selected_eq_unselected
      p hp selected unselected⟩

/--
With positive selected share, the unselected law equals a binary PMF mixture
exactly when the selected and unselected laws are equal.
-/
theorem unselected_eq_binaryMixturePMF_iff_of_pos
    {α : Type*} (p : NNReal) (hp : p ≤ 1)
    (selected unselected : PMF α)
    (hpos : 0 < p.toReal) :
    unselected = binaryMixturePMF p hp selected unselected ↔
      selected = unselected := by
  constructor
  · intro hmix
    exact
      selected_eq_unselected_of_binaryMixturePMF_eq_unselected
        p hp selected unselected hpos hmix.symm
  · intro heq
    exact
      (binaryMixturePMF_eq_unselected_of_selected_eq_unselected
        p hp selected unselected heq).symm

/--
With positive selected share and distinct component laws, a binary PMF mixture
is not the unselected law.
-/
theorem binaryMixturePMF_ne_unselected_of_pos_of_ne
    {α : Type*} (p : NNReal) (hp : p ≤ 1)
    (selected unselected : PMF α)
    (hpos : 0 < p.toReal)
    (hne : selected ≠ unselected) :
    binaryMixturePMF p hp selected unselected ≠ unselected := by
  intro hmix
  exact hne
    (selected_eq_unselected_of_binaryMixturePMF_eq_unselected
      p hp selected unselected hpos hmix)

/--
With positive selected share and distinct component laws, the unselected law is
not the binary PMF mixture.
-/
theorem unselected_ne_binaryMixturePMF_of_pos_of_ne
    {α : Type*} (p : NNReal) (hp : p ≤ 1)
    (selected unselected : PMF α)
    (hpos : 0 < p.toReal)
    (hne : selected ≠ unselected) :
    unselected ≠ binaryMixturePMF p hp selected unselected := by
  exact (binaryMixturePMF_ne_unselected_of_pos_of_ne
    p hp selected unselected hpos hne).symm

/--
For an indexed binary-mixture surface whose share is the finite mass of an
event, raw relevance of the displayed mixture implies that the event has a
positive-mass atom.  If the event had no positive-mass atom, the mixture share
would be zero and the mixture would reduce to the unselected law.
-/
theorem indexedBinaryMixturePMF_positive_event_of_raw_relevance
    {ι κ α β : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (selected unselected : ι → κ → PMF β)
    (i : ι) (k : κ)
    (hraw :
      unselected i k ≠
        binaryMixturePMF
          (indexedPMFEventShare μ event decEvent i k)
          (indexedPMFEventShare_le_one μ event decEvent i k)
          (selected i k) (unselected i k)) :
    ∃ a, event i k a ∧ 0 < (μ i k a).toReal := by
  by_contra hno_positive
  have hzero :
      (indexedPMFEventShare μ event decEvent i k).toReal = 0 :=
    (indexedPMFEventShare_eq_zero_iff_no_positive_mass
      μ event decEvent i k).2 hno_positive
  exact hraw
    (binaryMixturePMF_eq_unselected_of_zero
      (indexedPMFEventShare μ event decEvent i k)
      (indexedPMFEventShare_le_one μ event decEvent i k)
      (selected i k) (unselected i k) hzero).symm

/--
For an indexed binary-mixture surface whose mixture share is the finite mass of
an event, absence of positive-event raw relevance is equivalent to selected and
unselected laws agreeing at every positive-mass event profile.

The extra `witnessOf` argument supplies the paper-level auxiliary witness in
the existential relevance statement when a component-law difference is turned
into a positive-event relevance witness.
-/
theorem indexedBinaryMixturePMF_no_positive_event_raw_relevance_iff_selected_eq_unselected_on_positive_event
    {ι κ α β τ : Type*} [Fintype α] [DecidableEq α]
    (μ : ι → κ → PMF α)
    (event : ι → κ → α → Prop)
    (decEvent : ∀ i k, DecidablePred (event i k))
    (selected unselected : ι → κ → PMF β)
    (witnessOf : ι → κ → τ) :
    (¬ ∃ i k a, ∃ t : τ,
      event i k a ∧
        0 < (μ i k a).toReal ∧
          unselected i k ≠
            binaryMixturePMF
              (indexedPMFEventShare μ event decEvent i k)
              (indexedPMFEventShare_le_one μ event decEvent i k)
              (selected i k) (unselected i k)) ↔
      (∀ i k a,
        event i k a →
          0 < (μ i k a).toReal →
            selected i k = unselected i k) := by
  constructor
  · intro hno i k a hevent hmass
    by_contra hne
    have hshare_pos :
        0 < (indexedPMFEventShare μ event decEvent i k).toReal :=
      (indexedPMFEventShare_pos_iff_exists_pos_mass μ event decEvent i k).2
        ⟨a, hevent, hmass⟩
    exact hno
      ⟨i, k, a, witnessOf i k, hevent, hmass,
        unselected_ne_binaryMixturePMF_of_pos_of_ne
          (indexedPMFEventShare μ event decEvent i k)
          (indexedPMFEventShare_le_one μ event decEvent i k)
          (selected i k) (unselected i k) hshare_pos hne⟩
  · intro hEq hrel
    rcases hrel with ⟨i, k, a, t, hevent, hmass, hne⟩
    exact hne
      (binaryMixturePMF_eq_unselected_of_selected_eq_unselected
        (indexedPMFEventShare μ event decEvent i k)
        (indexedPMFEventShare_le_one μ event decEvent i k)
        (selected i k) (unselected i k)
        (hEq i k a hevent hmass)).symm

end

end AppliedModelingLib
