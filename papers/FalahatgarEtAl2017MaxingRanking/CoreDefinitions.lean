import AppliedModelingLib.Learning.ReinforcementLearning.Preference.ApproximateDynamicProgramming

/-!
# Falahatgar et al. (2017): maxing primitives

The definitions in this file follow Sections 1.2 and 3 of the NeurIPS source.
The preference quantity is centered: `preferenceGap first second` is
`p(first, second) - 1 / 2` in the paper's notation.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL

/-- The paper's strong stochastic transitivity condition. -/
def StrongStochasticTransitivity {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) : Prop :=
  ∀ first middle last,
    0 ≤ preferenceGap first middle →
    0 ≤ preferenceGap middle last →
    max (preferenceGap first middle) (preferenceGap middle last) ≤
      preferenceGap first last

/-- An arm that is preferable to every arm, including possible preference ties. -/
def AbsoluteMaximum {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (selected : Arm) : Prop :=
  ∀ competitor, 0 ≤ preferenceGap selected competitor

/-- The source's `ε`-maximum definition, written through the shared PAC interface. -/
def EpsilonMaximum {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (selected : Arm) : Prop :=
  ApproximatePreferenceWinner preferenceGap selected epsilon

/-- An `ε`-maximum restricted to a currently active finite set. -/
def EpsilonMaximumOn {Arm : Type*} [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (active : Finset Arm) (selected : Arm) : Prop :=
  selected ∈ active ∧ ∀ competitor ∈ active,
    -epsilon ≤ preferenceGap selected competitor

/-- A finite output order whose earlier arms are `ε`-preferable to later ones. -/
def EpsilonPreferenceRanking {Arm : Type*} [Fintype Arm]
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm) : Prop :=
  Function.Bijective ranking ∧ ∀ first second, first.val ≤ second.val →
    -epsilon ≤ preferenceGap (ranking first) (ranking second)

/-- An exact preference ranking, the model assumption in Appendix B.2. -/
def PreferenceRanking {Arm : Type*} [Fintype Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm) : Prop :=
  Function.Bijective ranking ∧ ∀ first second, first.val ≤ second.val →
    0 ≤ preferenceGap (ranking first) (ranking second)

/-- The arms at and after one position in a finite output order. -/
noncomputable def rankingSuffix {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (ranking : Fin (Fintype.card Arm) → Arm) (start : ℕ) : Finset Arm :=
  ((Finset.univ : Finset (Fin (Fintype.card Arm))).filter fun slot => start ≤ slot.val).image
    ranking

/-- A slot at or after `start` belongs to the corresponding output suffix. -/
theorem mem_rankingSuffix {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (ranking : Fin (Fintype.card Arm) → Arm) (start : ℕ)
    (slot : Fin (Fintype.card Arm)) (hslot : start ≤ slot.val) :
    ranking slot ∈ rankingSuffix ranking start := by
  classical
  exact Finset.mem_image.mpr ⟨slot,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hslot⟩, rfl⟩

/-- The current arm of an exact ranking is a maximum of every later suffix. -/
theorem absoluteMaximumOn_rankingSuffix_of_preferenceRanking
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (first : Fin (Fintype.card Arm)) :
    EpsilonMaximumOn preferenceGap 0 (rankingSuffix ranking first.val) (ranking first) := by
  refine ⟨mem_rankingSuffix ranking first.val first (le_refl _), ?_⟩
  intro competitor hcompetitor
  rcases Finset.mem_image.mp hcompetitor with ⟨second, hsecond, hvalue⟩
  have horder : first.val ≤ second.val := (Finset.mem_filter.mp hsecond).2
  rw [← hvalue]
  simpa using hranking.2 first second horder

/--
Selecting an `ε`-maximum of the remaining suffix at every position produces
an `ε`-ranking.  This is the deterministic invariant used in Appendix B.2.
-/
theorem epsilonPreferenceRanking_of_suffixEpsilonMaximum
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hbijective : Function.Bijective ranking)
    (hsuffix : ∀ first,
      EpsilonMaximumOn preferenceGap epsilon
        (rankingSuffix ranking first.val) (ranking first)) :
    EpsilonPreferenceRanking preferenceGap epsilon ranking := by
  refine ⟨hbijective, ?_⟩
  intro first second horder
  exact (hsuffix first).2 (ranking second)
    (mem_rankingSuffix ranking first.val second horder)

/-- A source-faithful `(ε, n')`-good-anchor predicate on a finite arm set. -/
def GoodAnchor {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
  (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (cutoff : ℕ) (anchor : Arm) : Prop :=
  (Finset.univ.filter fun arm => epsilon < preferenceGap arm anchor).card ≤ cutoff

/-- An approximate maximum remains one when its allowed error is enlarged. -/
theorem epsilonMaximum_mono {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (lower upper : ℝ) (selected : Arm)
    (hmaximum : EpsilonMaximum preferenceGap lower selected) (hle : lower ≤ upper) :
    EpsilonMaximum preferenceGap upper selected := by
  intro competitor
  exact (neg_le_neg hle).trans (hmaximum competitor)

/-- An absolute maximum is an `ε`-maximum for every nonnegative `ε`. -/
theorem epsilonMaximum_of_absoluteMaximum {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (selected : Arm)
    (hepsilon : 0 ≤ epsilon)
    (hmaximum : AbsoluteMaximum preferenceGap selected) :
    EpsilonMaximum preferenceGap epsilon selected := by
  intro competitor
  exact (neg_nonpos.mpr hepsilon).trans (hmaximum competitor)

/--
Under antisymmetry and SST, an arm that is `ε`-preferable to an absolute
maximum is an `ε`-maximum. This is the finite relation argument used in
Appendix A.3 and A.7 when the source transfers a guarantee from `b*`.
-/
theorem epsilonMaximum_of_epsilonPreferableTo_absoluteMaximum {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum selected : Arm)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hpreferable : -epsilon ≤ preferenceGap selected maximum) :
    EpsilonMaximum preferenceGap epsilon selected := by
  intro competitor
  by_cases hselectedMaximum : 0 ≤ preferenceGap selected maximum
  · have hchain := hsst selected maximum competitor hselectedMaximum (hmaximum competitor)
    exact hpreferable.trans ((le_max_left _ _).trans hchain)
  by_cases hselectedCompetitor : 0 ≤ preferenceGap selected competitor
  · exact (neg_nonpos.mpr hepsilon).trans hselectedCompetitor
  have hcompetitorSelected : 0 ≤ preferenceGap competitor selected := by
    rw [hantisymmetric selected competitor]
    linarith
  have hchain := hsst maximum competitor selected (hmaximum competitor) hcompetitorSelected
  have hcomparisonBound :
      preferenceGap competitor selected ≤ preferenceGap maximum selected :=
    (le_max_right _ _).trans hchain
  rw [hantisymmetric selected competitor, hantisymmetric selected maximum] at hcomparisonBound
  linarith

/--
The contrapositive gap form used by OPT-Maximize and Prune: if an anchor is
not an `ε`-maximum, the absolute maximum beats it by strictly more than `ε`.
-/
theorem absoluteMaximum_gap_gt_of_not_epsilonMaximum {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum anchor : Arm)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hanchorNotMaximum : ¬ EpsilonMaximum preferenceGap epsilon anchor) :
    epsilon < preferenceGap maximum anchor := by
  by_contra hnotStrict
  apply hanchorNotMaximum
  apply epsilonMaximum_of_epsilonPreferableTo_absoluteMaximum preferenceGap epsilon
    hantisymmetric hsst hepsilon maximum anchor hmaximum
  rw [hantisymmetric maximum anchor]
  linarith

/--
Appendix A.7's subset-to-full-set transfer: if a candidate set contains an
absolute maximum, an `ε`-maximum within that set is one for the original set.
-/
theorem epsilonMaximum_of_subsetContainsAbsoluteMaximum {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (subset : Set Arm) (maximum selected : Arm)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hmaximumMem : maximum ∈ subset)
    (hsubsetWinner : ∀ competitor, competitor ∈ subset →
      -epsilon ≤ preferenceGap selected competitor) :
    EpsilonMaximum preferenceGap epsilon selected :=
  epsilonMaximum_of_epsilonPreferableTo_absoluteMaximum preferenceGap epsilon hantisymmetric
    hsst hepsilon maximum selected hmaximum (hsubsetWinner maximum hmaximumMem)

end FalahatgarEtAl2017MaxingRanking
