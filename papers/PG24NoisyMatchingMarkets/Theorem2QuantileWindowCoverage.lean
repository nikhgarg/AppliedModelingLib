import PG24NoisyMatchingMarkets.Theorem2QuantifierRepair

/-!
# PG24 Theorem 2 quantile-window coverage

The amplification proof chooses `vLow`, `vHigh`, and `vStar` from shrinking
value-law tails and then needs those windows to contain each fixed target.
This module proves that implication directly.  In particular, converting the
source's two open-tail bounds into a tail bound above `vStar` needs
nonatomicity; an atom at `vHigh` is otherwise missing from the displayed
mass accounting.
-/

open Filter MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
The two open pieces used by the source quantile construction bound the tail
above `vStar` when the value law has no atoms.

This is the precise repair for the endpoint omitted by
`proof-amplifying.tex:31`: without `NoAtoms`, the atom at `vHigh` belongs to
`Ioi vStar` but not to either displayed open set.
-/
theorem theorem2_upperTailMass_le_of_open_quantile_window_noAtoms
    (η : Measure ℝ) [IsFiniteMeasure η] [NoAtoms η]
    {vStar vHigh windowMass highTailMass : ℝ}
    (horder : vStar ≤ vHigh)
    (hwindow : η.real (Set.Ioo vStar vHigh) ≤ windowMass)
    (hhigh : η.real (Set.Ioi vHigh) ≤ highTailMass) :
    η.real (Set.Ioi vStar) ≤ windowMass + highTailMass := by
  have htail_eq :
      η.real (Set.Ioi vStar) =
        η.real (Set.Ioo vStar vHigh ∪ Set.Ioi vHigh) := by
    symm
    exact MeasureTheory.measureReal_congr
      (AppliedModelingLib.ae_eq_Ioo_union_Ioi_touching η horder)
  calc
    η.real (Set.Ioi vStar) =
        η.real (Set.Ioo vStar vHigh ∪ Set.Ioi vHigh) := htail_eq
    _ ≤ η.real (Set.Ioo vStar vHigh) + η.real (Set.Ioi vHigh) :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ windowMass + highTailMass := add_le_add hwindow hhigh

/--
Without nonatomicity, the same tail estimate must pay explicitly for the
possible atom at the high endpoint.
-/
theorem theorem2_upperTailMass_le_of_open_quantile_window_with_atom
    (η : Measure ℝ) [IsFiniteMeasure η]
    {vStar vHigh windowMass highTailMass atomMass : ℝ}
    (hwindow : η.real (Set.Ioo vStar vHigh) ≤ windowMass)
    (hhigh : η.real (Set.Ioi vHigh) ≤ highTailMass)
    (hatom : η.real ({vHigh} : Set ℝ) ≤ atomMass) :
    η.real (Set.Ioi vStar) ≤ windowMass + highTailMass + atomMass := by
  have hsubset :
      Set.Ioi vStar ⊆
        (Set.Ioo vStar vHigh ∪ Set.Ioi vHigh) ∪ ({vHigh} : Set ℝ) := by
    intro x hx
    rcases lt_or_ge x vHigh with hlt | hge
    · exact Or.inl (Or.inl ⟨hx, hlt⟩)
    · rcases lt_or_eq_of_le hge with hgt | heq
      · exact Or.inl (Or.inr hgt)
      · exact Or.inr (by simpa [heq])
  calc
    η.real (Set.Ioi vStar) ≤
        η.real ((Set.Ioo vStar vHigh ∪ Set.Ioi vHigh) ∪ ({vHigh} : Set ℝ)) :=
      MeasureTheory.measureReal_mono hsubset (measure_ne_top η _)
    _ ≤ η.real (Set.Ioo vStar vHigh ∪ Set.Ioi vHigh) +
          η.real ({vHigh} : Set ℝ) :=
      MeasureTheory.measureReal_union_le _ _
    _ ≤ (η.real (Set.Ioo vStar vHigh) + η.real (Set.Ioi vHigh)) +
          η.real ({vHigh} : Set ℝ) := by
      gcongr
      exact MeasureTheory.measureReal_union_le _ _
    _ ≤ (windowMass + highTailMass) + atomMass :=
      add_le_add (add_le_add hwindow hhigh) hatom
    _ = windowMass + highTailMass + atomMass := by ring

/--
A shrinking lower-tail budget forces its endpoint below every target with
positive value-law mass below it.
-/
theorem theorem2_eventually_lowerEndpoint_lt_of_lowerTailBudget
    (η : Measure ℝ) [IsFiniteMeasure η]
    {vLow lowerBudget : ℕ → ℝ} {v : ℝ}
    (hbudget : Tendsto lowerBudget atTop (nhds 0))
    (hlowTail : ∀ᶠ n : ℕ in atTop,
      η.real (Set.Iio (vLow n)) ≤ lowerBudget n)
    (hv : 0 < η.real (Set.Iio v)) :
    ∀ᶠ n : ℕ in atTop, vLow n < v := by
  have hsmall : ∀ᶠ n : ℕ in atTop, lowerBudget n < η.real (Set.Iio v) :=
    hbudget (isOpen_Iio.mem_nhds hv)
  filter_upwards [hsmall, hlowTail] with n hsmall_n htail_n
  by_contra hnot
  have horder : v ≤ vLow n := le_of_not_gt hnot
  have hmono : η.real (Set.Iio v) ≤ η.real (Set.Iio (vLow n)) :=
    MeasureTheory.measureReal_mono
      (by
        intro x hx
        exact lt_of_lt_of_le hx horder)
      (measure_ne_top η _)
  linarith

/--
A shrinking strict upper-tail budget forces its endpoint above every target
with positive value-law mass above it.
-/
theorem theorem2_eventually_lt_upperEndpoint_of_upperTailBudget
    (η : Measure ℝ) [IsFiniteMeasure η]
    {vStar upperBudget : ℕ → ℝ} {v : ℝ}
    (hbudget : Tendsto upperBudget atTop (nhds 0))
    (hupperTail : ∀ᶠ n : ℕ in atTop,
      η.real (Set.Ioi (vStar n)) ≤ upperBudget n)
    (hv : 0 < η.real (Set.Ioi v)) :
    ∀ᶠ n : ℕ in atTop, v < vStar n := by
  have hsmall : ∀ᶠ n : ℕ in atTop, upperBudget n < η.real (Set.Ioi v) :=
    hbudget (isOpen_Iio.mem_nhds hv)
  filter_upwards [hsmall, hupperTail] with n hsmall_n htail_n
  by_contra hnot
  have horder : vStar n ≤ v := le_of_not_gt hnot
  have hmono : η.real (Set.Ioi v) ≤ η.real (Set.Ioi (vStar n)) :=
    MeasureTheory.measureReal_mono
      (by
        intro x hx
        exact lt_of_le_of_lt horder hx)
      (measure_ne_top η _)
  linarith

/--
The repaired target-coverage bridge for the local Theorem 2 proof window.
It applies to targets in the interior of the value law's support, expressed
semantically as positive mass on both sides of the target.
-/
theorem theorem2_localWindowMembership_eventually_of_tailBudgets
    (η : Measure ℝ) [IsFiniteMeasure η]
    {vLow vHigh vStar lowerBudget upperBudget : ℕ → ℝ} {v : ℝ}
    (hlowerBudget : Tendsto lowerBudget atTop (nhds 0))
    (hupperBudget : Tendsto upperBudget atTop (nhds 0))
    (hlowTail : ∀ᶠ n : ℕ in atTop,
      η.real (Set.Iio (vLow n)) ≤ lowerBudget n)
    (hupperTail : ∀ᶠ n : ℕ in atTop,
      η.real (Set.Ioi (vStar n)) ≤ upperBudget n)
    (hstar_le_high : ∀ᶠ n : ℕ in atTop, vStar n ≤ vHigh n)
    (hvLower : 0 < η.real (Set.Iio v))
    (hvUpper : 0 < η.real (Set.Ioi v)) :
    ∀ᶠ n : ℕ in atTop,
      theorem2_localWindowMembership (vLow n) (vHigh n) (vStar n) v := by
  filter_upwards
      [theorem2_eventually_lowerEndpoint_lt_of_lowerTailBudget
        η hlowerBudget hlowTail hvLower,
       theorem2_eventually_lt_upperEndpoint_of_upperTailBudget
        η hupperBudget hupperTail hvUpper,
       hstar_le_high] with n hlow_n hupper_n hstar_high_n
  exact ⟨le_of_lt hlow_n, le_trans (le_of_lt hupper_n) hstar_high_n,
    le_of_lt hupper_n⟩

/--
The source's quantile-window masses give the shrinking upper-tail budget needed
by the coverage bridge, once nonatomicity makes its open endpoints legitimate.
-/
theorem theorem2_eventually_upperTailBudget_of_quantileWindows_noAtoms
    (η : Measure ℝ) [IsFiniteMeasure η] [NoAtoms η]
    {epsilon vStar vHigh : ℕ → ℝ}
    (hwindow : ∀ᶠ n : ℕ in atTop,
      η.real (Set.Ioo (vStar n) (vHigh n)) ≤ Real.sqrt (epsilon n))
    (hhigh : ∀ᶠ n : ℕ in atTop,
      η.real (Set.Ioi (vHigh n)) ≤ epsilon n / 2)
    (horder : ∀ᶠ n : ℕ in atTop, vStar n ≤ vHigh n) :
    ∀ᶠ n : ℕ in atTop,
      η.real (Set.Ioi (vStar n)) ≤ Real.sqrt (epsilon n) + epsilon n / 2 := by
  filter_upwards [hwindow, hhigh, horder] with n hwindow_n hhigh_n horder_n
  exact theorem2_upperTailMass_le_of_open_quantile_window_noAtoms
    η horder_n hwindow_n hhigh_n

/-- The source's `sqrt(epsilon) + epsilon / 2` upper-tail budget vanishes. -/
theorem theorem2_quantile_upperTailBudget_tendsto_zero
    {epsilon : ℕ → ℝ}
    (hepsilon : Tendsto epsilon atTop (nhds 0)) :
    Tendsto (fun n : ℕ => Real.sqrt (epsilon n) + epsilon n / 2)
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (epsilon n)) atTop (nhds 0) := by
    simpa [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hepsilon
  have hhalf : Tendsto (fun n : ℕ => epsilon n / 2) atTop (nhds 0) := by
    simpa using
      (hepsilon.div tendsto_const_nhds (by norm_num : (2 : ℝ) ≠ 0))
  simpa using hsqrt.add hhalf

/--
Complete source-shaped coverage theorem for the `v_-`, `v_+`, `v^*` schedule.
The target must be in the interior of the value-law support, and nonatomicity
is an explicit hypothesis rather than an unstated endpoint convention.
-/
theorem theorem2_localWindowMembership_eventually_of_quantileWindows_noAtoms
    (η : Measure ℝ) [IsFiniteMeasure η] [NoAtoms η]
    {epsilon vLow vHigh vStar : ℕ → ℝ} {v : ℝ}
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hlow : ∀ᶠ n : ℕ in atTop,
      η.real (Set.Iio (vLow n)) ≤ epsilon n / 2)
    (hwindow : ∀ᶠ n : ℕ in atTop,
      η.real (Set.Ioo (vStar n) (vHigh n)) ≤ Real.sqrt (epsilon n))
    (hhigh : ∀ᶠ n : ℕ in atTop,
      η.real (Set.Ioi (vHigh n)) ≤ epsilon n / 2)
    (horder : ∀ᶠ n : ℕ in atTop, vStar n ≤ vHigh n)
    (hvLower : 0 < η.real (Set.Iio v))
    (hvUpper : 0 < η.real (Set.Ioi v)) :
    ∀ᶠ n : ℕ in atTop,
      theorem2_localWindowMembership (vLow n) (vHigh n) (vStar n) v := by
  have hlowerBudget :
      Tendsto (fun n : ℕ => epsilon n / 2) atTop (nhds 0) := by
    simpa using
      (hepsilon.div tendsto_const_nhds (by norm_num : (2 : ℝ) ≠ 0))
  exact theorem2_localWindowMembership_eventually_of_tailBudgets
    η hlowerBudget (theorem2_quantile_upperTailBudget_tendsto_zero hepsilon)
    hlow
    (theorem2_eventually_upperTailBudget_of_quantileWindows_noAtoms
      η hwindow hhigh horder)
    horder hvLower hvUpper

end

end PG24NoisyMatchingMarkets
