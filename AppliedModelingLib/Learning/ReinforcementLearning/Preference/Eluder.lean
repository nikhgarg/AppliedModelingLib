import Mathlib.Tactic

/-!
# Finite eluder sequences

This module gives the finite-sequence form of the eluder-dimension definition
used by confidence-set preference-RL analyses.  It keeps the existential
scale in the source definition explicit, rather than treating an eluder
dimension bound as an opaque query-count certificate.
-/

open scoped BigOperators

namespace AppliedModelingLib

namespace PreferenceRL

/--
At `index`, a point is `epsilon`-independent of its preceding points for a
function class when two class members agree in squared error on the prefix at
some scale at least `epsilon`, yet differ by at least that scale at the point.
This is Definition 2's finite algebraic form; for a nonnegative scale, the
squared-prefix condition is equivalent to its displayed square-root form.
-/
def EpsilonIndependentAt {Input : Type*}
    (functionClass : Set (Input → ℝ)) (points : ℕ → Input)
    (epsilon : ℝ) (index : ℕ) : Prop :=
  ∃ scale, epsilon ≤ scale ∧ ∃ first ∈ functionClass, ∃ second ∈ functionClass,
    (∑ prior ∈ Finset.range index,
      (first (points prior) - second (points prior)) ^ 2) ≤ scale ^ 2 ∧
    scale ≤ |first (points index) - second (points index)|

/-- A finite prefix is an eluder sequence when each of its positions is independent. -/
def IsEpsilonEluderSequence {Input : Type*}
    (functionClass : Set (Input → ℝ)) (points : ℕ → Input)
    (epsilon : ℝ) (length : ℕ) : Prop :=
  ∀ index < length, EpsilonIndependentAt functionClass points epsilon index

/--
`dimension` is an upper bound for the `epsilon`-eluder dimension when no
finite epsilon-eluder sequence for the class can be longer than it.
-/
def EluderDimensionAtMost {Input : Type*}
    (functionClass : Set (Input → ℝ)) (epsilon : ℝ) (dimension : ℕ) : Prop :=
  ∀ length points, IsEpsilonEluderSequence functionClass points epsilon length →
    length ≤ dimension

/-- An eluder-dimension upper bound for a function class also bounds every
subclass at the same scale. -/
theorem EluderDimensionAtMost.mono {Input : Type*}
    {smaller larger : Set (Input → ℝ)} {epsilon : ℝ} {dimension : ℕ}
    (hsubset : smaller ⊆ larger)
    (hlarger : EluderDimensionAtMost larger epsilon dimension) :
    EluderDimensionAtMost smaller epsilon dimension := by
  intro length points hsequence
  apply hlarger length points
  intro index hindex
  rcases hsequence index hindex with
    ⟨scale, hscale, first, hfirst, second, hsecond, hprefix, hgap⟩
  exact ⟨scale, hscale, first, hsubset hfirst, second, hsubset hsecond,
    hprefix, hgap⟩

/--
A concrete pair of confidence-set functions with squared-prefix agreement and
current-point separation supplies the corresponding Definition-2
independence witness at that same scale.
-/
theorem epsilonIndependentAt_of_squaredPrefix_and_gap {Input : Type*}
    (functionClass : Set (Input → ℝ)) (points : ℕ → Input)
    (epsilon : ℝ) (index : ℕ) (first second : Input → ℝ)
    (hfirst : first ∈ functionClass) (hsecond : second ∈ functionClass)
    (hprefix : (∑ prior ∈ Finset.range index,
      (first (points prior) - second (points prior)) ^ 2) ≤ epsilon ^ 2)
    (hgap : epsilon ≤ |first (points index) - second (points index)|) :
    EpsilonIndependentAt functionClass points epsilon index :=
  ⟨epsilon, le_rfl, first, hfirst, second, hsecond, hprefix, hgap⟩

/--
The deterministic endgame in an eluder-dimension query bound.  If each of
`count` queried points has a candidate and the true function as a
Definition-2 witness at scale `epsilon`, no more than the assumed eluder
dimension can have been queried.
-/
theorem queryCount_le_eluderDimension_of_confidenceWitnesses {Input : Type*}
    (functionClass : Set (Input → ℝ)) (points : ℕ → Input)
    (epsilon : ℝ) (dimension count : ℕ) (truth : Input → ℝ)
    (candidate : ℕ → Input → ℝ)
    (htruth : truth ∈ functionClass)
    (hcandidate : ∀ index < count, candidate index ∈ functionClass)
    (hprefix : ∀ index < count,
      (∑ prior ∈ Finset.range index,
        (candidate index (points prior) - truth (points prior)) ^ 2) ≤ epsilon ^ 2)
    (hgap : ∀ index < count,
      epsilon ≤ |candidate index (points index) - truth (points index)|)
    (hdimension : EluderDimensionAtMost functionClass epsilon dimension) :
    count ≤ dimension := by
  apply hdimension count points
  intro index hindex
  exact epsilonIndependentAt_of_squaredPrefix_and_gap functionClass points epsilon index
    (candidate index) truth (hcandidate index hindex) htruth
    (hprefix index hindex) (hgap index hindex)

end PreferenceRL

end AppliedModelingLib
