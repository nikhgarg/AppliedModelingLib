import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Compact

namespace AppliedModelingLib
namespace Optimization

open scoped BigOperators

/-!
# Optimization Certificates

Reusable certificate wrappers for finite, LP, allocation, and policy
optimization arguments.

## Main declarations

- `IsGlobalMaximizer`, `IsGlobalMinimizer`: unrestricted optimality.
- `IsMaximizerOn`, `IsMinimizerOn`: optimality on an explicit feasible set.
- `IsLexicographicMaximizerOn`: primary-objective maximization with a
  secondary tie-breaker objective.
- `UpperBoundCertificate`: a candidate value plus a universal upper bound.
- `LowerBoundCertificate`: a candidate value plus a universal lower bound.
- `StrictUpperBoundCertificate`, `StrictLowerBoundCertificate`: uniqueness
  variants based on strict bounds away from the candidate.
- `AlgorithmMinimizerCertificate`, `AlgorithmMaximizerCertificate`: pointwise
  optimality certificates for an algorithm together with an abstract
  operation-count bound.
- `AlgorithmMinimizerCertificate.of_lowerBoundCertificate`,
  `AlgorithmMaximizerCertificate.of_upperBoundCertificate`: lift pointwise
  ordinary bound certificates into algorithm certificates.
- `AlgorithmMinimizerCertificate.of_output_transform`,
  `AlgorithmMaximizerCertificate.of_output_transform`: lift algorithm
  certificates through feasible objective-preserving output transforms.
- `MinimizerOutputTransformCertificate`: certificate for an objective-preserving
  feasible transform of a minimization algorithm output.
- `componentwiseLowerBoundFill_isMinimizerOn`: exact componentwise lower-bound
  filling minimizes the sum of nonnegative integral allocations.
- `AlgorithmSoundnessCertificate`: pointwise specification certificate for an
  algorithm together with an abstract operation-count bound.
- `AlgorithmSoundnessCertificate.of_condition`: lift a checked condition plus
  a condition-to-specification bridge into a soundness certificate.
- `exists_feasible_objective_lt_of_replacement`: a deterministic replacement
  map gives a feasible strict-improvement witness.
- `exists_feasible_objective_lt_of_split_replacement`: two deterministic
  replacement maps, selected by a source split, give a feasible strict
  improvement witness.
- `exists_isMaximizerOn_of_isCompact_continuousOn`,
  `exists_isMinimizerOn_of_isCompact_continuousOn`: extreme-value theorem
  wrappers in the local `IsMaximizerOn`/`IsMinimizerOn` certificate language.
- `bddAbove_range_of_forall_le`: a pointwise upper bound yields boundedness of
  the objective range.
- `le_sSup_range`: any achieved value is at most the supremum of a bounded
  range.
- `sSup_range_eq_of_forall_le_of_exists_eq`: an attained upper bound is the
  supremum of the range.
-/

/-- Objective values achieved by feasible points. -/
def feasibleValueSet {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) : Set ℝ :=
  {v | ∃ x, feasible x ∧ v = objective x}

/--
An achieved value is bounded by the supremum of the range when that range is
bounded above.
-/
theorem le_sSup_range {α : Type*} (f : α → ℝ) (x : α)
    (hbdd : BddAbove (Set.range f)) :
    f x ≤ sSup (Set.range f) :=
  le_csSup hbdd (Set.mem_range_self x)

/--
Pointwise version of `le_sSup_range` for a family of functions.
-/
theorem le_sSup_range_apply {α β : Type*} (f : α → β → ℝ)
    (hbdd : ∀ a : α, BddAbove (Set.range (f a))) :
    ∀ a : α, ∀ b : β, f a b ≤ sSup (Set.range (f a)) := by
  intro a b
  exact le_sSup_range (f a) b (hbdd a)

/--
A pointwise upper bound gives boundedness above of the objective range.
-/
theorem bddAbove_range_of_forall_le {α : Type*} (f : α → ℝ) {M : ℝ}
    (hupper : ∀ x : α, f x ≤ M) :
    BddAbove (Set.range f) :=
  ⟨M, by
    rintro y ⟨x, rfl⟩
    exact hupper x⟩

/--
Pointwise version of `bddAbove_range_of_forall_le` for a family of functions.
-/
theorem bddAbove_range_apply_of_forall_le {α β : Type*}
    (f : α → β → ℝ) {M : α → ℝ}
    (hupper : ∀ a : α, ∀ b : β, f a b ≤ M a) :
    ∀ a : α, BddAbove (Set.range (f a)) := by
  intro a
  exact bddAbove_range_of_forall_le (f a) (hupper a)

/--
An upper bound that is attained is the supremum of the range.
-/
theorem sSup_range_eq_of_forall_le_of_exists_eq {α : Type*}
    (f : α → ℝ) {M : ℝ}
    (hupper : ∀ x : α, f x ≤ M)
    (hattain : ∃ x : α, f x = M) :
    sSup (Set.range f) = M := by
  rcases hattain with ⟨x0, hx0⟩
  have hbdd : BddAbove (Set.range f) := by
    exact bddAbove_range_of_forall_le f hupper
  apply le_antisymm
  · exact csSup_le ⟨f x0, Set.mem_range_self x0⟩
      (by
        rintro y ⟨x, rfl⟩
        exact hupper x)
  · rw [← hx0]
    exact le_sSup_range f x0 hbdd

/--
Pointwise version of `sSup_range_eq_of_forall_le_of_exists_eq` for a family of
functions.
-/
theorem sSup_range_apply_eq_of_forall_le_of_exists_eq {α β : Type*}
    (f : α → β → ℝ) {M : α → ℝ}
    (hupper : ∀ a : α, ∀ b : β, f a b ≤ M a)
    (hattain : ∀ a : α, ∃ b : β, f a b = M a) :
    ∀ a : α, sSup (Set.range (f a)) = M a := by
  intro a
  exact sSup_range_eq_of_forall_le_of_exists_eq
    (f a) (hupper a) (hattain a)

/-- `x` globally maximizes `objective`. -/
def IsGlobalMaximizer {α : Type*} (objective : α → ℝ) (x : α) : Prop :=
  ∀ y, objective y ≤ objective x

/-- `x` globally minimizes `objective`. -/
def IsGlobalMinimizer {α : Type*} (objective : α → ℝ) (x : α) : Prop :=
  ∀ y, objective x ≤ objective y

/-- `x` maximizes `objective` over the feasible region. -/
def IsMaximizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → objective y ≤ objective x

/-- `x` minimizes `objective` over the feasible region. -/
def IsMinimizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → objective x ≤ objective y

/-- Strict sufficient condition for a unique maximizer. -/
def IsStrictMaximizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → y ≠ x → objective y < objective x

/-- Strict sufficient condition for a unique minimizer. -/
def IsStrictMinimizerOn {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y → y ≠ x → objective x < objective y

/--
Extreme-value theorem in `IsMaximizerOn` form: a continuous real objective on
a nonempty compact feasible set attains a maximum.
-/
theorem exists_isMaximizerOn_of_isCompact_continuousOn
    {α : Type*} [TopologicalSpace α] {s : Set α} (hs : IsCompact s)
    (hne : s.Nonempty) (objective : α → ℝ)
    (hcont : ContinuousOn objective s) :
    ∃ opt : α, IsMaximizerOn (fun x => x ∈ s) objective opt := by
  rcases hs.exists_isMaxOn hne hcont with ⟨opt, hopt_mem, hopt⟩
  exact ⟨opt, hopt_mem, fun _y hy => hopt hy⟩

/--
Extreme-value theorem in `IsMinimizerOn` form: a continuous real objective on
a nonempty compact feasible set attains a minimum.
-/
theorem exists_isMinimizerOn_of_isCompact_continuousOn
    {α : Type*} [TopologicalSpace α] {s : Set α} (hs : IsCompact s)
    (hne : s.Nonempty) (objective : α → ℝ)
    (hcont : ContinuousOn objective s) :
    ∃ opt : α, IsMinimizerOn (fun x => x ∈ s) objective opt := by
  rcases hs.exists_isMinOn hne hcont with ⟨opt, hopt_mem, hopt⟩
  exact ⟨opt, hopt_mem, fun _y hy => hopt hy⟩

/--
`x` is lexicographically maximal: every feasible alternative has either a
strictly smaller primary objective, or the same primary objective and no larger
secondary objective.
-/
def IsLexicographicMaximizerOn {α : Type*} (feasible : α → Prop)
    (primary secondary : α → ℝ) (x : α) : Prop :=
  feasible x ∧ ∀ y, feasible y →
    primary y < primary x ∨
      (primary y = primary x ∧ secondary y ≤ secondary x)

namespace IsMaximizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

/-- A maximizer is feasible. -/
theorem isFeasible (h : IsMaximizerOn feasible objective x) : feasible x :=
  h.1

/-- A maximizer upper-bounds every feasible objective value. -/
theorem le (h : IsMaximizerOn feasible objective x)
    (hy : feasible y) : objective y ≤ objective x :=
  h.2 y hy

/-- No feasible point strictly improves on a maximizer. -/
theorem not_lt (h : IsMaximizerOn feasible objective x)
    (hy : feasible y) : ¬ objective x < objective y :=
  not_lt_of_ge (h.le hy)

/-- A point with a feasible strict improvement is not a maximizer. -/
theorem not_of_exists_objective_lt
    (hbetter : ∃ y, feasible y ∧ objective x < objective y) :
    ¬ IsMaximizerOn feasible objective x := by
  intro hmax
  rcases hbetter with ⟨y, hy, hlt⟩
  exact hmax.not_lt hy hlt

/--
A feasible point with no feasible strict improvement is a maximizer.
-/
theorem of_feasible_not_exists_objective_lt
    (hx : feasible x)
    (hno : ¬ ∃ y, feasible y ∧ objective x < objective y) :
    IsMaximizerOn feasible objective x := by
  refine ⟨hx, ?_⟩
  intro y hy
  by_contra hnot
  exact hno ⟨y, hy, lt_of_not_ge hnot⟩

/-- The objective value of a maximizer is in the feasible value set. -/
theorem value_mem_feasibleValueSet
    (h : IsMaximizerOn feasible objective x) :
    objective x ∈ feasibleValueSet feasible objective :=
  ⟨x, h.isFeasible, rfl⟩

/-- Any two maximizers have the same objective value. -/
theorem objective_eq_of_isMaximizerOn
    (hx : IsMaximizerOn feasible objective x)
    (hy : IsMaximizerOn feasible objective y) :
    objective x = objective y :=
  le_antisymm (hy.le hx.isFeasible) (hx.le hy.isFeasible)

end IsMaximizerOn

/--
Compact lexicographic extreme-value theorem.  A continuous primary objective
and a continuous secondary tie-breaker on a nonempty compact feasible set admit
a lexicographic maximizer: first maximize the primary objective, then maximize
the secondary objective on the primary-optimal fiber.
-/
theorem exists_isLexicographicMaximizerOn_of_isCompact_continuousOn
    {α : Type*} [TopologicalSpace α] [T2Space α] {s : Set α}
    (hs : IsCompact s) (hne : s.Nonempty) (primary secondary : α → ℝ)
    (hprimary : ContinuousOn primary s)
    (hsecondary : ContinuousOn secondary s) :
    ∃ opt : α,
      IsLexicographicMaximizerOn (fun x => x ∈ s) primary secondary opt := by
  rcases exists_isMaximizerOn_of_isCompact_continuousOn
      hs hne primary hprimary with
    ⟨primaryOpt, hprimaryOpt⟩
  let fiber : Set α := s ∩ primary ⁻¹' {primary primaryOpt}
  have hfiber_closed : IsClosed fiber := by
    simpa [fiber] using
      hprimary.preimage_isClosed_of_isClosed hs.isClosed
        (isClosed_singleton : IsClosed ({primary primaryOpt} : Set ℝ))
  have hfiber_compact : IsCompact fiber :=
    hs.of_isClosed_subset hfiber_closed (by
      intro x hx
      exact hx.1)
  have hfiber_nonempty : fiber.Nonempty :=
    ⟨primaryOpt, hprimaryOpt.isFeasible, by simp⟩
  have hsecondary_fiber : ContinuousOn secondary fiber :=
    hsecondary.mono (by
      intro x hx
      exact hx.1)
  rcases exists_isMaximizerOn_of_isCompact_continuousOn
      hfiber_compact hfiber_nonempty secondary hsecondary_fiber with
    ⟨opt, hopt⟩
  refine ⟨opt, ?_⟩
  have hopt_mem_s : opt ∈ s := hopt.isFeasible.1
  have hopt_primary : primary opt = primary primaryOpt := by
    simpa [fiber] using hopt.isFeasible.2
  refine ⟨hopt_mem_s, ?_⟩
  intro y hy
  by_cases hlt : primary y < primary opt
  · exact Or.inl hlt
  · have hy_le_primaryOpt : primary y ≤ primary primaryOpt :=
      hprimaryOpt.le hy
    have hy_le_opt : primary y ≤ primary opt := by
      simpa [hopt_primary] using hy_le_primaryOpt
    have hopt_le_y : primary opt ≤ primary y := le_of_not_gt hlt
    have heq : primary y = primary opt := le_antisymm hy_le_opt hopt_le_y
    refine Or.inr ⟨heq, ?_⟩
    exact hopt.le ⟨hy, by simpa [fiber, hopt_primary, heq]⟩

namespace IsLexicographicMaximizerOn

variable {α : Type*} {feasible : α → Prop}
  {primary secondary : α → ℝ} {x y : α}

/-- A lexicographic maximizer is feasible. -/
theorem isFeasible
    (h : IsLexicographicMaximizerOn feasible primary secondary x) :
    feasible x :=
  h.1

/-- Every feasible alternative is lexicographically dominated by the maximizer. -/
theorem le_or_tie_le
    (h : IsLexicographicMaximizerOn feasible primary secondary x)
    (hy : feasible y) :
    primary y < primary x ∨
      (primary y = primary x ∧ secondary y ≤ secondary x) :=
  h.2 y hy

end IsLexicographicMaximizerOn

/--
Primary optimality plus secondary optimality on the primary-optimal fiber gives
lexicographic optimality.  This is the reusable certificate pattern for papers
that first maximize a limiting objective and then maximize a convergence-rate
objective among limiting-objective maximizers.
-/
theorem isLexicographicMaximizerOn_of_primary_and_secondary_on_tie
    {α : Type*} {feasible : α → Prop} {primary secondary : α → ℝ} {x : α}
    (hprimary : IsMaximizerOn feasible primary x)
    (hsecondary :
      ∀ y, feasible y → primary y = primary x → secondary y ≤ secondary x) :
    IsLexicographicMaximizerOn feasible primary secondary x := by
  refine ⟨hprimary.isFeasible, ?_⟩
  intro y hy
  by_cases hlt : primary y < primary x
  · exact Or.inl hlt
  · have hle : primary y ≤ primary x := hprimary.le hy
    have hge : primary x ≤ primary y := le_of_not_gt hlt
    have heq : primary y = primary x := le_antisymm hle hge
    exact Or.inr ⟨heq, hsecondary y hy heq⟩

/--
Primary optimality plus an `IsMaximizerOn` certificate for the secondary
objective on the primary-optimal fiber gives lexicographic optimality.  This
is the source-shaped form of the common two-stage optimization argument.
-/
theorem isLexicographicMaximizerOn_of_primary_and_secondary_maximizer_on_tie
    {α : Type*} {feasible : α → Prop} {primary secondary : α → ℝ} {x : α}
    (hprimary : IsMaximizerOn feasible primary x)
    (hsecondary :
      IsMaximizerOn (fun y => feasible y ∧ primary y = primary x)
        secondary x) :
    IsLexicographicMaximizerOn feasible primary secondary x :=
  isLexicographicMaximizerOn_of_primary_and_secondary_on_tie hprimary
    (fun y hy heq => hsecondary.le ⟨hy, heq⟩)

namespace IsMinimizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

/-- A minimizer is feasible. -/
theorem isFeasible (h : IsMinimizerOn feasible objective x) : feasible x :=
  h.1

/-- A minimizer lower-bounds every feasible objective value. -/
theorem le (h : IsMinimizerOn feasible objective x)
    (hy : feasible y) : objective x ≤ objective y :=
  h.2 y hy

/-- No feasible point strictly improves on a minimizer. -/
theorem not_lt (h : IsMinimizerOn feasible objective x)
    (hy : feasible y) : ¬ objective y < objective x :=
  not_lt_of_ge (h.le hy)

/-- A point with a feasible strict improvement is not a minimizer. -/
theorem not_of_exists_objective_lt
    (hbetter : ∃ y, feasible y ∧ objective y < objective x) :
    ¬ IsMinimizerOn feasible objective x := by
  intro hmin
  rcases hbetter with ⟨y, hy, hlt⟩
  exact hmin.not_lt hy hlt

/--
A feasible point with no feasible strict improvement is a minimizer.
-/
theorem of_feasible_not_exists_objective_lt
    (hx : feasible x)
    (hno : ¬ ∃ y, feasible y ∧ objective y < objective x) :
    IsMinimizerOn feasible objective x := by
  refine ⟨hx, ?_⟩
  intro y hy
  by_contra hnot
  exact hno ⟨y, hy, lt_of_not_ge hnot⟩

/-- The objective value of a minimizer is in the feasible value set. -/
theorem value_mem_feasibleValueSet
    (h : IsMinimizerOn feasible objective x) :
    objective x ∈ feasibleValueSet feasible objective :=
  ⟨x, h.isFeasible, rfl⟩

/-- Any two minimizers have the same objective value. -/
theorem objective_eq_of_isMinimizerOn
    (hx : IsMinimizerOn feasible objective x)
    (hy : IsMinimizerOn feasible objective y) :
    objective x = objective y :=
  le_antisymm (hx.le hy.isFeasible) (hy.le hx.isFeasible)

end IsMinimizerOn

/--
A deterministic replacement map for bad feasible points gives an existential
strict-improvement witness.
-/
theorem exists_feasible_objective_lt_of_replacement
    {α : Type*} {feasible bad : α → Prop} {objective : α → ℝ}
    (replacement : ∀ x, feasible x → bad x → α)
    (replacement_feasible : ∀ x hx hbad,
      feasible (replacement x hx hbad))
    (replacement_objective_lt : ∀ x hx hbad,
      objective (replacement x hx hbad) < objective x) :
    ∀ x, feasible x → bad x → ∃ y, feasible y ∧ objective y < objective x := by
  intro x hx hbad
  exact ⟨replacement x hx hbad,
    replacement_feasible x hx hbad,
    replacement_objective_lt x hx hbad⟩

/--
Two deterministic replacement maps, selected by a source-level split of the
bad cases, give an existential strict-improvement witness.
-/
theorem exists_feasible_objective_lt_of_split_replacement
    {α : Type*}
    {feasible bad leftCase rightCase : α → Prop} {objective : α → ℝ}
    (split : ∀ x, feasible x → bad x → leftCase x ∨ rightCase x)
    (leftReplacement : ∀ x, feasible x → bad x → leftCase x → α)
    (leftReplacement_feasible : ∀ x hx hbad hleft,
      feasible (leftReplacement x hx hbad hleft))
    (leftReplacement_objective_lt : ∀ x hx hbad hleft,
      objective (leftReplacement x hx hbad hleft) < objective x)
    (rightReplacement : ∀ x, feasible x → bad x → rightCase x → α)
    (rightReplacement_feasible : ∀ x hx hbad hright,
      feasible (rightReplacement x hx hbad hright))
    (rightReplacement_objective_lt : ∀ x hx hbad hright,
      objective (rightReplacement x hx hbad hright) < objective x) :
    ∀ x, feasible x → bad x → ∃ y, feasible y ∧ objective y < objective x := by
  intro x hx hbad
  rcases split x hx hbad with hleft | hright
  · exact ⟨leftReplacement x hx hbad hleft,
      leftReplacement_feasible x hx hbad hleft,
      leftReplacement_objective_lt x hx hbad hleft⟩
  · exact ⟨rightReplacement x hx hbad hright,
      rightReplacement_feasible x hx hbad hright,
      rightReplacement_objective_lt x hx hbad hright⟩

namespace IsStrictMaximizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

/-- A strict maximizer is feasible. -/
theorem isFeasible (h : IsStrictMaximizerOn feasible objective x) :
    feasible x :=
  h.1

/-- Every other feasible point has strictly smaller value than a strict maximizer. -/
theorem lt_of_ne (h : IsStrictMaximizerOn feasible objective x)
    (hy : feasible y) (hne : y ≠ x) : objective y < objective x :=
  h.2 y hy hne

/-- Strict maximization implies weak maximization. -/
theorem isMaximizerOn
    (h : IsStrictMaximizerOn feasible objective x) :
    IsMaximizerOn feasible objective x := by
  constructor
  · exact h.isFeasible
  · intro y hy
    by_cases hxy : y = x
    · subst y
      exact le_rfl
    · exact le_of_lt (h.lt_of_ne hy hxy)

/-- A strict maximizer is the only weak maximizer. -/
theorem eq_of_isMaximizerOn
    (h : IsStrictMaximizerOn feasible objective x)
    (hy : IsMaximizerOn feasible objective y) : y = x := by
  by_contra hne
  exact hy.not_lt h.isFeasible (h.lt_of_ne hy.isFeasible hne)

end IsStrictMaximizerOn

namespace IsStrictMinimizerOn

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {x y : α}

/-- A strict minimizer is feasible. -/
theorem isFeasible (h : IsStrictMinimizerOn feasible objective x) :
    feasible x :=
  h.1

/-- Every other feasible point has strictly larger value than a strict minimizer. -/
theorem lt_of_ne (h : IsStrictMinimizerOn feasible objective x)
    (hy : feasible y) (hne : y ≠ x) : objective x < objective y :=
  h.2 y hy hne

/-- Strict minimization implies weak minimization. -/
theorem isMinimizerOn
    (h : IsStrictMinimizerOn feasible objective x) :
    IsMinimizerOn feasible objective x := by
  constructor
  · exact h.isFeasible
  · intro y hy
    by_cases hxy : y = x
    · subst y
      exact le_rfl
    · exact le_of_lt (h.lt_of_ne hy hxy)

/-- A strict minimizer is the only weak minimizer. -/
theorem eq_of_isMinimizerOn
    (h : IsStrictMinimizerOn feasible objective x)
    (hy : IsMinimizerOn feasible objective y) : y = x := by
  by_contra hne
  exact hy.not_lt h.isFeasible (h.lt_of_ne hy.isFeasible hne)

end IsStrictMinimizerOn

/--
A maximization certificate: the candidate is feasible, has value `value`, and
`value` upper-bounds every feasible objective value.
-/
structure UpperBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  upper_bound : ∀ y, feasible y → objective y ≤ value

/--
A minimization certificate: the candidate is feasible, has value `value`, and
`value` lower-bounds every feasible objective value.
-/
structure LowerBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  lower_bound : ∀ y, feasible y → value ≤ objective y

/-- A strict maximization certificate proving uniqueness by strict upper bounds. -/
structure StrictUpperBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  strict_upper_bound : ∀ y, feasible y → y ≠ candidate → objective y < value

/-- A strict minimization certificate proving uniqueness by strict lower bounds. -/
structure StrictLowerBoundCertificate {α : Type*} (feasible : α → Prop)
    (objective : α → ℝ) (value : ℝ) where
  candidate : α
  candidate_feasible : feasible candidate
  candidate_value : objective candidate = value
  strict_lower_bound : ∀ y, feasible y → y ≠ candidate → value < objective y

namespace UpperBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

/-- The certified value is achieved by a feasible point. -/
theorem value_mem_feasibleValueSet
    (cert : UpperBoundCertificate feasible objective value) :
    value ∈ feasibleValueSet feasible objective := by
  exact ⟨cert.candidate, cert.candidate_feasible, cert.candidate_value.symm⟩

/-- Every feasible value is at most the certified value. -/
theorem le_value_of_mem_feasibleValueSet
    (cert : UpperBoundCertificate feasible objective value)
    {v : ℝ} (hv : v ∈ feasibleValueSet feasible objective) : v ≤ value := by
  rcases hv with ⟨x, hx, hvx⟩
  rw [hvx]
  exact cert.upper_bound x hx

/-- The feasible value set is bounded above by the certified value. -/
theorem bddAbove_feasibleValueSet
    (cert : UpperBoundCertificate feasible objective value) :
    BddAbove (feasibleValueSet feasible objective) :=
  ⟨value, fun _v hv => cert.le_value_of_mem_feasibleValueSet hv⟩

/-- A maximization certificate proves candidate optimality. -/
theorem isMaximizerOn
    (cert : UpperBoundCertificate feasible objective value) :
    IsMaximizerOn feasible objective cert.candidate := by
  constructor
  · exact cert.candidate_feasible
  · intro y hy
    simpa [cert.candidate_value] using cert.upper_bound y hy

/-- Any maximizer has the certified objective value. -/
theorem objective_eq_value_of_isMaximizerOn
    (cert : UpperBoundCertificate feasible objective value)
    {y : α} (hy : IsMaximizerOn feasible objective y) :
    objective y = value := by
  have hle : objective y ≤ value := cert.upper_bound y hy.isFeasible
  have hge : value ≤ objective y := by
    rw [← cert.candidate_value]
    exact hy.le cert.candidate_feasible
  exact le_antisymm hle hge

end UpperBoundCertificate

namespace LowerBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

/-- The certified value is achieved by a feasible point. -/
theorem value_mem_feasibleValueSet
    (cert : LowerBoundCertificate feasible objective value) :
    value ∈ feasibleValueSet feasible objective := by
  exact ⟨cert.candidate, cert.candidate_feasible, cert.candidate_value.symm⟩

/-- Every feasible value is at least the certified value. -/
theorem value_le_of_mem_feasibleValueSet
    (cert : LowerBoundCertificate feasible objective value)
    {v : ℝ} (hv : v ∈ feasibleValueSet feasible objective) : value ≤ v := by
  rcases hv with ⟨x, hx, hvx⟩
  rw [hvx]
  exact cert.lower_bound x hx

/-- The feasible value set is bounded below by the certified value. -/
theorem bddBelow_feasibleValueSet
    (cert : LowerBoundCertificate feasible objective value) :
    BddBelow (feasibleValueSet feasible objective) :=
  ⟨value, fun _v hv => cert.value_le_of_mem_feasibleValueSet hv⟩

/-- A minimization certificate proves candidate optimality. -/
theorem isMinimizerOn
    (cert : LowerBoundCertificate feasible objective value) :
    IsMinimizerOn feasible objective cert.candidate := by
  constructor
  · exact cert.candidate_feasible
  · intro y hy
    simpa [cert.candidate_value] using cert.lower_bound y hy

/-- Any minimizer has the certified objective value. -/
theorem objective_eq_value_of_isMinimizerOn
    (cert : LowerBoundCertificate feasible objective value)
    {y : α} (hy : IsMinimizerOn feasible objective y) :
    objective y = value := by
  have hge : value ≤ objective y := cert.lower_bound y hy.isFeasible
  have hle : objective y ≤ value := by
    rw [← cert.candidate_value]
    exact hy.le cert.candidate_feasible
  exact le_antisymm hle hge

end LowerBoundCertificate

namespace StrictUpperBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

/-- Forget strictness to obtain an ordinary maximization certificate. -/
def toUpperBoundCertificate
    (cert : StrictUpperBoundCertificate feasible objective value) :
    UpperBoundCertificate feasible objective value where
  candidate := cert.candidate
  candidate_feasible := cert.candidate_feasible
  candidate_value := cert.candidate_value
  upper_bound := by
    intro y hy
    by_cases h : y = cert.candidate
    · subst y
      exact le_of_eq cert.candidate_value
    · exact le_of_lt (cert.strict_upper_bound y hy h)

/-- A strict maximization certificate proves strict candidate optimality. -/
theorem isStrictMaximizerOn
    (cert : StrictUpperBoundCertificate feasible objective value) :
    IsStrictMaximizerOn feasible objective cert.candidate := by
  constructor
  · exact cert.candidate_feasible
  · intro y hy hne
    simpa [cert.candidate_value] using cert.strict_upper_bound y hy hne

/-- A strict maximization certificate also proves weak candidate optimality. -/
theorem isMaximizerOn
    (cert : StrictUpperBoundCertificate feasible objective value) :
    IsMaximizerOn feasible objective cert.candidate :=
  cert.toUpperBoundCertificate.isMaximizerOn

/-- A strict maximization certificate identifies every weak maximizer. -/
theorem eq_of_isMaximizerOn
    (cert : StrictUpperBoundCertificate feasible objective value)
    {y : α} (hy : IsMaximizerOn feasible objective y) : y = cert.candidate :=
  cert.isStrictMaximizerOn.eq_of_isMaximizerOn hy

end StrictUpperBoundCertificate

namespace StrictLowerBoundCertificate

variable {α : Type*} {feasible : α → Prop} {objective : α → ℝ}
  {value : ℝ}

/-- Forget strictness to obtain an ordinary minimization certificate. -/
def toLowerBoundCertificate
    (cert : StrictLowerBoundCertificate feasible objective value) :
    LowerBoundCertificate feasible objective value where
  candidate := cert.candidate
  candidate_feasible := cert.candidate_feasible
  candidate_value := cert.candidate_value
  lower_bound := by
    intro y hy
    by_cases h : y = cert.candidate
    · subst y
      exact le_of_eq cert.candidate_value.symm
    · exact le_of_lt (cert.strict_lower_bound y hy h)

/-- A strict minimization certificate proves strict candidate optimality. -/
theorem isStrictMinimizerOn
    (cert : StrictLowerBoundCertificate feasible objective value) :
    IsStrictMinimizerOn feasible objective cert.candidate := by
  constructor
  · exact cert.candidate_feasible
  · intro y hy hne
    simpa [cert.candidate_value] using cert.strict_lower_bound y hy hne

/-- A strict minimization certificate also proves weak candidate optimality. -/
theorem isMinimizerOn
    (cert : StrictLowerBoundCertificate feasible objective value) :
    IsMinimizerOn feasible objective cert.candidate :=
  cert.toLowerBoundCertificate.isMinimizerOn

/-- A strict minimization certificate identifies every weak minimizer. -/
theorem eq_of_isMinimizerOn
    (cert : StrictLowerBoundCertificate feasible objective value)
    {y : α} (hy : IsMinimizerOn feasible objective y) : y = cert.candidate :=
  cert.isStrictMinimizerOn.eq_of_isMinimizerOn hy

end StrictLowerBoundCertificate

/--
A pointwise certificate that an algorithm returns a minimizer and satisfies an
abstract operation-count bound.

The operation model is deliberately a parameter: downstream modules can use
Turing-machine time, comparison counts, arithmetic-operation counts, or
application-level pseudocode costs while reusing the same optimality wrapper.
-/
structure AlgorithmMinimizerCertificate {Input Output : Type*}
    (algorithm : Input → Output)
    (feasible : Input → Output → Prop)
    (objective : Input → Output → ℝ)
    (operationCount operationBound : Input → ℕ) where
  optimal : ∀ input, IsMinimizerOn (feasible input) (objective input) (algorithm input)
  operationCount_le : ∀ input, operationCount input ≤ operationBound input

/--
A pointwise certificate that an algorithm returns a maximizer and satisfies an
abstract operation-count bound.
-/
structure AlgorithmMaximizerCertificate {Input Output : Type*}
    (algorithm : Input → Output)
    (feasible : Input → Output → Prop)
    (objective : Input → Output → ℝ)
    (operationCount operationBound : Input → ℕ) where
  optimal : ∀ input, IsMaximizerOn (feasible input) (objective input) (algorithm input)
  operationCount_le : ∀ input, operationCount input ≤ operationBound input

/--
A pointwise certificate that an algorithm's output satisfies a specification
and has an abstract operation-count bound.

Use this for soundness claims that are not optimization problems, such as
preprocessing, reduction, feasibility filtering, or verified transformations.
-/
structure AlgorithmSoundnessCertificate {Input Output : Type*}
    (algorithm : Input → Output)
    (specification : Input → Output → Prop)
    (operationCount operationBound : Input → ℕ) where
  sound : ∀ input, specification input (algorithm input)
  operationCount_le : ∀ input, operationCount input ≤ operationBound input

/--
Certificate for a feasible, objective-preserving transform of a minimization
algorithm's output.

This packages the common pattern used by robust-output and postprocessing
arguments: a base algorithm is already certified optimal, the transformed
output is feasible and has the same objective value on every input, and the
transformed implementation satisfies the advertised operation-count bound.
-/
structure MinimizerOutputTransformCertificate {Input Output : Type*}
    (baseAlgorithm transformedAlgorithm : Input → Output)
    (feasible : Input → Output → Prop)
    (objective : Input → Output → ℝ)
    (baseOperationCount transformedOperationCount operationBound :
      Input → ℕ) where
  baseCert :
    AlgorithmMinimizerCertificate baseAlgorithm feasible objective
      baseOperationCount operationBound
  transformed_feasible :
    ∀ input, feasible input (transformedAlgorithm input)
  transformed_objective_eq :
    ∀ input,
      objective input (transformedAlgorithm input) =
        objective input (baseAlgorithm input)
  transformedOperationCount_le :
    ∀ input, transformedOperationCount input ≤ operationBound input

namespace AlgorithmMinimizerCertificate

variable {Input Output : Type*} {algorithm : Input → Output}
  {feasible : Input → Output → Prop} {objective : Input → Output → ℝ}
  {operationCount operationBound : Input → ℕ}

/--
Build an algorithm minimization certificate from source-shaped output
feasibility, objective lower-bound, and operation-count fields.
-/
theorem of_output_feasible_objective_le
    (output_feasible : ∀ input, feasible input (algorithm input))
    (objective_le : ∀ input output, feasible input output →
      objective input (algorithm input) ≤ objective input output)
    (operationCount_le : ∀ input, operationCount input ≤ operationBound input) :
    AlgorithmMinimizerCertificate algorithm feasible objective
      operationCount operationBound where
  optimal := by
    intro input
    exact ⟨output_feasible input, objective_le input⟩
  operationCount_le := operationCount_le

/--
Build an algorithm minimization certificate from output feasibility, absence
of any feasible lower-objective output, and operation-count fields.
-/
theorem of_output_feasible_not_exists_objective_lt
    (output_feasible : ∀ input, feasible input (algorithm input))
    (not_exists_objective_lt : ∀ input,
      ¬ ∃ output, feasible input output ∧
        objective input output < objective input (algorithm input))
    (operationCount_le : ∀ input, operationCount input ≤ operationBound input) :
    AlgorithmMinimizerCertificate algorithm feasible objective
      operationCount operationBound where
  optimal := by
    intro input
    exact IsMinimizerOn.of_feasible_not_exists_objective_lt
      (output_feasible input) (not_exists_objective_lt input)
  operationCount_le := operationCount_le

/--
Build an algorithm minimization certificate from pointwise lower-bound
certificates whose certified candidate is the algorithm output.
-/
theorem of_lowerBoundCertificate
    (value : Input → ℝ)
    (lowerBoundCert : ∀ input,
      LowerBoundCertificate (feasible input) (objective input) (value input))
    (candidate_eq : ∀ input, (lowerBoundCert input).candidate = algorithm input)
    (operationCount_le : ∀ input, operationCount input ≤ operationBound input) :
    AlgorithmMinimizerCertificate algorithm feasible objective
      operationCount operationBound where
  optimal := by
    intro input
    simpa [candidate_eq input] using (lowerBoundCert input).isMinimizerOn
  operationCount_le := operationCount_le

/--
Lift a minimization certificate through an output transform that preserves the
objective value of the certified output and returns a feasible transformed
output.
-/
theorem of_output_transform
    {transformedAlgorithm : Input → Output}
    {transformedOperationCount : Input → ℕ}
    (cert :
      AlgorithmMinimizerCertificate algorithm feasible objective
        operationCount operationBound)
    (transformed_feasible : ∀ input, feasible input (transformedAlgorithm input))
    (transformed_objective_eq : ∀ input,
      objective input (transformedAlgorithm input) =
        objective input (algorithm input))
    (transformedOperationCount_le :
      ∀ input, transformedOperationCount input ≤ operationBound input) :
    AlgorithmMinimizerCertificate transformedAlgorithm feasible objective
      transformedOperationCount operationBound where
  optimal := by
    intro input
    refine ⟨transformed_feasible input, ?_⟩
    intro output houtput
    rw [transformed_objective_eq input]
    exact (cert.optimal input).le houtput
  operationCount_le := transformedOperationCount_le

/-- The certified algorithm output is feasible for each input. -/
theorem output_feasible
    (cert :
      AlgorithmMinimizerCertificate algorithm feasible objective
        operationCount operationBound)
    (input : Input) :
    feasible input (algorithm input) :=
  (cert.optimal input).isFeasible

/-- The certified algorithm output weakly minimizes the objective for each input. -/
theorem objective_le
    (cert :
      AlgorithmMinimizerCertificate algorithm feasible objective
        operationCount operationBound)
    (input : Input) {output : Output}
    (houtput : feasible input output) :
    objective input (algorithm input) ≤ objective input output :=
  (cert.optimal input).le houtput

end AlgorithmMinimizerCertificate

namespace MinimizerOutputTransformCertificate

variable {Input Output : Type*}
  {baseAlgorithm transformedAlgorithm : Input → Output}
  {feasible : Input → Output → Prop} {objective : Input → Output → ℝ}
  {baseOperationCount transformedOperationCount operationBound : Input → ℕ}

/--
A minimizer output-transform certificate gives the reusable algorithm
certificate for the transformed algorithm.
-/
theorem algorithmCertificate
    (cert :
      MinimizerOutputTransformCertificate baseAlgorithm transformedAlgorithm
        feasible objective baseOperationCount transformedOperationCount
        operationBound) :
    AlgorithmMinimizerCertificate transformedAlgorithm feasible objective
      transformedOperationCount operationBound :=
  AlgorithmMinimizerCertificate.of_output_transform
    cert.baseCert cert.transformed_feasible cert.transformed_objective_eq
    cert.transformedOperationCount_le

/--
Pointwise optimality and operation-count projection from a minimizer
output-transform certificate.
-/
theorem optimal_and_operationCount
    (cert :
      MinimizerOutputTransformCertificate baseAlgorithm transformedAlgorithm
        feasible objective baseOperationCount transformedOperationCount
        operationBound) :
    ∀ input,
      IsMinimizerOn
          (feasible input) (objective input) (transformedAlgorithm input) ∧
        transformedOperationCount input ≤ operationBound input := by
  intro input
  let transformedCert :=
    algorithmCertificate cert
  exact ⟨transformedCert.optimal input,
    transformedCert.operationCount_le input⟩

end MinimizerOutputTransformCertificate

namespace AlgorithmMaximizerCertificate

variable {Input Output : Type*} {algorithm : Input → Output}
  {feasible : Input → Output → Prop} {objective : Input → Output → ℝ}
  {operationCount operationBound : Input → ℕ}

/--
Build an algorithm maximization certificate from source-shaped output
feasibility, objective upper-bound, and operation-count fields.
-/
theorem of_output_feasible_objective_le_output
    (output_feasible : ∀ input, feasible input (algorithm input))
    (objective_le_output : ∀ input output, feasible input output →
      objective input output ≤ objective input (algorithm input))
    (operationCount_le : ∀ input, operationCount input ≤ operationBound input) :
    AlgorithmMaximizerCertificate algorithm feasible objective
      operationCount operationBound where
  optimal := by
    intro input
    exact ⟨output_feasible input, objective_le_output input⟩
  operationCount_le := operationCount_le

/--
Build an algorithm maximization certificate from output feasibility, absence
of any feasible higher-objective output, and operation-count fields.
-/
theorem of_output_feasible_not_exists_objective_lt
    (output_feasible : ∀ input, feasible input (algorithm input))
    (not_exists_objective_lt : ∀ input,
      ¬ ∃ output, feasible input output ∧
        objective input (algorithm input) < objective input output)
    (operationCount_le : ∀ input, operationCount input ≤ operationBound input) :
    AlgorithmMaximizerCertificate algorithm feasible objective
      operationCount operationBound where
  optimal := by
    intro input
    exact IsMaximizerOn.of_feasible_not_exists_objective_lt
      (output_feasible input) (not_exists_objective_lt input)
  operationCount_le := operationCount_le

/--
Build an algorithm maximization certificate from pointwise upper-bound
certificates whose certified candidate is the algorithm output.
-/
theorem of_upperBoundCertificate
    (value : Input → ℝ)
    (upperBoundCert : ∀ input,
      UpperBoundCertificate (feasible input) (objective input) (value input))
    (candidate_eq : ∀ input, (upperBoundCert input).candidate = algorithm input)
    (operationCount_le : ∀ input, operationCount input ≤ operationBound input) :
    AlgorithmMaximizerCertificate algorithm feasible objective
      operationCount operationBound where
  optimal := by
    intro input
    simpa [candidate_eq input] using (upperBoundCert input).isMaximizerOn
  operationCount_le := operationCount_le

/--
Lift a maximization certificate through an output transform that preserves the
objective value of the certified output and returns a feasible transformed
output.
-/
theorem of_output_transform
    {transformedAlgorithm : Input → Output}
    {transformedOperationCount : Input → ℕ}
    (cert :
      AlgorithmMaximizerCertificate algorithm feasible objective
        operationCount operationBound)
    (transformed_feasible : ∀ input, feasible input (transformedAlgorithm input))
    (transformed_objective_eq : ∀ input,
      objective input (transformedAlgorithm input) =
        objective input (algorithm input))
    (transformedOperationCount_le :
      ∀ input, transformedOperationCount input ≤ operationBound input) :
    AlgorithmMaximizerCertificate transformedAlgorithm feasible objective
      transformedOperationCount operationBound where
  optimal := by
    intro input
    refine ⟨transformed_feasible input, ?_⟩
    intro output houtput
    rw [transformed_objective_eq input]
    exact (cert.optimal input).le houtput
  operationCount_le := transformedOperationCount_le

/-- The certified algorithm output is feasible for each input. -/
theorem output_feasible
    (cert :
      AlgorithmMaximizerCertificate algorithm feasible objective
        operationCount operationBound)
    (input : Input) :
    feasible input (algorithm input) :=
  (cert.optimal input).isFeasible

/-- The certified algorithm output weakly maximizes the objective for each input. -/
theorem objective_le_output
    (cert :
      AlgorithmMaximizerCertificate algorithm feasible objective
        operationCount operationBound)
    (input : Input) {output : Output}
    (houtput : feasible input output) :
    objective input output ≤ objective input (algorithm input) :=
  (cert.optimal input).le houtput

end AlgorithmMaximizerCertificate

namespace AlgorithmSoundnessCertificate

variable {Input Output : Type*} {algorithm : Input → Output}
  {specification : Input → Output → Prop}
  {operationCount operationBound : Input → ℕ}

/--
Build an algorithm soundness certificate from source-shaped output-spec and
operation-count fields.
-/
theorem of_output_spec
    (output_spec : ∀ input, specification input (algorithm input))
    (operationCount_le : ∀ input, operationCount input ≤ operationBound input) :
    AlgorithmSoundnessCertificate algorithm specification
      operationCount operationBound where
  sound := output_spec
  operationCount_le := operationCount_le

/--
Build an algorithm soundness certificate from a checked condition and a bridge
from that condition to the requested output specification.
-/
theorem of_condition
    (condition : Input → Prop)
    (condition_holds : ∀ input, condition input)
    (output_spec_of_condition :
      ∀ input, condition input → specification input (algorithm input))
    (operationCount_le : ∀ input, operationCount input ≤ operationBound input) :
    AlgorithmSoundnessCertificate algorithm specification
      operationCount operationBound :=
  of_output_spec
    (fun input => output_spec_of_condition input (condition_holds input))
    operationCount_le

/-- The certified algorithm output satisfies the requested specification. -/
theorem output_spec
    (cert :
      AlgorithmSoundnessCertificate algorithm specification
        operationCount operationBound)
    (input : Input) :
    specification input (algorithm input) :=
  cert.sound input

end AlgorithmSoundnessCertificate

/-! ## Componentwise lower-bound filling -/

/--
Feasibility predicate for allocation problems where every component must meet
a nonnegative lower bound.
-/
def componentwiseLowerBoundFeasible {ι : Type*}
    (lower allocation : ι → ℕ) : Prop :=
  ∀ i, lower i ≤ allocation i

/-- Total cost of a finite vector of nonnegative integral allocations. -/
def componentwiseNatCost {ι : Type*} [Fintype ι]
    (allocation : ι → ℕ) : ℝ :=
  ∑ i, (allocation i : ℝ)

/-- The allocation that fills every component exactly to its lower bound. -/
def componentwiseLowerBoundFill {ι : Type*} (lower : ι → ℕ) : ι → ℕ :=
  lower

/--
Any feasible componentwise allocation has total cost at least the exact lower
bound fill.
-/
theorem componentwiseNatCost_le_of_componentwiseLowerBoundFeasible
    {ι : Type*} [Fintype ι] {lower allocation : ι → ℕ}
    (hfeasible : componentwiseLowerBoundFeasible lower allocation) :
    componentwiseNatCost lower ≤ componentwiseNatCost allocation := by
  unfold componentwiseNatCost
  exact Finset.sum_le_sum (by
    intro i _hi
    exact_mod_cast hfeasible i)

/--
Exact componentwise lower-bound filling gives a minimization lower-bound
certificate for total allocation cost.
-/
def componentwiseLowerBoundFill_lowerBoundCertificate
    {ι : Type*} [Fintype ι] (lower : ι → ℕ) :
    LowerBoundCertificate
      (componentwiseLowerBoundFeasible lower)
      componentwiseNatCost
      (componentwiseNatCost (componentwiseLowerBoundFill lower)) where
  candidate := componentwiseLowerBoundFill lower
  candidate_feasible := by
    intro i
    exact le_rfl
  candidate_value := rfl
  lower_bound := by
    intro allocation hfeasible
    exact componentwiseNatCost_le_of_componentwiseLowerBoundFeasible hfeasible

/--
Exact componentwise lower-bound filling minimizes total allocation cost among
all allocations that meet the componentwise lower bounds.
-/
theorem componentwiseLowerBoundFill_isMinimizerOn
    {ι : Type*} [Fintype ι] (lower : ι → ℕ) :
    IsMinimizerOn
      (componentwiseLowerBoundFeasible lower)
      componentwiseNatCost
      (componentwiseLowerBoundFill lower) :=
  (componentwiseLowerBoundFill_lowerBoundCertificate lower).isMinimizerOn

end Optimization
end AppliedModelingLib
