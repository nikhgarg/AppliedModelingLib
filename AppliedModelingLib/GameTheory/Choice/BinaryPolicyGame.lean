import Mathlib.Data.Real.Basic

namespace AppliedModelingLib

/-!
# Two-Player Binary Policy Games

Reusable normal-form bookkeeping for two players who each choose one of two
distinguished policies.

## Main declarations

- `TwoPlayerBinaryPolicyEquilibrium`
- `twoPlayerBinaryPolicyEquilibrium_lowHigh_iff`
- `twoPlayerBinaryPolicyEquilibrium_highLow_iff`
- `twoPlayerBinaryPolicyEquilibrium_highHigh_iff`
- `twoPlayerBinaryPolicyEquilibrium_lowLow_iff`
- `TwoPlayerBinaryPolicyFeasibleEquilibrium`
- `policy_pair_objective_le_iff_of_value_eq`
-/

/--
Binary-policy equilibrium for two players.  Each player weakly prefers the
current policy to the other distinguished policy, holding the other player's
policy fixed.
-/
def TwoPlayerBinaryPolicyEquilibrium
    {Policy : Type*} (objective1 objective2 : Policy → Policy → ℝ)
    (lowPolicy highPolicy current1 current2 : Policy) : Prop :=
  (∀ P1' : Policy, P1' = lowPolicy ∨ P1' = highPolicy →
    objective1 P1' current2 ≤ objective1 current1 current2) ∧
    (∀ P2' : Policy, P2' = lowPolicy ∨ P2' = highPolicy →
      objective2 current1 P2' ≤ objective2 current1 current2)

/-- Binary-policy equilibrium characterization for `(low, low)`. -/
theorem twoPlayerBinaryPolicyEquilibrium_lowLow_iff
    {Policy : Type*} (objective1 objective2 : Policy → Policy → ℝ)
    (lowPolicy highPolicy : Policy) :
    TwoPlayerBinaryPolicyEquilibrium objective1 objective2
        lowPolicy highPolicy lowPolicy lowPolicy ↔
      objective1 highPolicy lowPolicy ≤ objective1 lowPolicy lowPolicy ∧
        objective2 lowPolicy highPolicy ≤ objective2 lowPolicy lowPolicy := by
  constructor
  · intro h
    exact ⟨h.1 highPolicy (Or.inr rfl), h.2 highPolicy (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩
    constructor
    · intro P1' hmem
      rcases hmem with rfl | rfl
      · exact le_rfl
      · exact h1
    · intro P2' hmem
      rcases hmem with rfl | rfl
      · exact le_rfl
      · exact h2

/-- Binary-policy equilibrium characterization for `(low, high)`. -/
theorem twoPlayerBinaryPolicyEquilibrium_lowHigh_iff
    {Policy : Type*} (objective1 objective2 : Policy → Policy → ℝ)
    (lowPolicy highPolicy : Policy) :
    TwoPlayerBinaryPolicyEquilibrium objective1 objective2
        lowPolicy highPolicy lowPolicy highPolicy ↔
      objective1 highPolicy highPolicy ≤ objective1 lowPolicy highPolicy ∧
        objective2 lowPolicy lowPolicy ≤ objective2 lowPolicy highPolicy := by
  constructor
  · intro h
    exact ⟨h.1 highPolicy (Or.inr rfl), h.2 lowPolicy (Or.inl rfl)⟩
  · rintro ⟨h1, h2⟩
    constructor
    · intro P1' hmem
      rcases hmem with rfl | rfl
      · exact le_rfl
      · exact h1
    · intro P2' hmem
      rcases hmem with rfl | rfl
      · exact h2
      · exact le_rfl

/-- Binary-policy equilibrium characterization for `(high, low)`. -/
theorem twoPlayerBinaryPolicyEquilibrium_highLow_iff
    {Policy : Type*} (objective1 objective2 : Policy → Policy → ℝ)
    (lowPolicy highPolicy : Policy) :
    TwoPlayerBinaryPolicyEquilibrium objective1 objective2
        lowPolicy highPolicy highPolicy lowPolicy ↔
      objective1 lowPolicy lowPolicy ≤ objective1 highPolicy lowPolicy ∧
        objective2 highPolicy highPolicy ≤ objective2 highPolicy lowPolicy := by
  constructor
  · intro h
    exact ⟨h.1 lowPolicy (Or.inl rfl), h.2 highPolicy (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩
    constructor
    · intro P1' hmem
      rcases hmem with rfl | rfl
      · exact h1
      · exact le_rfl
    · intro P2' hmem
      rcases hmem with rfl | rfl
      · exact le_rfl
      · exact h2

/-- Binary-policy equilibrium characterization for `(high, high)`. -/
theorem twoPlayerBinaryPolicyEquilibrium_highHigh_iff
    {Policy : Type*} (objective1 objective2 : Policy → Policy → ℝ)
    (lowPolicy highPolicy : Policy) :
    TwoPlayerBinaryPolicyEquilibrium objective1 objective2
        lowPolicy highPolicy highPolicy highPolicy ↔
      objective1 lowPolicy highPolicy ≤ objective1 highPolicy highPolicy ∧
        objective2 highPolicy lowPolicy ≤ objective2 highPolicy highPolicy := by
  constructor
  · intro h
    exact ⟨h.1 lowPolicy (Or.inl rfl), h.2 lowPolicy (Or.inl rfl)⟩
  · rintro ⟨h1, h2⟩
    constructor
    · intro P1' hmem
      rcases hmem with rfl | rfl
      · exact h1
      · exact le_rfl
    · intro P2' hmem
      rcases hmem with rfl | rfl
      · exact h2
      · exact le_rfl

/--
Binary-policy equilibrium with policy-pair feasibility.  Each player must be
feasible at the current policy pair, and unilateral deviations are compared
only when the deviating pair is feasible for that player.
-/
def TwoPlayerBinaryPolicyFeasibleEquilibrium
    {Policy : Type*} (objective1 objective2 : Policy → Policy → ℝ)
    (feasible1 feasible2 : Policy → Policy → Prop)
    (lowPolicy highPolicy current1 current2 : Policy) : Prop :=
  feasible1 current1 current2 ∧
    feasible2 current1 current2 ∧
      (∀ P1' : Policy, P1' = lowPolicy ∨ P1' = highPolicy →
        feasible1 P1' current2 →
          objective1 P1' current2 ≤ objective1 current1 current2) ∧
        (∀ P2' : Policy, P2' = lowPolicy ∨ P2' = highPolicy →
          feasible2 current1 P2' →
            objective2 current1 P2' ≤ objective2 current1 current2)

/-- Feasible binary-policy equilibrium characterization for `(low, low)`. -/
theorem twoPlayerBinaryPolicyFeasibleEquilibrium_lowLow_iff
    {Policy : Type*} (objective1 objective2 : Policy → Policy → ℝ)
    (feasible1 feasible2 : Policy → Policy → Prop)
    (lowPolicy highPolicy : Policy) :
    TwoPlayerBinaryPolicyFeasibleEquilibrium objective1 objective2
        feasible1 feasible2 lowPolicy highPolicy lowPolicy lowPolicy ↔
      feasible1 lowPolicy lowPolicy ∧ feasible2 lowPolicy lowPolicy ∧
        (feasible1 highPolicy lowPolicy →
          objective1 highPolicy lowPolicy ≤ objective1 lowPolicy lowPolicy) ∧
          (feasible2 lowPolicy highPolicy →
            objective2 lowPolicy highPolicy ≤ objective2 lowPolicy lowPolicy) := by
  constructor
  · rintro ⟨hcur1, hcur2, hbest1, hbest2⟩
    exact ⟨hcur1, hcur2,
      fun hfeas => hbest1 highPolicy (Or.inr rfl) hfeas,
      fun hfeas => hbest2 highPolicy (Or.inr rfl) hfeas⟩
  · rintro ⟨hcur1, hcur2, hbest1, hbest2⟩
    refine ⟨hcur1, hcur2, ?_, ?_⟩
    · intro P1' hmem hfeas
      rcases hmem with rfl | rfl
      · exact le_rfl
      · exact hbest1 hfeas
    · intro P2' hmem hfeas
      rcases hmem with rfl | rfl
      · exact le_rfl
      · exact hbest2 hfeas

/-- Feasible binary-policy equilibrium characterization for `(low, high)`. -/
theorem twoPlayerBinaryPolicyFeasibleEquilibrium_lowHigh_iff
    {Policy : Type*} (objective1 objective2 : Policy → Policy → ℝ)
    (feasible1 feasible2 : Policy → Policy → Prop)
    (lowPolicy highPolicy : Policy) :
    TwoPlayerBinaryPolicyFeasibleEquilibrium objective1 objective2
        feasible1 feasible2 lowPolicy highPolicy lowPolicy highPolicy ↔
      feasible1 lowPolicy highPolicy ∧ feasible2 lowPolicy highPolicy ∧
        (feasible1 highPolicy highPolicy →
          objective1 highPolicy highPolicy ≤ objective1 lowPolicy highPolicy) ∧
          (feasible2 lowPolicy lowPolicy →
            objective2 lowPolicy lowPolicy ≤ objective2 lowPolicy highPolicy) := by
  constructor
  · rintro ⟨hcur1, hcur2, hbest1, hbest2⟩
    exact ⟨hcur1, hcur2,
      fun hfeas => hbest1 highPolicy (Or.inr rfl) hfeas,
      fun hfeas => hbest2 lowPolicy (Or.inl rfl) hfeas⟩
  · rintro ⟨hcur1, hcur2, hbest1, hbest2⟩
    refine ⟨hcur1, hcur2, ?_, ?_⟩
    · intro P1' hmem hfeas
      rcases hmem with rfl | rfl
      · exact le_rfl
      · exact hbest1 hfeas
    · intro P2' hmem hfeas
      rcases hmem with rfl | rfl
      · exact hbest2 hfeas
      · exact le_rfl

/-- Feasible binary-policy equilibrium characterization for `(high, low)`. -/
theorem twoPlayerBinaryPolicyFeasibleEquilibrium_highLow_iff
    {Policy : Type*} (objective1 objective2 : Policy → Policy → ℝ)
    (feasible1 feasible2 : Policy → Policy → Prop)
    (lowPolicy highPolicy : Policy) :
    TwoPlayerBinaryPolicyFeasibleEquilibrium objective1 objective2
        feasible1 feasible2 lowPolicy highPolicy highPolicy lowPolicy ↔
      feasible1 highPolicy lowPolicy ∧ feasible2 highPolicy lowPolicy ∧
        (feasible1 lowPolicy lowPolicy →
          objective1 lowPolicy lowPolicy ≤ objective1 highPolicy lowPolicy) ∧
          (feasible2 highPolicy highPolicy →
            objective2 highPolicy highPolicy ≤ objective2 highPolicy lowPolicy) := by
  constructor
  · rintro ⟨hcur1, hcur2, hbest1, hbest2⟩
    exact ⟨hcur1, hcur2,
      fun hfeas => hbest1 lowPolicy (Or.inl rfl) hfeas,
      fun hfeas => hbest2 highPolicy (Or.inr rfl) hfeas⟩
  · rintro ⟨hcur1, hcur2, hbest1, hbest2⟩
    refine ⟨hcur1, hcur2, ?_, ?_⟩
    · intro P1' hmem hfeas
      rcases hmem with rfl | rfl
      · exact hbest1 hfeas
      · exact le_rfl
    · intro P2' hmem hfeas
      rcases hmem with rfl | rfl
      · exact le_rfl
      · exact hbest2 hfeas

/-- Feasible binary-policy equilibrium characterization for `(high, high)`. -/
theorem twoPlayerBinaryPolicyFeasibleEquilibrium_highHigh_iff
    {Policy : Type*} (objective1 objective2 : Policy → Policy → ℝ)
    (feasible1 feasible2 : Policy → Policy → Prop)
    (lowPolicy highPolicy : Policy) :
    TwoPlayerBinaryPolicyFeasibleEquilibrium objective1 objective2
        feasible1 feasible2 lowPolicy highPolicy highPolicy highPolicy ↔
      feasible1 highPolicy highPolicy ∧ feasible2 highPolicy highPolicy ∧
        (feasible1 lowPolicy highPolicy →
          objective1 lowPolicy highPolicy ≤ objective1 highPolicy highPolicy) ∧
          (feasible2 highPolicy lowPolicy →
            objective2 highPolicy lowPolicy ≤ objective2 highPolicy highPolicy) := by
  constructor
  · rintro ⟨hcur1, hcur2, hbest1, hbest2⟩
    exact ⟨hcur1, hcur2,
      fun hfeas => hbest1 lowPolicy (Or.inl rfl) hfeas,
      fun hfeas => hbest2 lowPolicy (Or.inl rfl) hfeas⟩
  · rintro ⟨hcur1, hcur2, hbest1, hbest2⟩
    refine ⟨hcur1, hcur2, ?_, ?_⟩
    · intro P1' hmem hfeas
      rcases hmem with rfl | rfl
      · exact hbest1 hfeas
      · exact le_rfl
    · intro P2' hmem hfeas
      rcases hmem with rfl | rfl
      · exact hbest2 hfeas
      · exact le_rfl

/--
Generic objective-rewrite helper: once both policy-pair objective values are
identified with scalar expressions, the objective comparison is the scalar
comparison.
-/
theorem policy_pair_objective_le_iff_of_value_eq
    {Policy : Type*} (objective : Policy → Policy → ℝ)
    {P1 P2 P1' P2' : Policy} {lhs rhs : ℝ}
    (hlhs : objective P1 P2 = lhs) (hrhs : objective P1' P2' = rhs) :
    objective P1 P2 ≤ objective P1' P2' ↔ lhs ≤ rhs := by
  rw [hlhs, hrhs]

end AppliedModelingLib
