/-!
# Reusable-library declaration-graph regression fixture

This module is imported by the paper-shaped declaration-graph fixture but is
not itself paper-owned.  It tests the role distinction between explicit
source-semantic roots, proved implementation helpers, and unproved boundaries.
-/

namespace AppliedModelingLibAudit.DeclarationGraphFixtureLibrary

def MaterialPredicate (n : Nat) : Prop := n = n

theorem provedImplementationHelper (n : Nat) : MaterialPredicate n := rfl

def proofCarryingValue (n : Nat) : {m : Nat // MaterialPredicate m} :=
  ⟨n, provedImplementationHelper n⟩

theorem explicitSourceLaw (n : Nat) : MaterialPredicate n := rfl

def explicitLawCarryingValue (n : Nat) : {m : Nat // MaterialPredicate m} :=
  ⟨n, explicitSourceLaw n⟩

axiom unprovedBoundary (n : Nat) : MaterialPredicate n

def boundaryCarryingValue (n : Nat) : {m : Nat // MaterialPredicate m} :=
  ⟨n, unprovedBoundary n⟩

/-- An ordinary transparent implementation helper.  Lean should reduce it
into the containing semantic target without a declaration-specific rule. -/
def transparentImplementationHelper (n : Nat) : Nat := n + 1

def helperCarryingValue (n : Nat) : Nat :=
  transparentImplementationHelper n

/-- Equation compilation introduces a range-less transparent matcher.  Its
elaborated branches belong in this definition's display, not in a separate
semantic-review row. -/
def transparentPatternValue : Int → Nat
  | .ofNat n => n
  | .negSucc n => n + 1

end AppliedModelingLibAudit.DeclarationGraphFixtureLibrary
