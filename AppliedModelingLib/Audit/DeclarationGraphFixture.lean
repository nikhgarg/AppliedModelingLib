import AppliedModelingLib.SocialChoice.FairDivision.IndivisibleGoods
import AppliedModelingLib.Audit.DeclarationGraphFixtureLibrary

/-!
# Native declaration-graph regression fixture

This tiny module exercises the distinction between a source-semantic frontier
node and an ordinary transparent implementation helper. It is imported only by
the audit regression suite.
-/

namespace AppliedModelingLibAudit.DeclarationGraphFixture

def reviewedPrimitive (n : Nat) : Nat := n + 1

def transparentHelper (n : Nat) : Nat := n + 1

private noncomputable def hiddenReviewedPrimitive (n : Nat) : Nat := n + 1

def claimSpec : Prop :=
  reviewedPrimitive 1 = transparentHelper 1

theorem claim : claimSpec := rfl

def libraryPrimitiveClaimSpec : Prop :=
  AppliedModelingLibAudit.DeclarationGraphFixtureLibrary.helperCarryingValue 1 = 2

theorem libraryPrimitiveClaim : libraryPrimitiveClaimSpec := rfl

/-- A source-presented inductive with a range-less compiler-generated child. -/
inductive GeneratedChoice where
  | left
  | right
  deriving DecidableEq, Repr

/-- The generated representation index must review through `GeneratedChoice`. -/
def generatedOwnerClaimSpec : Prop :=
  GeneratedChoice.ctorIdx GeneratedChoice.left = 0 ∧
    (if GeneratedChoice.left = GeneratedChoice.right then False else True)

theorem generatedOwnerClaim : generatedOwnerClaimSpec := by
  unfold generatedOwnerClaimSpec
  constructor
  · rfl
  · simp

/-- The proof route deliberately reaches a reusable axiom boundary. -/
def boundaryClosureClaimSpec : Prop :=
  ∃ n : Nat,
    AppliedModelingLibAudit.DeclarationGraphFixtureLibrary.MaterialPredicate n

theorem boundaryClosureClaim : boundaryClosureClaimSpec :=
  ⟨0, AppliedModelingLibAudit.DeclarationGraphFixtureLibrary.unprovedBoundary 0⟩

theorem explicitPaperSourceLaw (n : Nat) :
    AppliedModelingLibAudit.DeclarationGraphFixtureLibrary.MaterialPredicate n := rfl

def explicitPaperLawCarryingValue (n : Nat) :
    {m : Nat // AppliedModelingLibAudit.DeclarationGraphFixtureLibrary.MaterialPredicate m} :=
  ⟨n, explicitPaperSourceLaw n⟩

/-- A hand-written declaration under the same prefix remains independently owned. -/
def GeneratedChoice.sourcePresentedChild : Nat := 7

end AppliedModelingLibAudit.DeclarationGraphFixture
