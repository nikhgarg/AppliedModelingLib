import LOS02CombinatorialAuctions.SourceGVA
import LOS02CombinatorialAuctions.SourceCriticalProperties
import LOS02CombinatorialAuctions.SourceGreedyMechanism
import LOS02CombinatorialAuctions.NegativeResults

/-!
# LOS02: complete source-result propositions

Current-protocol migration draft: one transparent proposition per named result,
with a separate proof. Definitions and algorithm rules are semantic prerequisites,
not duplicate reflexive result rows. The native complexity conclusions of
Theorem 6.1 are not realized by the old abstract complexity wrappers and remain
an explicitly unformalized boundary. No semantic-review verdict is asserted.
Single-minded results use nonnegative, nonempty requests.  The Section 7
approximation endpoint also retains the source's explicit no-equal-norm
condition; its separate fixed-priority convention is used only where the
source's later tied-run discussion requires it.
-/

namespace LOS02CombinatorialAuctions.PaperInterface
open AppliedModelingLib.Auction

/-- Theorem 4.1: GVA on feasible source allocations is truthful. -/
def theorem4_1Spec {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item) : Prop :=
  SourceGVA.MaximizesFeasible alloc → SourceGVA.Truthful (SourceGVA.auction alloc)


/-- Proposition 4.2: truthful utility is nonnegative for every bidder. -/
def proposition4_2Spec {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item) : Prop :=
  SourceGVA.MaximizesFeasible alloc → ∀ D, SourceGVA.Admissible D →
    ∀ i, 0 ≤ (SourceGVA.auction alloc).utility D D i


/-- Theorem 7.2: square-root-norm greedy is a sqrt(k)-approximation. -/
def theorem7_2Spec {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) : Prop := by
  classical
  exact SourceCritical.SqrtNormNoTies bids → order.Nodup → (∀ i, i ∈ order) →
    SingleMindedSqrtNormDescending bids order →
    ∀ optimal, SingleMindedOptimalAcceptedSet bids optimal →
      singleMindedTotalValue bids optimal ≤ Real.sqrt (Fintype.card Item : ℝ) *
        singleMindedTotalValue bids (singleMindedGreedyAcceptedFromOrder bids order)


/-- Section 8: Clarke payments do not make the greedy allocation truthful. -/
def section8Spec : Prop :=
  NegativeResults.section8Witness ∧
    ¬ NegativeResults.greedyClarke.TruthfulOn
      SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile


/-- Lemma 9.1: a fixed request has a finite threshold or is always denied;
allocation at exact threshold equality is unconstrained. -/
def lemma9_1Spec {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (M : SingleMindedAcceptedMechanism Bidder Item) : Prop := by
  classical
  exact SourceCritical.Feasible M →
    M.MonotonicityOn SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile →
    ∀ D, SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile D → ∀ i s,
    s.Nonempty →
      (∃ c : ℝ, 0 ≤ c ∧
        (∀ v, 0 ≤ v → v < c → i ∉ M.accepted (Function.update D i ⟨s, v⟩)) ∧
        (∀ v, 0 ≤ v → c < v → i ∈ M.accepted (Function.update D i ⟨s, v⟩))) ∨
      (∀ v, 0 ≤ v → i ∉ M.accepted (Function.update D i ⟨s, v⟩))


/-- Lemma 9.2: denied bidders have zero utility under Participation. -/
def lemma9_2Spec {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (M : SingleMindedAcceptedMechanism Bidder Item) : Prop := by
  classical
  exact SourceCritical.Feasible M →
    SourceCritical.Participation M → ∀ T D,
    SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile T →
    SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile D →
    ∀ i, i ∉ M.accepted D → M.utility T D i = 0


/-- Lemma 9.3: truthful bidders have nonnegative utility under the criterion. -/
def lemma9_3Spec {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (M : SingleMindedAcceptedMechanism Bidder Item) : Prop := by
  classical
  exact SourceCritical.Feasible M →
    M.MonotonicityOn SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile →
    SourceCritical.Participation M → ∀ (_C : M.NonnegativeCriticalValueWithInfinityCertificate) T,
    SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile T → ∀ i, 0 ≤ M.utility T T i


/-- Lemma 9.4: changing only the declared value cannot improve utility. -/
def lemma9_4Spec {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (M : SingleMindedAcceptedMechanism Bidder Item) : Prop := by
  classical
  exact SourceCritical.Feasible M →
    M.MonotonicityOn SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile →
    SourceCritical.Participation M → ∀ (_C : M.NonnegativeCriticalValueWithInfinityCertificate) T,
    SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile T → ∀ i v, 0 ≤ v →
      M.utility T (Function.update T i ⟨(T i).desired, v⟩) i ≤ M.utility T T i


/-- Lemma 9.5: shrinking a granted request cannot increase its actual payment. -/
def lemma9_5Spec {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (M : SingleMindedAcceptedMechanism Bidder Item) : Prop := by
  classical
  exact SourceCritical.Feasible M →
    M.MonotonicityOn SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile →
    ∀ (_C : M.NonnegativeCriticalValueWithInfinityCertificate) D,
    SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile D → ∀ i,
    i ∈ M.accepted D → ∀ s, s.Nonempty → s ⊆ (D i).desired →
      M.payment (Function.update D i ⟨s, (D i).value⟩) i ≤ M.payment D i


/-- Theorem 9.6: Exactness (built into the allocation model), Monotonicity,
Participation, and Critical imply truthfulness on the source request domain. -/
def theorem9_6Spec {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (M : SingleMindedAcceptedMechanism Bidder Item) : Prop := by
  classical
  exact SourceCritical.Feasible M →
    M.MonotonicityOn SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile →
    SourceCritical.Participation M → ∀ (_C : M.NonnegativeCriticalValueWithInfinityCertificate),
    M.TruthfulOn SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile


/-- Theorem 10.2: actual average-order greedy with Definition 10.1 payments is
truthful, using one fixed consistent priority for ties. -/
def theorem10_2Spec {Bidder Item : Type*} [Fintype Bidder] [Fintype Item] [LinearOrder Bidder] : Prop := by
  letI : DecidableEq Bidder := LinearOrder.toDecidableEq
  letI : DecidableEq Item := Classical.decEq Item
  exact (SourceGreedy.averageGreedyMechanism (Bidder := Bidder) (Item := Item)).TruthfulOn
    SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile


/-- Section 12: no report-based payment makes greedy truthful on the paper's
two-good, double-minded domain, even fixing Red's bid. -/
def section12Spec : Prop :=
  ¬ ∃ payment : NegativeResults.GreenType → ℝ, NegativeResults.GreenTruthfulPayment payment


end LOS02CombinatorialAuctions.PaperInterface
