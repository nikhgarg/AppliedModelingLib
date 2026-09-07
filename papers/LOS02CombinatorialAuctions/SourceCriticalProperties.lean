import AppliedModelingLib.MechanismDesign.Auctions.Combinatorial

/-!
# Source payment consequence of critical-value monotonicity

Lemma 9.5 compares actual payments after a granted bidder requests a smaller
bundle. The finite-threshold comparison in the reusable library is a proof
step, not that entire conclusion. This module composes it with Monotonicity
and Critical, keeping the nonnegative, nonempty request domain explicit.
-/

namespace LOS02CombinatorialAuctions

open AppliedModelingLib.Auction

universe u v

namespace SourceCritical

/-- Definition 5.1's legal single-minded declaration domain in the selected
Sections 7, 9, and 10 scope. Equality decisions remain local implementation
choices rather than extra source assumptions. -/
def LegalProfile {Bidder Item : Type*}
    (bids : Bidder → SingleMindedBid Item) : Prop := by
  classical
  exact SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile bids

/-- Definition 5.1's free-disposal valuation formula, with no public
implementation equality witness. -/
noncomputable def Valuation {Item : Type*}
    (bid : SingleMindedBid Item) (bundle : Bundle Item) : ℝ := by
  classical
  exact bid.valuation bundle

/-- Section 9's domain-restricted Monotonicity property. -/
def Monotonicity {Bidder Item : Type*}
    (M : SingleMindedAcceptedMechanism Bidder Item) : Prop := by
  classical
  exact M.MonotonicityOn LegalProfile

/-- Section 9's Critical property, including its finite/infinite threshold
alternative, with equality choices internal to the formalization. -/
noncomputable abbrev Critical {Bidder : Type u} {Item : Type v}
    (M : SingleMindedAcceptedMechanism Bidder Item) : Type (max u v) := by
  classical
  exact M.NonnegativeCriticalValueWithInfinityCertificate

/-- The Section 7 welfare objective on a selected set of bids. -/
noncomputable def TotalValue {Bidder Item : Type*}
    (bids : Bidder → SingleMindedBid Item) (selected : Finset Bidder) : ℝ := by
  classical
  exact singleMindedTotalValue bids selected

/-- Section 7's formal no-ties restriction on legal nonnegative, nonempty bids:
distinct bidders' bids have distinct square-root norms.  The separate fixed-priority
convention is used where the paper later discusses tied average-value runs; it is
not a substitute for this stated approximation-domain assumption. -/
def SqrtNormNoTies {Bidder Item : Type*}
    (bids : Bidder → SingleMindedBid Item) : Prop := by
  classical
  exact LegalProfile bids ∧
    Function.Injective fun i => (bids i).sqrtAmountNorm

/-- Sections 3 and 9: an exact allocation is a conflict-free set of bids. -/
def Feasible {Bidder Item : Type*}
    (M : SingleMindedAcceptedMechanism Bidder Item) : Prop := by
  classical
  exact ∀ D, LegalProfile D →
    PairwiseDisjointDesired D (M.accepted D)

/-- Participation is required only on the source declaration domain. -/
def Participation {Bidder Item : Type*}
    (M : SingleMindedAcceptedMechanism Bidder Item) : Prop := by
  classical
  exact ∀ D, LegalProfile D →
    ∀ i, i ∉ M.accepted D → M.payment D i = 0

/-- Extend payments by zero off the source domain, without changing any source run. -/
private noncomputable def extend {Bidder Item : Type*}
    (M : SingleMindedAcceptedMechanism Bidder Item) :
    SingleMindedAcceptedMechanism Bidder Item := by
  classical
  exact {
    accepted := M.accepted
    payment := fun D i =>
      if SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile D
      then M.payment D i else 0 }

private theorem extend_participation {Bidder Item : Type*}
    (M : SingleMindedAcceptedMechanism Bidder Item) (hp : Participation M) :
    (extend M).Participation := by
  classical
  intro D i hi
  by_cases hD : SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile D
  · simpa [extend, hD] using hp D hD i hi
  · simp [extend, hD]

private noncomputable def extend_critical {Bidder Item : Type*}
    [DecidableEq Bidder] [DecidableEq Item]
    {M : SingleMindedAcceptedMechanism Bidder Item}
    (C : M.NonnegativeCriticalValueWithInfinityCertificate) :
    (extend M).NonnegativeCriticalValueWithInfinityCertificate where
  threshold := C.threshold
  threshold_nonneg := C.threshold_nonneg
  threshold_own_value_independent := C.threshold_own_value_independent
  below_denied := C.below_denied
  above_granted := C.above_granted
  infinite_denied := C.infinite_denied
  payment_eq_of_accepted := by
    intro D hD i hi
    have hD' : ∀ j, (D j).desired.Nonempty ∧ 0 ≤ (D j).value := hD
    simpa [extend, SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile, hD'] using
      C.payment_eq_of_accepted D hD i hi

private theorem extend_utility {Bidder Item : Type*}
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (T D : Bidder → SingleMindedBid Item)
    (hD : SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile D) (i : Bidder) :
    (extend M).utility T D i = M.utility T D i := by
  have hD' : ∀ j, (D j).desired.Nonempty ∧ 0 ≤ (D j).value := hD
  simp [SingleMindedAcceptedMechanism.utility,
    SingleMindedAcceptedMechanism.allocation, extend,
    SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile, hD']

/-- Lemma 9.2 for valid declarations; no off-domain participation premise. -/
theorem denied_utility {Bidder Item : Type*}
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item) (hp : Participation M)
    (T D : Bidder → SingleMindedBid Item)
    (hT : SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile T)
    (hD : SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile D)
    (i : Bidder) (hi : i ∉ M.accepted D) : M.utility T D i = 0 := by
  rw [← extend_utility M T D hD i]
  exact SingleMindedAcceptedMechanism.utility_eq_zero_of_denied_participation
    (extend M) (extend_participation M hp) T D (hT i).1 hi

/-- Lemma 9.3 for valid declarations and the source Critical property. -/
theorem utility_nonneg {Bidder Item : Type*}
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item) (hp : Participation M)
    (C : M.NonnegativeCriticalValueWithInfinityCertificate)
    (T : Bidder → SingleMindedBid Item)
    (hT : SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile T) (i : Bidder) :
    0 ≤ M.utility T T i := by
  rw [← extend_utility M T T hT i]
  exact SingleMindedAcceptedMechanism.utility_nonneg_truthful_of_nonnegative_infinity_certificate
    (extend M) (extend_participation M hp) (extend_critical C) T hT i

/-- Theorem 9.6 without any assumption about invalid negative/empty reports. -/
theorem truthful {Bidder Item : Type*}
    [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hm : M.MonotonicityOn SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile)
    (hp : Participation M) (C : M.NonnegativeCriticalValueWithInfinityCertificate) :
    M.TruthfulOn SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile := by
  have h := SingleMindedAcceptedMechanism.truthfulOn_of_monotonicityOn_participation_nonnegative_infinity_critical
    (extend M) hm (extend_participation M hp) (extend_critical C)
  intro T hT i report hreport
  simpa only [extend_utility M T _ hreport i, extend_utility M T T hT i] using
    h T hT i report hreport

end SourceCritical

/-- Lemma 9.5: shrinking a granted request keeps it granted and lowers its payment. -/
theorem source_lemma9_5_payment_mono
    {Bidder Item : Type*} [DecidableEq Bidder] [DecidableEq Item]
    (M : SingleMindedAcceptedMechanism Bidder Item)
    (hmono : M.MonotonicityOn SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile)
    (C : M.NonnegativeCriticalValueWithInfinityCertificate)
    (reports : Bidder → SingleMindedBid Item)
    (hreports : SingleMindedAcceptedMechanism.NonnegativeNonemptyProfile reports)
    (i : Bidder) (hgrant : i ∈ M.accepted reports)
    (s : Finset Item) (hs : s.Nonempty) (hsub : s ⊆ (reports i).desired) :
    i ∈ M.accepted (Function.update reports i ⟨s, (reports i).value⟩) ∧
      M.payment (Function.update reports i ⟨s, (reports i).value⟩) i ≤
        M.payment reports i := by
  have hup := SingleMindedAcceptedMechanism.nonnegativeNonemptyProfile_update
    reports hreports i hs (hreports i).2
  have hsmall := hmono reports hreports i s (reports i).value hgrant hup hsub le_rfl
  refine ⟨hsmall, ?_⟩
  obtain ⟨pLarge, hLarge, hpayLarge⟩ := C.payment_eq_of_accepted reports hreports i hgrant
  obtain ⟨pSmall, hSmall, hle⟩ := C.finite_threshold_mono_of_monotone hmono
    reports hreports i hs (hreports i).1 hsub hLarge
  obtain ⟨pPaid, hPaid, hpaySmall⟩ := C.payment_eq_of_accepted
    (Function.update reports i ⟨s, (reports i).value⟩) hup i hsmall
  have hsame := C.threshold_own_value_independent reports hreports i s
    (reports i).value hs (hreports i).2
  simp only [Function.update_self] at hPaid
  rw [hsame, hSmall] at hPaid
  have heq : pSmall = pPaid := Option.some.inj hPaid
  rw [hpaySmall, hpayLarge, ← heq]
  exact hle

end LOS02CombinatorialAuctions
