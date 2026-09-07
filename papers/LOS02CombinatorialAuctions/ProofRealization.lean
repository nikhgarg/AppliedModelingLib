import LOS02CombinatorialAuctions.PaperInterface
import LOS02CombinatorialAuctions.ProofInterface

/-! Exact proof endpoints for the source-facing LOS02 Specs. -/

namespace LOS02CombinatorialAuctions.PaperInterface
open AppliedModelingLib.Auction

theorem theorem4_1 {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item) :
    theorem4_1Spec alloc := SourceGVA.truthful alloc

theorem proposition4_2 {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item) :
    proposition4_2Spec alloc := SourceGVA.truthful_utility_nonneg alloc

theorem theorem7_2 {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (bids : Bidder → SingleMindedBid Item) (order : List Bidder) :
    theorem7_2Spec bids order := by
  classical
  intro hlegal_no_ties _horder hall hsorted optimal hopt
  cases isEmpty_or_nonempty Bidder with
  | inl h =>
      letI := h
      have hz : ∀ S : Finset Bidder, singleMindedTotalValue bids S = 0 := by
        intro S
        apply Finset.sum_eq_zero
        intro i _
        exact isEmptyElim i
      simp only [singleMindedTotalValue] at hz ⊢
      rw [hz, hz]
      simp
  | inr h =>
      letI := h
      let i : Bidder := Classical.choice h
      obtain ⟨g, _⟩ := (hlegal_no_ties.1 i).1
      letI : Inhabited Bidder := ⟨i⟩
      letI : Inhabited Item := ⟨g⟩
      simpa using ProofInterface.theorem7_2_sqrt_norm_approx_of_sorted_order
        bids optimal Finset.univ order (fun _ _ => Finset.subset_univ _)
        hopt.1 (fun j _ => (hlegal_no_ties.1 j).1) (fun j _ => (hlegal_no_ties.1 j).1)
        (fun j _ => (hlegal_no_ties.1 j).2) (fun j _ => (hlegal_no_ties.1 j).2)
        hsorted (fun j _ => hall j)

theorem section8 : section8Spec :=
  ⟨NegativeResults.section8_witness, NegativeResults.section8_clarke_not_truthful⟩

theorem lemma9_1 {Bidder Item : Type*} [Fintype Bidder] [Fintype Item] (M : SingleMindedAcceptedMechanism Bidder Item) :
    lemma9_1Spec M := by
  classical
  intro _hfeasible
  exact M.exists_nonnegative_critical_value_of_monotonicityOn

theorem lemma9_2 {Bidder Item : Type*} [Fintype Bidder] [Fintype Item] (M : SingleMindedAcceptedMechanism Bidder Item) :
    lemma9_2Spec M := by
  classical
  intro _hfeasible
  exact SourceCritical.denied_utility M

theorem lemma9_3 {Bidder Item : Type*} [Fintype Bidder] [Fintype Item] (M : SingleMindedAcceptedMechanism Bidder Item) :
    lemma9_3Spec M := by
  classical
  intro _hfeasible _ hp C T hT i
  exact SourceCritical.utility_nonneg M hp C T hT i

theorem lemma9_4 {Bidder Item : Type*} [Fintype Bidder] [Fintype Item] (M : SingleMindedAcceptedMechanism Bidder Item) :
    lemma9_4Spec M := by
  classical
  intro _hfeasible hm hp C T hT i v hv
  exact SourceCritical.truthful M hm hp C T hT i ⟨(T i).desired, v⟩
    (SingleMindedAcceptedMechanism.nonnegativeNonemptyProfile_update T hT i (hT i).1 hv)

theorem lemma9_5 {Bidder Item : Type*} [Fintype Bidder] [Fintype Item] (M : SingleMindedAcceptedMechanism Bidder Item) :
    lemma9_5Spec M := by
  classical
  intro _hfeasible hm C D hD i hi s hs hsub
  exact (source_lemma9_5_payment_mono M hm C D hD i hi s hs hsub).2

theorem theorem9_6 {Bidder Item : Type*} [Fintype Bidder] [Fintype Item] (M : SingleMindedAcceptedMechanism Bidder Item) :
    theorem9_6Spec M := by
  classical
  intro _hfeasible
  exact SourceCritical.truthful M

theorem theorem10_2 {Bidder Item : Type*} [Fintype Bidder] [Fintype Item] [LinearOrder Bidder] :
    theorem10_2Spec (Bidder := Bidder) (Item := Item) := by
  classical
  simpa [theorem10_2Spec, SourceGreedy.averageGreedyMechanism, SourceGreedy.averagePayment,
    singleMindedAverageGreedyAcceptedMechanism,
    singleMindedGreedyAcceptedMechanismFromOrderOf,
    singleMindedGreedyPaymentFromOrder] using
    (ProofInterface.theorem10_2_averageGreedy_truthful
      (Bidder := Bidder) (Item := Item))

theorem section12 : section12Spec := NegativeResults.section12_no_truthful_payment

end LOS02CombinatorialAuctions.PaperInterface
