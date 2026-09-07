import AppliedModelingLib.Foundations.Probability.FiniteExpectation

open scoped BigOperators

namespace AppliedModelingLib

namespace FiniteProductTernaryCounts

/-- Product of a three-valued coordinate weight over two disjoint finite sets. -/
theorem prod_ite_mem_mem_eq_pow_mul_pow_mul_pow {ι : Type*}
    [Fintype ι] [DecidableEq ι] (U D : Finset ι) (hUD : Disjoint U D)
    (q r rho : ℝ) :
    (∏ i : ι, if i ∈ U then q else if i ∈ D then r else rho) =
      q ^ U.card * r ^ D.card *
        rho ^ (Fintype.card ι - U.card - D.card) := by
  classical
  let rest : Finset ι := (Finset.univ : Finset ι) \ (U ∪ D)
  have hU_filter :
      (Finset.univ : Finset ι).filter (fun i => i ∈ U) = U := by
    ext i
    simp
  have hD_filter :
      ((Finset.univ : Finset ι).filter (fun i => ¬ i ∈ U)).filter
          (fun i => i ∈ D) = D := by
    ext i
    by_cases hiD : i ∈ D
    · have hiU : i ∉ U := by
        exact (Finset.disjoint_left.mp hUD.symm) hiD
      simp [hiD, hiU]
    · simp [hiD]
  have hrest_filter :
      ((Finset.univ : Finset ι).filter (fun i => ¬ i ∈ U)).filter
          (fun i => ¬ i ∈ D) = rest := by
    ext i
    simp [rest]
  have hrest_card :
      rest.card = Fintype.card ι - U.card - D.card := by
    have hcard_union : (U ∪ D).card = U.card + D.card :=
      Finset.card_union_of_disjoint hUD
    dsimp [rest]
    rw [Finset.card_sdiff]
    rw [Finset.inter_univ, hcard_union, Finset.card_univ]
    omega
  have hsplitU :=
    Finset.prod_filter_mul_prod_filter_not
      (s := (Finset.univ : Finset ι))
      (p := fun i => i ∈ U)
      (f := fun i => if i ∈ U then q else if i ∈ D then r else rho)
  have hsplitD :=
    Finset.prod_filter_mul_prod_filter_not
      (s := (Finset.univ : Finset ι).filter (fun i => ¬ i ∈ U))
      (p := fun i => i ∈ D)
      (f := fun i => if i ∈ U then q else if i ∈ D then r else rho)
  rw [← hsplitU, ← hsplitD]
  have hprodU :
      (∏ x ∈ U, if x ∈ U then q else if x ∈ D then r else rho) =
        q ^ U.card := by
    trans ∏ _x ∈ U, q
    · refine Finset.prod_congr rfl ?_
      intro x hx
      simp [hx]
    · simp [Finset.prod_const]
  have hprodD :
      (∏ x ∈ D, if x ∈ U then q else if x ∈ D then r else rho) =
        r ^ D.card := by
    trans ∏ _x ∈ D, r
    · refine Finset.prod_congr rfl ?_
      intro x hx
      have hxU : x ∉ U := (Finset.disjoint_left.mp hUD.symm) hx
      simp [hx, hxU]
    · simp [Finset.prod_const]
  have hprodRest :
      (∏ x ∈ rest, if x ∈ U then q else if x ∈ D then r else rho) =
        rho ^ rest.card := by
    trans ∏ _x ∈ rest, rho
    · refine Finset.prod_congr rfl ?_
      intro x hx
      have hxRest : x ∉ U ∧ x ∉ D := by
        simpa [rest] using hx
      have hxU : x ∉ U := by
        exact hxRest.1
      have hxD : x ∉ D := by
        exact hxRest.2
      simp [hxU, hxD]
    · simp [Finset.prod_const]
  rw [hU_filter, hD_filter, hrest_filter, hprodU, hprodD, hprodRest,
    hrest_card]
  ring

end FiniteProductTernaryCounts

/--
For an independent finite product PMF, the probability of fixed success-index
sets for two disjoint predicates factors into the three coordinate categories:
`up`, `down`, and neither.
-/
theorem pmfProduct_prob_two_disjoint_successIndexSet_eq
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (up down : α → Prop)
    [DecidablePred up] [DecidablePred down]
    (hdisj : ∀ a, up a → down a → False)
    (U D : Finset ι) (hUD : Disjoint U D) :
    pmfProb (pmfProduct ι α μ)
        (fun sample : ι → α =>
          successIndexSet up sample = U ∧ successIndexSet down sample = D) =
      (pmfProb μ up) ^ U.card * (pmfProb μ down) ^ D.card *
        (pmfProb μ (fun a => ¬ up a ∧ ¬ down a)) ^
          (Fintype.card ι - U.card - D.card) := by
  classical
  let rest : α → Prop := fun a => ¬ up a ∧ ¬ down a
  let P : ι → α → Prop :=
    fun i a => if i ∈ U then up a else if i ∈ D then down a else rest a
  have hevent :
      ∀ sample : ι → α,
        (successIndexSet up sample = U ∧ successIndexSet down sample = D) ↔
          ∀ i : ι, P i (sample i) := by
    intro sample
    constructor
    · intro h i
      have hup := (successIndexSet_eq_iff sample U).mp h.1 i
      have hdown := (successIndexSet_eq_iff sample D).mp h.2 i
      by_cases hiU : i ∈ U
      · simp [P, hiU, (hup).2 hiU]
      · by_cases hiD : i ∈ D
        · simp [P, hiU, hiD, (hdown).2 hiD]
        · have hnup : ¬ up (sample i) := by
            intro hui
            exact hiU ((hup).1 hui)
          have hndown : ¬ down (sample i) := by
            intro hdi
            exact hiD ((hdown).1 hdi)
          simp [P, rest, hiU, hiD, hnup, hndown]
    · intro h
      constructor
      · refine (successIndexSet_eq_iff sample U).mpr ?_
        intro i
        constructor
        · intro hui
          by_contra hiU
          by_cases hiD : i ∈ D
          · have hdi : down (sample i) := by
              simpa [P, hiU, hiD] using h i
            exact hdisj (sample i) hui hdi
          · have hnui : ¬ up (sample i) := by
              exact (show rest (sample i) from by simpa [P, hiU, hiD] using h i).1
            exact hnui hui
        · intro hiU
          simpa [P, hiU] using h i
      · refine (successIndexSet_eq_iff sample D).mpr ?_
        intro i
        constructor
        · intro hdi
          by_contra hiD
          by_cases hiU : i ∈ U
          · have hui : up (sample i) := by
              simpa [P, hiU] using h i
            exact hdisj (sample i) hui hdi
          · have hndi : ¬ down (sample i) := by
              exact (show rest (sample i) from by simpa [P, hiU, hiD] using h i).2
            exact hndi hdi
        · intro hiD
          have hiU : i ∉ U := by
            exact (Finset.disjoint_left.mp hUD.symm) hiD
          simpa [P, hiU, hiD] using h i
  calc
    pmfProb (pmfProduct ι α μ)
        (fun sample : ι → α =>
          successIndexSet up sample = U ∧ successIndexSet down sample = D)
        =
        pmfProb (pmfProduct ι α μ)
          (fun sample : ι → α => ∀ i : ι, P i (sample i)) := by
          refine pmfProb_congr _ ?_
          intro sample
          exact hevent sample
    _ = ∏ i : ι, pmfProb μ (P i) :=
          pmfProduct_prob_forall_dependent μ P
    _ =
        ∏ i : ι,
          if i ∈ U then
            pmfProb μ up
          else if i ∈ D then
            pmfProb μ down
          else
            pmfProb μ rest := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          by_cases hiU : i ∈ U
          · simp [P, hiU]
          · by_cases hiD : i ∈ D
            · simp [P, hiU, hiD]
            · simp [P, hiU, hiD]
    _ =
        (pmfProb μ up) ^ U.card * (pmfProb μ down) ^ D.card *
          (pmfProb μ rest) ^ (Fintype.card ι - U.card - D.card) :=
          FiniteProductTernaryCounts.prod_ite_mem_mem_eq_pow_mul_pow_mul_pow
            U D hUD (pmfProb μ up) (pmfProb μ down) (pmfProb μ rest)

/--
For an independent finite product PMF, the joint count of two disjoint
success predicates has the ternary multinomial mass formula.
-/
theorem pmfProduct_prob_two_disjoint_success_counts_eq
    {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [DecidableEq α]
    (μ : PMF α) (up down : α → Prop)
    [DecidablePred up] [DecidablePred down]
    (hdisj : ∀ a, up a → down a → False) (i j : ℕ) :
    pmfProb (pmfProduct ι α μ)
        (fun sample : ι → α =>
          (successIndexSet up sample).card = i ∧
            (successIndexSet down sample).card = j) =
      (Nat.choose (Fintype.card ι) i : ℝ) *
        (Nat.choose (Fintype.card ι - i) j : ℝ) *
          (pmfProb μ up) ^ i * (pmfProb μ down) ^ j *
            (pmfProb μ (fun a => ¬ up a ∧ ¬ down a)) ^
              (Fintype.card ι - i - j) := by
  classical
  let exactUps : Finset (Finset ι) :=
    (Finset.univ : Finset ι).powersetCard i
  let exactDowns : Finset ι → Finset (Finset ι) :=
    fun U => ((Finset.univ : Finset ι) \ U).powersetCard j
  let rest : α → Prop := fun a => ¬ up a ∧ ¬ down a
  have hsuccess_disjoint :
      ∀ sample : ι → α,
        Disjoint (successIndexSet up sample) (successIndexSet down sample) := by
    intro sample
    rw [Finset.disjoint_left]
    intro x hxup hxdown
    have hup : up (sample x) := by
      simpa [successIndexSet] using hxup
    have hdown : down (sample x) := by
      simpa [successIndexSet] using hxdown
    exact hdisj (sample x) hup hdown
  have hindicator :
      ∀ sample : ι → α,
        (if (successIndexSet up sample).card = i ∧
              (successIndexSet down sample).card = j then
            (1 : ℝ)
          else 0) =
          ∑ U ∈ exactUps, ∑ D ∈ exactDowns U,
            if successIndexSet up sample = U ∧
                successIndexSet down sample = D then
              (1 : ℝ)
            else 0 := by
    intro sample
    by_cases hcard :
        (successIndexSet up sample).card = i ∧
          (successIndexSet down sample).card = j
    · have hUmem : successIndexSet up sample ∈ exactUps := by
        simp [exactUps, hcard.1]
      have hDmem :
          successIndexSet down sample ∈ exactDowns (successIndexSet up sample) := by
        have hsubset :
            successIndexSet down sample ⊆
              (Finset.univ : Finset ι) \ successIndexSet up sample := by
          intro x hxdown
          have hxnotup : x ∉ successIndexSet up sample :=
            (Finset.disjoint_left.mp (hsuccess_disjoint sample).symm) hxdown
          simp [hxnotup]
        exact Finset.mem_powersetCard.mpr ⟨hsubset, hcard.2⟩
      rw [if_pos hcard]
      rw [Finset.sum_eq_single (successIndexSet up sample)]
      · rw [Finset.sum_eq_single (successIndexSet down sample)]
        · simp
        · intro D hD hDne
          have hne :
              ¬ (successIndexSet up sample = successIndexSet up sample ∧
                  successIndexSet down sample = D) := by
            intro h
            exact hDne h.2.symm
          exact if_neg hne
        · intro hnot
          exact False.elim (hnot hDmem)
      · intro U hU hUne
        apply Finset.sum_eq_zero
        intro D _hD
        have hne :
            ¬ (successIndexSet up sample = U ∧
                successIndexSet down sample = D) := by
          intro h
          exact hUne h.1.symm
        exact if_neg hne
      · intro hnot
        exact False.elim (hnot hUmem)
    · have hzero :
        ∀ U ∈ exactUps, ∀ D ∈ exactDowns U,
          ¬ (successIndexSet up sample = U ∧
              successIndexSet down sample = D) := by
        intro U hU D hD h
        have hUcard : U.card = i := by
          simpa [exactUps] using (Finset.mem_powersetCard.mp hU).2
        have hDcard : D.card = j := by
          simpa [exactDowns] using (Finset.mem_powersetCard.mp hD).2
        exact hcard (by simp [h.1, h.2, hUcard, hDcard])
      rw [if_neg hcard]
      symm
      apply Finset.sum_eq_zero
      intro U hU
      apply Finset.sum_eq_zero
      intro D hD
      exact if_neg (hzero U hU D hD)
  let C : ℝ :=
    (pmfProb μ up) ^ i * (pmfProb μ down) ^ j *
      (pmfProb μ rest) ^ (Fintype.card ι - i - j)
  unfold pmfProb pmfExp
  calc
    ∑ sample : ι → α,
        (pmfProduct ι α μ sample).toReal *
          (if (successIndexSet up sample).card = i ∧
                (successIndexSet down sample).card = j then
              (1 : ℝ)
            else 0)
        =
        ∑ sample : ι → α,
          (pmfProduct ι α μ sample).toReal *
            (∑ U ∈ exactUps, ∑ D ∈ exactDowns U,
              if successIndexSet up sample = U ∧
                  successIndexSet down sample = D then
                (1 : ℝ)
              else 0) := by
          refine Finset.sum_congr rfl ?_
          intro sample _
          rw [hindicator sample]
    _ =
        ∑ sample : ι → α, ∑ U ∈ exactUps, ∑ D ∈ exactDowns U,
          (pmfProduct ι α μ sample).toReal *
            (if successIndexSet up sample = U ∧
                successIndexSet down sample = D then
              (1 : ℝ)
            else 0) := by
          refine Finset.sum_congr rfl ?_
          intro sample _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro U _
          rw [Finset.mul_sum]
    _ =
        ∑ U ∈ exactUps, ∑ sample : ι → α, ∑ D ∈ exactDowns U,
          (pmfProduct ι α μ sample).toReal *
            (if successIndexSet up sample = U ∧
                successIndexSet down sample = D then
              (1 : ℝ)
            else 0) :=
          Finset.sum_comm
    _ =
        ∑ U ∈ exactUps, ∑ D ∈ exactDowns U, ∑ sample : ι → α,
          (pmfProduct ι α μ sample).toReal *
            (if successIndexSet up sample = U ∧
                successIndexSet down sample = D then
              (1 : ℝ)
            else 0) := by
          refine Finset.sum_congr rfl ?_
          intro U _hU
          exact Finset.sum_comm
    _ =
        ∑ U ∈ exactUps, ∑ D ∈ exactDowns U,
          (pmfProb μ up) ^ U.card * (pmfProb μ down) ^ D.card *
            (pmfProb μ rest) ^ (Fintype.card ι - U.card - D.card) := by
          refine Finset.sum_congr rfl ?_
          intro U _hU
          refine Finset.sum_congr rfl ?_
          intro D hD
          have hUD : Disjoint U D := by
            rw [Finset.disjoint_left]
            intro x hxU hxD
            have hxsdiff : x ∈ (Finset.univ : Finset ι) \ U :=
              (Finset.mem_powersetCard.mp hD).1 hxD
            exact (Finset.mem_sdiff.mp hxsdiff).2 hxU
          exact pmfProduct_prob_two_disjoint_successIndexSet_eq μ up down hdisj U D hUD
    _ =
        ∑ U ∈ exactUps, ∑ D ∈ exactDowns U, C := by
          refine Finset.sum_congr rfl ?_
          intro U hU
          have hUcard : U.card = i := by
            simpa [exactUps] using (Finset.mem_powersetCard.mp hU).2
          refine Finset.sum_congr rfl ?_
          intro D hD
          have hDcard : D.card = j := by
            simpa [exactDowns] using (Finset.mem_powersetCard.mp hD).2
          simp [C, rest, hUcard, hDcard]
    _ =
        ∑ U ∈ exactUps,
          (Nat.choose (Fintype.card ι - i) j : ℝ) * C := by
          refine Finset.sum_congr rfl ?_
          intro U hU
          have hUcard : U.card = i := by
            simpa [exactUps] using (Finset.mem_powersetCard.mp hU).2
          have hcomp_card :
              ((Finset.univ : Finset ι) \ U).card = Fintype.card ι - i := by
            rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hUcard]
          have hcard_downs :
              (exactDowns U).card = Nat.choose (Fintype.card ι - i) j := by
            simp [exactDowns, Finset.card_powersetCard, hcomp_card]
          simp [hcard_downs]
    _ =
        (Nat.choose (Fintype.card ι) i : ℝ) *
          (Nat.choose (Fintype.card ι - i) j : ℝ) * C := by
          have hcard_ups :
              exactUps.card = Nat.choose (Fintype.card ι) i := by
            simp [exactUps, Finset.card_powersetCard, Finset.card_univ]
          simp [hcard_ups, mul_assoc]
    _ =
        (Nat.choose (Fintype.card ι) i : ℝ) *
          (Nat.choose (Fintype.card ι - i) j : ℝ) *
            (pmfProb μ up) ^ i * (pmfProb μ down) ^ j *
              (pmfProb μ (fun a => ¬ up a ∧ ¬ down a)) ^
                (Fintype.card ι - i - j) := by
          simp [C, rest, mul_assoc]

end AppliedModelingLib
