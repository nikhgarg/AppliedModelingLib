import AppliedModelingLib.Foundations.Probability.FiniteExpectation

/-!
# Prefix marginals of finite iid PMF products

Finite adaptive algorithms often expose only the first part of a pre-sampled
iid tape.  This module records the elementary fact that discarding the newest
draw preserves the iid law of the earlier tape.
-/

namespace AppliedModelingLib

/-- Removing the newest draw from a finite iid tape leaves the iid law of its
prefix unchanged, expressed as equality of finite expectations. -/
theorem pmfExp_pmfProduct_init_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) (n : ℕ) (statistic : (Fin n → α) → ℝ) :
    pmfExp (pmfProduct (Fin (n + 1)) α μ)
        (fun tape => statistic (Fin.init tape)) =
      pmfExp (pmfProduct (Fin n) α μ) statistic := by
  let e := optionFinEquivFinSucc n
  have hprefix : ∀ tape : Option (Fin n) → α,
      Fin.init (fun index : Fin (n + 1) => tape (e.symm index)) =
        (fun index => tape (some index)) := by
    intro tape
    funext index
    change tape (e.symm (Fin.castSucc index)) = tape (some index)
    simp [e, optionFinEquivFinSucc, Fin.castSucc_ne_last]
  calc
    pmfExp (pmfProduct (Fin (n + 1)) α μ)
        (fun tape => statistic (Fin.init tape)) =
      pmfExp (pmfProduct (Option (Fin n)) α μ)
        (fun tape => statistic (Fin.init (fun index => tape (e.symm index)))) := by
          exact (pmfExp_pmfProduct_equiv e μ
            (fun tape : Fin (n + 1) → α => statistic (Fin.init tape))).symm
    _ = pmfExp (pmfProduct (Option (Fin n)) α μ)
        (fun tape => statistic (fun index => tape (some index))) := by
          apply pmfExp_congr
          intro tape
          rw [hprefix tape]
    _ = pmfPairExp (pmfProduct (Fin n) α μ) μ
        (fun old _new => statistic old) := by
          rw [pmfExp_pmfProduct_option_eq_pairExp]
          rfl
    _ = pmfExp (pmfProduct (Fin n) α μ) statistic :=
      pmfPairExp_ignore_right _ _ statistic

/-- Every initial segment of a finite iid tape has its own iid product law,
again expressed as equality of finite expectations. -/
theorem pmfExp_pmfProduct_prefix_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) :
    ∀ {length total : ℕ} (hprefix : length ≤ total)
      (statistic : (Fin length → α) → ℝ),
      pmfExp (pmfProduct (Fin total) α μ)
          (fun tape => statistic (fun index => tape (Fin.castLE hprefix index))) =
        pmfExp (pmfProduct (Fin length) α μ) statistic := by
  intro length total hprefix statistic
  induction total generalizing length with
  | zero =>
      have hzero : length = 0 := Nat.eq_zero_of_le_zero hprefix
      subst length
      apply pmfExp_congr
      intro tape
      congr 1
  | succ total ih =>
      cases length with
      | zero =>
          let emptyTape : Fin 0 → α := Fin.elim0
          have hleft :
              pmfExp (pmfProduct (Fin (total + 1)) α μ)
                  (fun tape => statistic (fun index => tape (Fin.castLE hprefix index))) =
                statistic emptyTape := by
            calc
              pmfExp (pmfProduct (Fin (total + 1)) α μ)
                  (fun tape => statistic (fun index => tape (Fin.castLE hprefix index))) =
                pmfExp (pmfProduct (Fin (total + 1)) α μ)
                  (fun _ => statistic emptyTape) := by
                    apply pmfExp_congr
                    intro tape
                    congr 1
                    exact Subsingleton.elim _ _
              _ = statistic emptyTape := pmfExp_const _ _
          have hright :
              pmfExp (pmfProduct (Fin 0) α μ) statistic = statistic emptyTape := by
            calc
              pmfExp (pmfProduct (Fin 0) α μ) statistic =
                pmfExp (pmfProduct (Fin 0) α μ) (fun _ => statistic emptyTape) := by
                  apply pmfExp_congr
                  intro tape
                  congr 1
                  exact Subsingleton.elim _ _
              _ = statistic emptyTape := pmfExp_const _ _
          exact hleft.trans hright.symm
      | succ length =>
          have hsmall : length ≤ total := Nat.succ_le_succ_iff.mp hprefix
          by_cases heq : length = total
          · subst total
            apply pmfExp_congr
            intro tape
            congr 1
          · have hstrict : length < total := lt_of_le_of_ne hsmall heq
            have htail : length + 1 ≤ total := Nat.succ_le_of_lt hstrict
            let prefixStatistic : (Fin total → α) → ℝ := fun tape =>
              statistic (fun index => tape (Fin.castLE htail index))
            have hconsume :
                pmfExp (pmfProduct (Fin (total + 1)) α μ)
                    (fun tape => statistic
                      (fun index => tape (Fin.castLE hprefix index))) =
                  pmfExp (pmfProduct (Fin (total + 1)) α μ)
                    (fun tape => prefixStatistic (Fin.init tape)) := by
              apply pmfExp_congr
              intro tape
              unfold prefixStatistic
              congr 1
            calc
              pmfExp (pmfProduct (Fin (total + 1)) α μ)
                  (fun tape => statistic
                    (fun index => tape (Fin.castLE hprefix index))) =
                pmfExp (pmfProduct (Fin (total + 1)) α μ)
                  (fun tape => prefixStatistic (Fin.init tape)) := hconsume
              _ = pmfExp (pmfProduct (Fin total) α μ) prefixStatistic :=
                pmfExp_pmfProduct_init_eq μ total prefixStatistic
              _ = pmfExp (pmfProduct (Fin (length + 1)) α μ) statistic :=
                ih htail statistic

/-- The event-probability form of the iid-prefix marginal identity. -/
theorem pmfProb_pmfProduct_prefix_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (μ : PMF α) {length total : ℕ} (hprefix : length ≤ total)
    (event : (Fin length → α) → Prop) [DecidablePred event] :
    pmfProb (pmfProduct (Fin total) α μ)
        (fun tape => event (fun index => tape (Fin.castLE hprefix index))) =
      pmfProb (pmfProduct (Fin length) α μ) event := by
  unfold pmfProb
  exact pmfExp_pmfProduct_prefix_eq μ hprefix
    (fun sample => if event sample then (1 : ℝ) else 0)

end AppliedModelingLib
