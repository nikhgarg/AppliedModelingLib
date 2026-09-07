import SeshadriUgander2020IIATesting.AllEvenSubsets
import SeshadriUgander2020IIATesting.Testing

/-!
# The all-even-subsets testing consequence

This module feeds the constructed all-even comparison frame and its concrete
short/long cycle decomposition into the finite testing theorem.  It states an
explicit finite version of the paper's ``constant times `log(n)^5`'' exponent;
the source's asymptotic display leaves its constant unspecified.
-/

namespace SeshadriUgander2020IIATesting

open scoped BigOperators

namespace AllEvenChoiceSet

/-- The risk lower-bound expression is antitone in its nonnegative
chi-square exponent. -/
private theorem riskLower_antitone_exponent {a b : ℝ} (hab : a ≤ b) :
    1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp b - 1) ≤
      1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp a - 1) := by
  have hexp : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  have hsqrt : Real.sqrt (Real.exp a - 1) ≤ Real.sqrt (Real.exp b - 1) :=
    Real.sqrt_le_sqrt (by linarith)
  linarith

/-- A fully finite all-even-subsets instance of Theorem 1.  The source's
`c log(n)^5` display is made concrete with `8 * (5 log₂ n)^5`, and the
necessary small-separation condition is stated explicitly. -/
theorem productTestingLowerBound_five_log_of_three
    (n : ℕ) (hn : 3 ≤ n) (δ : ℝ) (hδ_nonneg : 0 ≤ δ)
    (hsmall : 2 * (5 * Real.logb 2 (n : ℝ)) * δ ≤ 1) (N : ℕ) :
    ChoiceSystem.ProductTestingLowerBound (F := frame n (by omega)) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp
          ((8 * (5 * Real.logb 2 (n : ℝ)) ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) /
            ((frame n (by omega)).incidenceCount : ℝ)) - 1)) := by
  obtain ⟨D, W, hmean, hdispersion⟩ :=
    exists_cycleDecomposition_five_log_withWitness_of_three n hn
  let L : ℝ := 5 * Real.logb 2 (n : ℝ)
  let d : ℝ := ((frame n (by omega)).incidenceCount : ℝ)
  let a : ℝ :=
    (8 * D.cycleMean ^ 4 *
      CycleMixture.cycleDispersion (frame n (by omega)).incidenceCount D.length *
        (N : ℝ) ^ 2 * δ ^ 4) / d
  let b : ℝ := (8 * L ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) / d
  have hsmallD : 2 * D.cycleMean * δ ≤ 1 := by
    calc
      2 * D.cycleMean * δ = D.cycleMean * (2 * δ) := by ring
      _ ≤ L * (2 * δ) :=
        mul_le_mul_of_nonneg_right (by simpa [L] using hmean) (by positivity)
      _ = 2 * L * δ := by ring
      _ ≤ 1 := by simpa [L] using hsmall
  have hbase := D.theorem1_productTestingLowerBound W δ hδ_nonneg hsmallD N
  have hdpos : 0 < d := by
    dsimp [d]
    exact_mod_cast (frame n (by omega)).incidenceCount_pos
  have hdisp_nonneg : 0 ≤
      CycleMixture.cycleDispersion (frame n (by omega)).incidenceCount D.length := by
    unfold CycleMixture.cycleDispersion
    positivity
  have hLnonneg : 0 ≤ L := by
    exact D.cycleMean_pos.le.trans (by simpa [L] using hmean)
  have hmean_pow : D.cycleMean ^ 4 ≤ L ^ 4 :=
    pow_le_pow_left₀ D.cycleMean_pos.le (by simpa [L] using hmean) 4
  have hproduct : D.cycleMean ^ 4 *
      CycleMixture.cycleDispersion (frame n (by omega)).incidenceCount D.length ≤
        L ^ 5 := by
    calc
      D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion (frame n (by omega)).incidenceCount D.length ≤
          L ^ 4 *
            CycleMixture.cycleDispersion (frame n (by omega)).incidenceCount D.length :=
        mul_le_mul_of_nonneg_right hmean_pow hdisp_nonneg
      _ ≤ L ^ 4 * L :=
        mul_le_mul_of_nonneg_left (by simpa [L] using hdispersion)
          (pow_nonneg hLnonneg 4)
      _ = L ^ 5 := by ring
  have hfactor : 0 ≤ 8 * (N : ℝ) ^ 2 * δ ^ 4 := by positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    calc
      (8 * D.cycleMean ^ 4 *
          CycleMixture.cycleDispersion (frame n (by omega)).incidenceCount D.length *
            (N : ℝ) ^ 2 * δ ^ 4) / d =
          (D.cycleMean ^ 4 *
            CycleMixture.cycleDispersion (frame n (by omega)).incidenceCount D.length) *
              (8 * (N : ℝ) ^ 2 * δ ^ 4) / d := by ring
      _ ≤ L ^ 5 * (8 * (N : ℝ) ^ 2 * δ ^ 4) / d :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hproduct hfactor) hdpos.le
      _ = (8 * L ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) / d := by ring
  have hlower := riskLower_antitone_exponent hab
  change ChoiceSystem.ProductTestingLowerBound (F := frame n (by omega)) N δ
    (1 / 2 - (1 / 4 : ℝ) * Real.sqrt (Real.exp b - 1))
  intro φ
  obtain ⟨q, hseparated, herror⟩ := hbase φ
  refine ⟨q, hseparated, ?_⟩
  apply hlower.trans
  simpa [a, d] using herror

/-- The same all-even testing bound with the source incidence count
`d = n 2^(n-2)` substituted into its exponent. -/
theorem productTestingLowerBound_five_log_source_count_of_three
    (n : ℕ) (hn : 3 ≤ n) (δ : ℝ) (hδ_nonneg : 0 ≤ δ)
    (hsmall : 2 * (5 * Real.logb 2 (n : ℝ)) * δ ≤ 1) (N : ℕ) :
    ChoiceSystem.ProductTestingLowerBound (F := frame n (by omega)) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp
          ((8 * (5 * Real.logb 2 (n : ℝ)) ^ 5 * (N : ℝ) ^ 2 * δ ^ 4) /
            ((n : ℝ) * (2 ^ (n - 2) : ℕ))) - 1)) := by
  have hcount : ((frame n (by omega)).incidenceCount : ℝ) =
      (n : ℝ) * (2 ^ (n - 2) : ℕ) := by
    exact_mod_cast (incidenceCount_eq_source_of_three n hn)
  simpa only [hcount] using
    (productTestingLowerBound_five_log_of_three n hn δ hδ_nonneg hsmall N)

end AllEvenChoiceSet

end SeshadriUgander2020IIATesting
