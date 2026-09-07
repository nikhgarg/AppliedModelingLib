import LMMS04FairDivision.Theorem31AdaptiveQuery
import AppliedModelingLib.Foundations.Math.Asymptotics

open Filter Topology
open AppliedModelingLib.FairDivision

namespace LMMS04FairDivision
namespace Theorem31

/-!
# LMMS Theorem 3.1: asymptotic query lower-bound wrapper

The finite adaptive-query endpoint proves failure whenever `2 * q` is smaller
than the number of middle-complement pairs.  This file packages the last
asymptotic seam: if the normalized query budget tends to zero relative to that
middle-pair count, then that finite inequality holds eventually, and the
adaptive lower-bound theorem applies eventually along a sequence of hard
instances.
-/

/--
Real asymptotic bridge for the Theorem 3.1 query scale.  If twice the query
budget is `o(card)` and the comparison cardinality is eventually positive,
then the finite transcript-count inequality `2 * q < card` holds eventually.
-/
theorem eventually_two_mul_lt_card_of_tendsToZero_ratio
    (q card : ℕ → ℕ)
    (hratio :
      AppliedModelingLib.Math.TendsToZero fun n =>
        (((2 * q n : ℕ) : ℝ) / (card n : ℝ)))
    (hcard_pos : ∀ᶠ n in atTop, 0 < card n) :
    ∀ᶠ n in atTop, 2 * q n < card n := by
  rw [AppliedModelingLib.Math.TendsToZero] at hratio
  have hlt_one :
      ∀ᶠ n in atTop,
        (((2 * q n : ℕ) : ℝ) / (card n : ℝ)) < 1 :=
    hratio.eventually (eventually_lt_nhds zero_lt_one)
  filter_upwards [hlt_one, hcard_pos] with n hratio_lt hcard_n_pos
  have hcard_real_pos : 0 < (card n : ℝ) := by
    exact_mod_cast hcard_n_pos
  have hlt_real : ((2 * q n : ℕ) : ℝ) < (card n : ℝ) := by
    calc
      ((2 * q n : ℕ) : ℝ) =
          (((2 * q n : ℕ) : ℝ) / (card n : ℝ)) * (card n : ℝ) := by
            field_simp [ne_of_gt hcard_real_pos]
      _ < 1 * (card n : ℝ) :=
          mul_lt_mul_of_pos_right hratio_lt hcard_real_pos
      _ = (card n : ℝ) := by ring
  exact_mod_cast hlt_real

/--
Eventually source-shaped adaptive lower bound for minimum envy.  Along any
sequence of middle-complement-pair certificates, an eventually sub-half-pair
two-bit query budget cannot solve all crossed hard profiles eventually.
-/
theorem eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries_of_eventually_two_mul_lt
    {Item : ℕ → Type*} [∀ n, Fintype (Item n)] [∀ n, DecidableEq (Item n)]
    {k q : ℕ → ℕ}
    (C : ∀ n, LMMS31MiddleComplementPairs (Item n) (k n))
    (hcard_items : ∀ n, Fintype.card (Item n) = 2 * k n)
    (strategy : ∀ n, AdaptiveQueryStrategy (Finset (Item n)) (Bool × Bool))
    (output :
      ∀ n, QueryTranscript (Bool × Bool) (q n) →
        Allocation LMMS31Agent (Item n))
    (hquery_bound :
      ∀ᶠ n in atTop, 2 * q n < Fintype.card (C n).Pair) :
    ∀ᶠ n in atTop,
      ¬ ∀ choice₁ choice₂,
        MinimumReportEnvyAllocation
          (lmms31CrossReport
            ((C n).hardFunctionOfMiddleChoice choice₁)
            ((C n).hardFunctionOfMiddleChoice choice₂))
          (Finset.univ : Finset (Item n))
          (output n
            (twoPlayerHardFunctionAdaptiveTranscript (strategy n)
              ((C n).hardFunctionOfMiddleChoice choice₁)
              ((C n).hardFunctionOfMiddleChoice choice₂))) := by
  filter_upwards [hquery_bound] with n hquery_bound_n
  exact
    (C n).minimum_envy_lower_bound_from_twoBit_adaptive_queries_of_two_mul_lt
      (hcard_items n) (strategy n) (output n) hquery_bound_n

/--
Eventually source-shaped adaptive lower bound for minimum envy-ratio, using the
same eventual two-bit query-budget comparison.
-/
theorem eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries_of_eventually_two_mul_lt
    {Item : ℕ → Type*} [∀ n, Fintype (Item n)] [∀ n, DecidableEq (Item n)]
    {k q : ℕ → ℕ}
    (C : ∀ n, LMMS31MiddleComplementPairs (Item n) (k n))
    (hcard_items : ∀ n, Fintype.card (Item n) = 2 * k n)
    (strategy : ∀ n, AdaptiveQueryStrategy (Finset (Item n)) (Bool × Bool))
    (output :
      ∀ n, QueryTranscript (Bool × Bool) (q n) →
        Allocation LMMS31Agent (Item n))
    (hquery_bound :
      ∀ᶠ n in atTop, 2 * q n < Fintype.card (C n).Pair) :
    ∀ᶠ n in atTop,
      ¬ ∀ choice₁ choice₂,
        MinimumReportEnvyRatioAllocation
          (lmms31CrossReport
            ((C n).hardFunctionOfMiddleChoice choice₁)
            ((C n).hardFunctionOfMiddleChoice choice₂))
          (Finset.univ : Finset (Item n))
          (output n
            (twoPlayerHardFunctionAdaptiveTranscript (strategy n)
              ((C n).hardFunctionOfMiddleChoice choice₁)
              ((C n).hardFunctionOfMiddleChoice choice₂))) := by
  filter_upwards [hquery_bound] with n hquery_bound_n
  exact
    (C n).minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries_of_two_mul_lt
      (hcard_items n) (strategy n) (output n) hquery_bound_n

/--
Asymptotic adaptive lower bound for minimum envy.  It is enough to prove that
the two-bit query budget is asymptotically negligible relative to the number of
middle complement pairs.
-/
theorem eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries_of_tendsToZero_ratio
    {Item : ℕ → Type*} [∀ n, Fintype (Item n)] [∀ n, DecidableEq (Item n)]
    {k q : ℕ → ℕ}
    (C : ∀ n, LMMS31MiddleComplementPairs (Item n) (k n))
    (hcard_items : ∀ n, Fintype.card (Item n) = 2 * k n)
    (strategy : ∀ n, AdaptiveQueryStrategy (Finset (Item n)) (Bool × Bool))
    (output :
      ∀ n, QueryTranscript (Bool × Bool) (q n) →
        Allocation LMMS31Agent (Item n))
    (hquery_ratio :
      AppliedModelingLib.Math.TendsToZero fun n =>
        (((2 * q n : ℕ) : ℝ) / (Fintype.card (C n).Pair : ℝ)))
    (hpair_pos : ∀ᶠ n in atTop, 0 < Fintype.card (C n).Pair) :
    ∀ᶠ n in atTop,
      ¬ ∀ choice₁ choice₂,
        MinimumReportEnvyAllocation
          (lmms31CrossReport
            ((C n).hardFunctionOfMiddleChoice choice₁)
            ((C n).hardFunctionOfMiddleChoice choice₂))
          (Finset.univ : Finset (Item n))
          (output n
            (twoPlayerHardFunctionAdaptiveTranscript (strategy n)
              ((C n).hardFunctionOfMiddleChoice choice₁)
              ((C n).hardFunctionOfMiddleChoice choice₂))) :=
  eventually_minimum_envy_lower_bound_from_twoBit_adaptive_queries_of_eventually_two_mul_lt
    C hcard_items strategy output
    (eventually_two_mul_lt_card_of_tendsToZero_ratio q
      (fun n => Fintype.card (C n).Pair) hquery_ratio hpair_pos)

/--
Asymptotic adaptive lower bound for minimum envy-ratio, from the same
negligible-query-budget condition.
-/
theorem eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries_of_tendsToZero_ratio
    {Item : ℕ → Type*} [∀ n, Fintype (Item n)] [∀ n, DecidableEq (Item n)]
    {k q : ℕ → ℕ}
    (C : ∀ n, LMMS31MiddleComplementPairs (Item n) (k n))
    (hcard_items : ∀ n, Fintype.card (Item n) = 2 * k n)
    (strategy : ∀ n, AdaptiveQueryStrategy (Finset (Item n)) (Bool × Bool))
    (output :
      ∀ n, QueryTranscript (Bool × Bool) (q n) →
        Allocation LMMS31Agent (Item n))
    (hquery_ratio :
      AppliedModelingLib.Math.TendsToZero fun n =>
        (((2 * q n : ℕ) : ℝ) / (Fintype.card (C n).Pair : ℝ)))
    (hpair_pos : ∀ᶠ n in atTop, 0 < Fintype.card (C n).Pair) :
    ∀ᶠ n in atTop,
      ¬ ∀ choice₁ choice₂,
        MinimumReportEnvyRatioAllocation
          (lmms31CrossReport
            ((C n).hardFunctionOfMiddleChoice choice₁)
            ((C n).hardFunctionOfMiddleChoice choice₂))
          (Finset.univ : Finset (Item n))
          (output n
            (twoPlayerHardFunctionAdaptiveTranscript (strategy n)
              ((C n).hardFunctionOfMiddleChoice choice₁)
              ((C n).hardFunctionOfMiddleChoice choice₂))) :=
  eventually_minimum_envy_ratio_lower_bound_from_twoBit_adaptive_queries_of_eventually_two_mul_lt
    C hcard_items strategy output
    (eventually_two_mul_lt_card_of_tendsToZero_ratio q
      (fun n => Fintype.card (C n).Pair) hquery_ratio hpair_pos)

end Theorem31
end LMMS04FairDivision
