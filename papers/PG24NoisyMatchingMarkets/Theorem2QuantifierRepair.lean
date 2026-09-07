import PG24NoisyMatchingMarkets.MainTheorems

/-!
# PG24 Theorem 2 parameter-selection bridge

The amplification appendix chooses a proof window before it handles a fixed
target value.  This file formalizes that quantifier order without treating the
window clauses as a source-model assumption.  A future proof must supply the
three displayed ingredients below: shrinking source errors, eventual target
coverage by the chosen windows, and the local source window at every covered
target.

In particular, this file does not derive either target coverage or error
shrinkage from the local interval/event clauses.  Those implications are the
open mathematical obligations exposed by `proof-amplifying.tex:27-31` and
`:100-130`.
-/

open Filter Topology

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- A target belongs to the local value window used by the Theorem 2 proof. -/
def theorem2_localWindowMembership
    (vLow vHigh vStar v : ℝ) : Prop :=
  vLow ≤ v ∧ v ≤ vHigh ∧ v ≤ vStar

/--
If the three endpoint sequences expand to cover the real line, then every
fixed target is eventually in the local Theorem 2 window.

This is the missing quantifier bridge behind the sentence at
`proof-amplifying.tex:31`.  It requires genuine lower and upper endpoint
divergence; connected or bounded support alone does not provide it.
-/
theorem theorem2_localWindowMembership_eventually_of_expanding_endpoints
    {vLow vHigh vStar : ℕ → ℝ}
    (hlow : Tendsto vLow atTop atBot)
    (hhigh : Tendsto vHigh atTop atTop)
    (hstar : Tendsto vStar atTop atTop)
    (v : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      theorem2_localWindowMembership (vLow n) (vHigh n) (vStar n) v := by
  filter_upwards [tendsto_atBot.mp hlow v, tendsto_atTop.mp hhigh v,
    tendsto_atTop.mp hstar v] with n hlow_n hhigh_n hstar_n
  exact ⟨hlow_n, hhigh_n, hstar_n⟩

/--
A family whose upper endpoints are eventually bounded cannot establish the
all-real-target coverage claimed in the current local-event package.

For example, the source's quantile windows for a value law supported on
`[0, 1]` have upper endpoint at most `1`, so they cannot cover target value
`2`.  Such a bounded connected support is not excluded by `model.tex:15-17`.
-/
theorem theorem2_not_forall_eventually_upper_covered_of_eventually_upper_bounded
    {vHigh : ℕ → ℝ} {bound : ℝ}
    (hbounded : ∀ᶠ n : ℕ in atTop, vHigh n ≤ bound) :
    ¬ (∀ v : ℝ, ∀ᶠ n : ℕ in atTop, v ≤ vHigh n) := by
  intro hcoverage
  rcases (hbounded.and (hcoverage (bound + 1))).exists with ⟨n, hbound, hcover⟩
  linarith

/--
The correct Theorem 2 closure for a source-selected parameter schedule.

Unlike the pre-existing fixed-parameter closure, `epsilon n` and `sigma n`
may be selected together by the source proof.  The conclusion follows once
their two displayed errors vanish and the corresponding local source window
holds at every target eventually covered by its endpoints.
-/
theorem theorem2_uniformAmplification_of_expanding_local_source_windows
    {Admissible : ℕ → Type*}
    {matchProb : ∀ C : ℕ, Admissible C → ℝ → ℝ}
    {totalSupply alpha : ℝ}
    (epsilon sigma vLow vHigh vStar : ℕ → ℝ)
    (hlower_error :
      Tendsto
        (fun n : ℕ => theorem2_sourceLowerError alpha (epsilon n) (sigma n))
        atTop (nhds 0))
    (hupper_error :
      Tendsto
        (fun n : ℕ =>
          theorem2_sourceUpperError totalSupply alpha (epsilon n) (sigma n))
        atTop (nhds 0))
    (hcoverage :
      ∀ v : ℝ, ∀ᶠ n : ℕ in atTop,
        theorem2_localWindowMembership (vLow n) (vHigh n) (vStar n) v)
    (hwindow :
      ∀ n v,
        theorem2_localWindowMembership (vLow n) (vHigh n) (vStar n) v →
          ∀ᶠ C : ℕ in atTop,
            ∀ mu : Admissible C,
              theorem2_totalSourceWindow totalSupply alpha (epsilon n) (sigma n)
                (matchProb C mu v)) :
    theorem2_uniformAmplificationConclusion Admissible matchProb totalSupply := by
  intro v tol htol
  have hlower_small :
      ∀ᶠ n : ℕ in atTop,
        theorem2_sourceLowerError alpha (epsilon n) (sigma n) < tol :=
    hlower_error (isOpen_Iio.mem_nhds htol)
  have hupper_small :
      ∀ᶠ n : ℕ in atTop,
        theorem2_sourceUpperError totalSupply alpha (epsilon n) (sigma n) < tol :=
    hupper_error (isOpen_Iio.mem_nhds htol)
  rcases (hlower_small.and (hupper_small.and (hcoverage v))).exists with
    ⟨n, hlower_n, hupper_n, hmember_n⟩
  filter_upwards [hwindow n v hmember_n] with C hwindow_C mu
  have hwindow_mu := hwindow_C mu
  rw [abs_sub_lt_iff]
  constructor <;> linarith [hwindow_mu.1, hwindow_mu.2]

/--
If `epsilon * sigma` stays at least one, the independent-product error in the
source window stays bounded away from zero.  Therefore an existential choice
of `sigma` after `epsilon` is insufficient for the final Theorem 2 limit;
the source proof must control their product.
-/
theorem theorem2_exp_gap_lower_bound_of_one_le_product
    {epsilon sigma : ℝ}
    (hproduct : 1 ≤ epsilon * sigma) :
    1 - Real.exp (-2 : ℝ) ≤
      1 - Real.exp (-(2 * epsilon * sigma)) := by
  have harg : -(2 * epsilon * sigma) ≤ (-2 : ℝ) := by
    nlinarith
  have hexp :
      Real.exp (-(2 * epsilon * sigma)) ≤ Real.exp (-2 : ℝ) :=
    Real.exp_monotone harg
  linarith

/--
Formal obstruction for an uncontrolled source `sigma` schedule.  This is the
failure mode left open by `proof-amplifying.tex:100-130`: its existence proof
for `sigma` supplies no asymptotic upper bound on `epsilon * sigma`.
-/
theorem theorem2_exp_gap_not_tendsto_zero_of_eventually_one_le_product
    {epsilon sigma : ℕ → ℝ}
    (hproduct : ∀ᶠ n : ℕ in atTop, 1 ≤ epsilon n * sigma n) :
    ¬ Tendsto
      (fun n : ℕ => 1 - Real.exp (-(2 * epsilon n * sigma n)))
      atTop (nhds 0) := by
  intro hgap
  have hpositive : 0 < 1 - Real.exp (-2 : ℝ) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hsmall :
      ∀ᶠ n : ℕ in atTop,
        1 - Real.exp (-(2 * epsilon n * sigma n)) <
          (1 - Real.exp (-2 : ℝ)) / 2 :=
    hgap (isOpen_Iio.mem_nhds (div_pos hpositive (by norm_num)))
  rcases (hproduct.and hsmall).exists with ⟨n, hproduct_n, hsmall_n⟩
  have hlower := theorem2_exp_gap_lower_bound_of_one_le_product hproduct_n
  linarith

end

end PG24NoisyMatchingMarkets
