import LBG22StrategicRanking.SecondPrice
import LBG22StrategicRanking.GammaRank

namespace LBG22StrategicRanking

open Filter
open MeasureTheory

/-!
Finite and ordered-band wrappers around the source-shaped second-price lemmas.

The statements below keep every analytic and boundary assumption explicit.
They are intended as small bridge lemmas for finite reward partitions: a
finite set of previous-band scores, adjacent reward levels, and monotone
boundary efforts indexed by an ordered band type.
-/

/--
Package a bounded source rank-level value as a finite band index.  This keeps
the finite second-price endpoints from treating the actual/deviation band
classifiers as independent source data: once `rankLevel` is known to take only
the displayed finite levels, the classifier is computed from `rankLevel`
itself.
-/
def finiteRankLevel {n : ℕ} (rankLevel : ℝ → ℕ)
    (hbound : ∀ z, rankLevel z < n + 1) (z : ℝ) : Fin (n + 1) :=
  ⟨rankLevel z, hbound z⟩

@[simp]
theorem finiteRankLevel_val {n : ℕ} (rankLevel : ℝ → ℕ)
    (hbound : ∀ z, rankLevel z < n + 1) (z : ℝ) :
    (finiteRankLevel rankLevel hbound z).val = rankLevel z := rfl

/--
Finite reward-band best response on the source feasible effort domain.  This
keeps the finite second-price theorem from conflating rank values and score
values: the actual and counterfactual reward bands are explicit finite labels,
and rank preservation is proved separately from the tie-broken score order.
-/
def FiniteBandBestResponseFeasible
    {α : Type*} {n : ℕ} (e0 : ℝ) (costFn : ℝ → ℝ)
    (reward : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (effort : α → ℝ) : Prop :=
  (∀ x, e0 ≤ effort x) ∧
    ∀ x d, e0 ≤ d →
      reward (actualBand x) - costFn (effort x) ≥
        reward (deviationBand x d) - costFn d

/--
Finite score-threshold classifier: return the highest displayed band whose
lower score target is weakly reached.  If no target is reached, the classifier
defaults to the bottom band.  Paper-facing endpoints use the accompanying
lemmas with an explicit bottom-target reachability proof, so the default branch
never carries a source assumption.
-/
noncomputable def finiteScoreBand {n : ℕ}
    (target : Fin (n + 1) → ℝ) (z : ℝ) : Fin (n + 1) :=
  let feasible :=
    (Finset.univ : Finset (Fin (n + 1))).filter (fun i => target i ≤ z)
  if h : feasible.Nonempty then feasible.max' h else ⟨0, Nat.succ_pos n⟩

/-- The finite score-threshold classifier is always a bounded level. -/
theorem finiteScoreBand_val_lt {n : ℕ}
    (target : Fin (n + 1) → ℝ) (z : ℝ) :
    (finiteScoreBand target z).val < n + 1 :=
  (finiteScoreBand target z).isLt

/--
If at least one displayed target is reached, the classifier's own target is
reached.
-/
theorem finiteScoreBand_target_le_of_exists {n : ℕ}
    {target : Fin (n + 1) → ℝ} {z : ℝ}
    (hreach : ∃ i : Fin (n + 1), target i ≤ z) :
    target (finiteScoreBand target z) ≤ z := by
  classical
  let feasible :=
    (Finset.univ : Finset (Fin (n + 1))).filter (fun i => target i ≤ z)
  have hnonempty : feasible.Nonempty := by
    rcases hreach with ⟨i, hi⟩
    exact ⟨i, by simp [feasible, hi]⟩
  have hmem : feasible.max' hnonempty ∈ feasible :=
    Finset.max'_mem feasible hnonempty
  have htarget : target (feasible.max' hnonempty) ≤ z :=
    (Finset.mem_filter.mp hmem).2
  simpa [finiteScoreBand, feasible, hnonempty] using htarget

/--
If the bottom target is reached, the classifier's own target is reached.  This
is the common source use case, because all feasible scores are above the bottom
band target.
-/
theorem finiteScoreBand_target_le_of_bottom {n : ℕ}
    {target : Fin (n + 1) → ℝ} {z : ℝ}
    (hbottom : target ⟨0, Nat.succ_pos n⟩ ≤ z) :
    target (finiteScoreBand target z) ≤ z :=
  finiteScoreBand_target_le_of_exists
    (target := target) (z := z) ⟨⟨0, Nat.succ_pos n⟩, hbottom⟩

/--
Any displayed band whose target is reached is weakly below the classifier.
-/
theorem le_finiteScoreBand_of_target_le {n : ℕ}
    {target : Fin (n + 1) → ℝ} {z : ℝ} {i : Fin (n + 1)}
    (hi : target i ≤ z) :
    i ≤ finiteScoreBand target z := by
  classical
  let feasible :=
    (Finset.univ : Finset (Fin (n + 1))).filter (fun j => target j ≤ z)
  have hnonempty : feasible.Nonempty := ⟨i, by simp [feasible, hi]⟩
  have himem : i ∈ feasible := by simp [feasible, hi]
  have hle : i ≤ feasible.max' hnonempty :=
    Finset.le_max' feasible i himem
  simpa [finiteScoreBand, feasible, hnonempty] using hle

/--
Exact-band rule for the finite score-threshold classifier: if band `i` is
reached and every strictly higher band target is not reached, the classifier
returns exactly `i`.
-/
theorem finiteScoreBand_eq_of_target_interval {n : ℕ}
    {target : Fin (n + 1) → ℝ} {z : ℝ} {i : Fin (n + 1)}
    (hi : target i ≤ z)
    (hupper : ∀ j : Fin (n + 1), i < j → z < target j) :
    finiteScoreBand target z = i := by
  classical
  apply le_antisymm
  · by_contra hnot
    have hlt : i < finiteScoreBand target z := lt_of_not_ge hnot
    have htarget :=
      finiteScoreBand_target_le_of_exists
        (target := target) (z := z) ⟨i, hi⟩
    exact not_lt_of_ge htarget (hupper (finiteScoreBand target z) hlt)
  · exact le_finiteScoreBand_of_target_le (target := target) (z := z) hi

/--
If every displayed cutoff type is realized by some source applicant, positivity
of source skill transfers to positivity of the cutoff skill factor.
-/
theorem source_cutoff_pos_of_type_support
    {α β : Type*} {f : ℝ → ℝ} {theta skill : α → ℝ}
    {cutoff : β → ℝ}
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_source : ∀ x, skill x = f (theta x))
    (hcutoff_type_support : ∀ i : β, ∃ x : α, theta x = cutoff i) :
    ∀ i : β, 0 < f (cutoff i) := by
  intro i
  rcases hcutoff_type_support i with ⟨x, htheta⟩
  simpa [← htheta, ← hskill_source x] using hskill_pos x

/--
If the source second-price score lies strictly above a scalar upper bound for
all previous-band scores, then it lies strictly above each score in a finite
previous-band set.
-/
theorem secondPrice_score_gt_finite_previousBand_scores_of_cost_gap
    {ι : Type*} {previousBands : Finset ι}
    {previousScore : ι → ℝ}
    {e0 prevAtCutoff tildePrev rewardGap c theta prevSup : ℝ}
    {cost gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hfc_pos : 0 < f c)
    (hInv :
      g (gInv (g tildePrev * f c / f theta))
        = g tildePrev * f c / f theta)
    (hprevious_le_sup :
      ∀ i ∈ previousBands, previousScore i ≤ prevSup)
    (hprevSup_le : prevSup ≤ g prevAtCutoff * f c)
    (hprev_le_tilde : prevAtCutoff ≤ tildePrev)
    (hcost :
      cost tildePrev = cost prevAtCutoff + rewardGap)
    (hgap : 0 < rewardGap) :
    ∀ i ∈ previousBands,
      previousScore i
        < g (secondPriceEffort e0 gInv g f tildePrev c theta) * f theta := by
  intro i hi
  exact lt_of_le_of_lt (hprevious_le_sup i hi)
    (secondPrice_score_gt_previousBandSup_of_cost_gap
      hg_mono hg_strict hf_theta_pos hfc_pos hInv hprevSup_le
      hprev_le_tilde hcost hgap)

/--
Finite-set version with a pointwise score expression.  This is useful when
previous bands are represented by their effort/type pairs rather than by an
already-computed score.
-/
theorem secondPrice_score_gt_finite_previousBand_effort_scores_of_cost_gap
    {ι : Type*} {previousBands : Finset ι}
    {previousEffort previousType : ι → ℝ}
    {e0 prevAtCutoff tildePrev rewardGap c theta prevSup : ℝ}
    {cost gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hfc_pos : 0 < f c)
    (hInv :
      g (gInv (g tildePrev * f c / f theta))
        = g tildePrev * f c / f theta)
    (hprevious_le_sup :
      ∀ i ∈ previousBands, g (previousEffort i) * f (previousType i) ≤ prevSup)
    (hprevSup_le : prevSup ≤ g prevAtCutoff * f c)
    (hprev_le_tilde : prevAtCutoff ≤ tildePrev)
    (hcost :
      cost tildePrev = cost prevAtCutoff + rewardGap)
    (hgap : 0 < rewardGap) :
    ∀ i ∈ previousBands,
      g (previousEffort i) * f (previousType i)
        < g (secondPriceEffort e0 gInv g f tildePrev c theta) * f theta :=
  secondPrice_score_gt_finite_previousBand_scores_of_cost_gap
    hg_mono hg_strict hf_theta_pos hfc_pos hInv hprevious_le_sup
    hprevSup_le hprev_le_tilde hcost hgap

/--
Source second-price actual-cost bound, indexed by an arbitrary finite-band
label: if the displayed effort formula reaches its own boundary score, then
its cost is weakly below the boundary effort cost for that band.
-/
theorem secondPrice_actualCost_le_boundary_of_effort_formula
    {α β : Type*} {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (tilde cutoff : β → ℝ) (band : α → β) (theta effort : α → ℝ)
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i, e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hactual_reaches_boundary :
      ∀ x, g (tilde (band x)) * f (cutoff (band x)) ≤
        g (tilde (band x)) * f (theta x))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (band x))
          (cutoff (band x)) (theta x)) :
    ∀ x, costFn (effort x) ≤ costFn (tilde (band x)) := by
  intro x
  rw [heffort_formula x]
  exact
    secondPriceEffort_cost_le_of_reaches_boundary_score_of_rightInverse
      hg_strict (hf_theta_pos x) hInv hcost_mono
      (htilde_feasible (band x)) (hactual_reaches_boundary x)

/--
Same-band finite deviation-cost bound for the source second-price formula:
if a same-band deviation still has to reach the same boundary score, then the
displayed effort is minimum-cost among such deviations.
-/
theorem secondPrice_sameBandCost_le_of_effort_formula
    {α β : Type*} {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (tilde cutoff : β → ℝ) (band : α → β)
    (deviationBand : α → ℝ → β) (theta effort : α → ℝ)
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hdeviation_feasible :
      ∀ x d, deviationBand x d = band x → e0 ≤ d)
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = band x →
        g (tilde (band x)) * f (cutoff (band x)) ≤ g d * f (theta x))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (band x))
          (cutoff (band x)) (theta x)) :
    ∀ x d, deviationBand x d = band x → costFn (effort x) ≤ costFn d := by
  intro x d hsame
  rw [heffort_formula x]
  exact
    secondPriceEffort_cost_le_of_reaches_boundary_score_of_rightInverse
      hg_strict (hf_theta_pos x) hInv hcost_mono
      (hdeviation_feasible x d hsame)
      (hsame_reaches_boundary x d hsame)

/--
Upward finite deviation-cost bound: if reaching a higher band forces the
deviating effort to clear that band's cutoff-boundary score, then monotone
cost and strict score effort imply the deviation costs at least the target
band's boundary effort.
-/
theorem secondPrice_upwardCost_ge_boundary_of_score_boundary
    {α β : Type*} [Preorder β] {costFn g f : ℝ → ℝ} {e0 : ℝ}
    (tilde cutoff : β → ℝ) (band : α → β)
    (deviationBand : α → ℝ → β)
    (hg_strict : StrictMono g)
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i, e0 ≤ tilde i)
    (hf_cutoff_pos : ∀ i, 0 < f (cutoff i))
    (hdeviation_feasible :
      ∀ x d, band x < deviationBand x d → e0 ≤ d)
    (hup_reaches_boundary :
      ∀ x d, band x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d))) :
    ∀ x d, band x < deviationBand x d →
      costFn (tilde (deviationBand x d)) ≤ costFn d := by
  intro x d hup
  have hscore : g (tilde (deviationBand x d)) ≤ g d := by
    exact le_of_mul_le_mul_right
      (hup_reaches_boundary x d hup)
      (hf_cutoff_pos (deviationBand x d))
  have htilde_le : tilde (deviationBand x d) ≤ d :=
    hg_strict.le_iff_le.mp hscore
  exact hcost_mono
    (htilde_feasible (deviationBand x d))
    (hdeviation_feasible x d hup)
    htilde_le

/--
Actual-band reachability from the source type interval: if the realized type is
above its band cutoff and the boundary score factor is nonnegative, then the
actual boundary effort reaches its own cutoff score.
-/
theorem secondPrice_actual_reaches_boundary_of_cutoff_le_theta
    {α β : Type*} {g f : ℝ → ℝ}
    (tilde cutoff : β → ℝ) (band : α → β) (theta : α → ℝ)
    (hf_mono : Monotone f)
    (hg_boundary_nonneg : ∀ x, 0 ≤ g (tilde (band x)))
    (hcutoff_le_theta : ∀ x, cutoff (band x) ≤ theta x) :
    ∀ x, g (tilde (band x)) * f (cutoff (band x)) ≤
      g (tilde (band x)) * f (theta x) := by
  intro x
  exact mul_le_mul_of_nonneg_left
    (hf_mono (hcutoff_le_theta x)) (hg_boundary_nonneg x)

/--
Same-band reachability from source interval facts: if a same-band deviation
uses at least the current band's boundary effort and the applicant type is
above that band's cutoff, then it reaches the same boundary score.
-/
theorem secondPrice_same_reaches_boundary_of_boundary_le_deviation_and_cutoff_le_theta
    {α β : Type*} {g f : ℝ → ℝ}
    (tilde cutoff : β → ℝ) (band : α → β)
    (deviationBand : α → ℝ → β) (theta : α → ℝ)
    (hg_mono : Monotone g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_cutoff_nonneg : ∀ i, 0 ≤ f (cutoff i))
    (hboundary_le_deviation :
      ∀ x d, deviationBand x d = band x → tilde (band x) ≤ d)
    (hcutoff_le_theta : ∀ x, cutoff (band x) ≤ theta x) :
    ∀ x d, deviationBand x d = band x →
      g (tilde (band x)) * f (cutoff (band x)) ≤ g d * f (theta x) := by
  intro x d hsame
  have hg_le : g (tilde (band x)) ≤ g d :=
    hg_mono (hboundary_le_deviation x d hsame)
  have hf_le : f (cutoff (band x)) ≤ f (theta x) :=
    hf_mono (hcutoff_le_theta x)
  exact mul_le_mul hg_le hf_le
    (hf_cutoff_nonneg (band x)) (hg_nonneg d)

/--
Upward-band reachability from source threshold facts: if an upward deviation
uses at least the target band's boundary effort, then it reaches that band's
cutoff score.
-/
theorem secondPrice_up_reaches_boundary_of_boundary_le_deviation
    {α β : Type*} [Preorder β] {g f : ℝ → ℝ}
    (tilde cutoff : β → ℝ) (band : α → β)
    (deviationBand : α → ℝ → β)
    (hg_mono : Monotone g)
    (hf_cutoff_nonneg : ∀ i, 0 ≤ f (cutoff i))
    (hboundary_le_deviation :
      ∀ x d, band x < deviationBand x d → tilde (deviationBand x d) ≤ d) :
    ∀ x d, band x < deviationBand x d →
      g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
        g d * f (cutoff (deviationBand x d)) := by
  intro x d hup
  exact mul_le_mul_of_nonneg_right
    (hg_mono (hboundary_le_deviation x d hup))
    (hf_cutoff_nonneg (deviationBand x d))

/--
Monotonicity of the source boundary target
`g(tilde i) * f(cutoff i)` from monotone boundary efforts and cutoffs.
-/
theorem secondPrice_bandTarget_mono_of_mono
    {β : Type*} [Preorder β] {g f : ℝ → ℝ}
    {tilde cutoff : β → ℝ}
    (hg_mono : Monotone g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_cutoff_nonneg : ∀ i, 0 ≤ f (cutoff i))
    (htilde_mono : Monotone tilde)
    (hcutoff_mono : Monotone cutoff) :
    Monotone (fun i : β => g (tilde i) * f (cutoff i)) := by
  intro i j hij
  have hg_le : g (tilde i) ≤ g (tilde j) :=
    hg_mono (htilde_mono hij)
  have hf_le : f (cutoff i) ≤ f (cutoff j) :=
    hf_mono (hcutoff_mono hij)
  exact mul_le_mul hg_le hf_le (hf_cutoff_nonneg i) (hg_nonneg (tilde j))

/--
Adjacent ordered-band no-profit inequality, written with generic band labels.
The order relation is intentionally not used in the proof: adjacency/order is
part of the caller's explicit choice of `prevBand` and `nextBand`.
-/
theorem secondPrice_orderedBand_adjacent_boundary_no_profit_of_cost_equation
    {β : Type*} [Preorder β] {prevBand nextBand : β}
    {reward : β → ℝ} {prevCost boundaryCost : ℝ}
    (hcost :
      boundaryCost = prevCost + (reward nextBand - reward prevBand)) :
    reward nextBand - boundaryCost ≤ reward prevBand - prevCost :=
  secondPrice_adjacent_boundary_no_profit_of_cost_equation hcost

/--
If the deviation cost is below the adjacent-boundary cost, deviating upward to
the next ordered band is strictly profitable.
-/
theorem secondPrice_orderedBand_adjacent_boundary_profit_of_lower_cost
    {β : Type*} [Preorder β] {prevBand nextBand : β}
    {reward : β → ℝ} {prevCost devCost boundaryCost : ℝ}
    (hcost :
      boundaryCost = prevCost + (reward nextBand - reward prevBand))
    (hdev : devCost < boundaryCost) :
    reward prevBand - prevCost < reward nextBand - devCost :=
  secondPrice_adjacent_boundary_profit_of_lower_cost hcost hdev

/--
Downward no-profit from a cost-saving bound: if moving from the high reward to
the low reward saves no more cost than the reward loss, the lower reward is not
profitable.
-/
theorem secondPrice_downward_no_profit_of_cost_saving_le_reward_gap
    {rewardLow rewardHigh actualCost deviationCost : ℝ}
    (hsaving : actualCost - deviationCost ≤ rewardHigh - rewardLow) :
    rewardLow - deviationCost ≤ rewardHigh - actualCost := by
  linarith

/--
Convexity version of the source downward no-profit step.  The boundary
applicant's interval `[boundaryLow, boundaryHigh]` is shifted to the right and
longer than the actual applicant's downward interval `[deviation, actual]`;
strictly convex/increasing cost therefore makes the actual cost saving smaller
than the boundary cost gap, which equals the reward gap by the second-price
boundary equation.
-/
theorem secondPrice_downward_no_profit_of_convex_boundary_gap
    {costFn : ℝ → ℝ} {e0 deviation actual boundaryLow boundaryHigh : ℝ}
    {rewardLow rewardHigh : ℝ}
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hdeviation_feasible : e0 ≤ deviation)
    (hboundaryLow_feasible : e0 ≤ boundaryLow)
    (hactual_gt_deviation : deviation < actual)
    (hactual_le_boundaryHigh : actual ≤ boundaryHigh)
    (hlen : actual - deviation < boundaryHigh - boundaryLow)
    (hboundaryGap :
      rewardHigh - rewardLow = costFn boundaryHigh - costFn boundaryLow) :
    rewardLow - costFn deviation ≤ rewardHigh - costFn actual := by
  have hactual_feasible : e0 ≤ actual :=
    le_trans hdeviation_feasible (le_of_lt hactual_gt_deviation)
  have hsaving :
      costFn actual - costFn deviation ≤ rewardHigh - rewardLow := by
    rw [hboundaryGap]
    by_cases hdeviation_le_boundaryLow : deviation ≤ boundaryLow
    · have hboundary_order : boundaryLow < boundaryHigh := by
        have hactual_len_pos : 0 < actual - deviation :=
          sub_pos.mpr hactual_gt_deviation
        have hboundary_len_pos : 0 < boundaryHigh - boundaryLow :=
          lt_trans hactual_len_pos hlen
        linarith
      exact le_of_lt
        (convex_strictMono_increment_lt_of_shifted_longer_interval
          hcost_conv hcost_strict hdeviation_feasible hactual_gt_deviation
          hboundary_order hdeviation_le_boundaryLow hactual_le_boundaryHigh
          hlen)
    · have hboundaryLow_le_deviation : boundaryLow ≤ deviation :=
        le_of_lt (lt_of_not_ge hdeviation_le_boundaryLow)
      have hboundaryHigh_feasible : e0 ≤ boundaryHigh :=
        le_trans hactual_feasible hactual_le_boundaryHigh
      have hcost_low_le_deviation :
          costFn boundaryLow ≤ costFn deviation :=
        hcost_strict.monotoneOn hboundaryLow_feasible hdeviation_feasible
          hboundaryLow_le_deviation
      have hcost_actual_le_high :
          costFn actual ≤ costFn boundaryHigh :=
        hcost_strict.monotoneOn hactual_feasible hboundaryHigh_feasible
          hactual_le_boundaryHigh
      linarith
  exact secondPrice_downward_no_profit_of_cost_saving_le_reward_gap hsaving

/--
Nat-indexed finite telescoping on an interval: if every adjacent upward move
from `i` through `i + d` is not profitable, then the whole upward move is not
profitable.
-/
theorem secondPrice_nat_chain_no_profit_of_adjacent_from
    (utility : ℕ → ℝ) (i d : ℕ)
    (hadj :
      ∀ k, i ≤ k → k < i + d → utility (k + 1) ≤ utility k) :
    utility (i + d) ≤ utility i := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hlast : utility (i + (d + 1)) ≤ utility (i + d) := by
        have hle : i ≤ i + d := Nat.le_add_right i d
        have hlt : i + d < i + (d + 1) :=
          Nat.add_lt_add_left (Nat.lt_succ_self d) i
        simpa [Nat.add_assoc, Nat.succ_eq_add_one] using
          hadj (i + d) hle hlt
      have hprefix : utility (i + d) ≤ utility i := by
        refine ih ?_
        intro k hik hk
        exact hadj k hik
          (Nat.lt_trans hk (Nat.add_lt_add_left (Nat.lt_succ_self d) i))
      exact le_trans hlast hprefix

/--
Reverse Nat-indexed finite telescoping on an interval: if every adjacent
downward move from `i + d` through `i` is not profitable, then the whole
downward move is not profitable.
-/
theorem secondPrice_nat_reverse_chain_no_profit_of_adjacent_from
    (utility : ℕ → ℝ) (i d : ℕ)
    (hadj :
      ∀ k, i ≤ k → k < i + d → utility k ≤ utility (k + 1)) :
    utility i ≤ utility (i + d) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hprefix : utility i ≤ utility (i + d) := by
        refine ih ?_
        intro k hik hk
        exact hadj k hik
          (Nat.lt_trans hk (Nat.add_lt_add_left (Nat.lt_succ_self d) i))
      have hlast : utility (i + d) ≤ utility (i + (d + 1)) := by
        have hle : i ≤ i + d := Nat.le_add_right i d
        have hlt : i + d < i + (d + 1) :=
          Nat.add_lt_add_left (Nat.lt_succ_self d) i
        simpa [Nat.add_assoc, Nat.succ_eq_add_one] using
          hadj (i + d) hle hlt
      exact le_trans hprefix hlast

/--
Finite telescoping no-profit inequality: if every adjacent upward move in a
finite chain is not profitable, then the total upward move across the chain is
not profitable.
-/
theorem secondPrice_fin_chain_no_profit_of_adjacent
    {n : ℕ} (reward cost : Fin (n + 1) → ℝ)
    (hadj :
      ∀ k : Fin n,
        reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
            - cost ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
          ≤ reward ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
            - cost ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩) :
    reward ⟨n, Nat.lt_succ_self n⟩ - cost ⟨n, Nat.lt_succ_self n⟩
      ≤ reward ⟨0, Nat.succ_pos n⟩ - cost ⟨0, Nat.succ_pos n⟩ := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hlast := hadj ⟨n, Nat.lt_succ_self n⟩
      have hprefix :
          ∀ k : Fin n,
            reward ⟨k.val + 1,
                Nat.lt_trans (Nat.succ_lt_succ k.isLt) (Nat.lt_succ_self (n + 1))⟩
                - cost ⟨k.val + 1,
                    Nat.lt_trans (Nat.succ_lt_succ k.isLt) (Nat.lt_succ_self (n + 1))⟩
              ≤ reward ⟨k.val,
                    Nat.lt_trans k.isLt (Nat.lt_succ_of_lt (Nat.lt_succ_self n))⟩
                - cost ⟨k.val,
                    Nat.lt_trans k.isLt (Nat.lt_succ_of_lt (Nat.lt_succ_self n))⟩ := by
        intro k
        simpa using hadj ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
      have hchain :=
        ih (fun i : Fin (n + 1) =>
            reward ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self (n + 1))⟩)
          (fun i : Fin (n + 1) =>
            cost ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self (n + 1))⟩)
          hprefix
      exact le_trans hlast hchain

/--
All-pairs finite-chain version: adjacent upward no-profit inequalities imply
that no lower-index band can profit by jumping to any weakly higher-index band.
-/
theorem secondPrice_fin_utility_chain_no_profit_of_adjacent_between
    {n : ℕ} (utility : Fin (n + 1) → ℝ)
    (hadj :
      ∀ k : Fin n,
        utility ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
          ≤ utility ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    utility j ≤ utility i := by
  let utilityNat : ℕ → ℝ := fun m =>
    if h : m ≤ n then utility ⟨m, Nat.lt_succ_of_le h⟩ else 0
  have hdist : i.val + (j.val - i.val) = j.val :=
    Nat.add_sub_of_le hij
  have hchain :
      utilityNat (i.val + (j.val - i.val)) ≤ utilityNat i.val := by
    refine
      secondPrice_nat_chain_no_profit_of_adjacent_from
        utilityNat i.val (j.val - i.val) ?_
    intro k hik hk
    have hk_lt_j : k < j.val := by
      simpa [hdist] using hk
    have hj_le_n : j.val ≤ n := Nat.lt_succ_iff.mp j.isLt
    have hk_lt_n : k < n := Nat.lt_of_lt_of_le hk_lt_j hj_le_n
    have hk_le_n : k ≤ n := Nat.le_of_lt hk_lt_n
    have hksucc_le_n : k + 1 ≤ n := Nat.succ_le_of_lt hk_lt_n
    simpa [utilityNat, hk_le_n, hksucc_le_n] using
      hadj ⟨k, hk_lt_n⟩
  have hchain' : utilityNat j.val ≤ utilityNat i.val := by
    simpa [hdist] using hchain
  have hi_le_n : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
  have hj_le_n : j.val ≤ n := Nat.lt_succ_iff.mp j.isLt
  simpa [utilityNat, hi_le_n, hj_le_n] using hchain'

/--
Reward/cost all-pairs finite-chain version of
`secondPrice_fin_chain_no_profit_of_adjacent`: adjacent upward no-profit
inequalities rule out every upward jump along the finite chain.
-/
theorem secondPrice_fin_chain_no_profit_of_adjacent_between
    {n : ℕ} (reward cost : Fin (n + 1) → ℝ)
    (hadj :
      ∀ k : Fin n,
        reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
            - cost ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
          ≤ reward ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
            - cost ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    reward j - cost j ≤ reward i - cost i :=
  secondPrice_fin_utility_chain_no_profit_of_adjacent_between
    (fun k => reward k - cost k) hadj hij

/--
Cost-equation version of the finite upward no-profit chain: if each adjacent
boundary cost is exactly the previous cost plus the adjacent reward gap, then
adjacent no-profit inequalities hold with equality and telescope across the
finite chain.
-/
theorem secondPrice_fin_chain_no_profit_of_adjacent_cost_equations
    {n : ℕ} (reward cost : Fin (n + 1) → ℝ)
    (hcost :
      ∀ k : Fin n,
        cost ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ =
          cost ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
            + (reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
              - reward ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩)) :
    ∀ {i j : Fin (n + 1)}, i ≤ j →
      reward j - cost j ≤ reward i - cost i := by
  intro i j hij
  exact secondPrice_fin_chain_no_profit_of_adjacent_between reward cost
    (by
      intro k
      have hk := hcost k
      rw [hk]
      linarith)
    hij

/--
Reverse all-pairs finite-chain version: adjacent downward no-profit
inequalities imply that no higher-index band can profit by jumping to any
weakly lower-index band.
-/
theorem secondPrice_fin_utility_reverse_chain_no_profit_of_adjacent_between
    {n : ℕ} (utility : Fin (n + 1) → ℝ)
    (hadj :
      ∀ k : Fin n,
        utility ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
          ≤ utility ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    utility i ≤ utility j := by
  let utilityNat : ℕ → ℝ := fun m =>
    if h : m ≤ n then utility ⟨m, Nat.lt_succ_of_le h⟩ else 0
  have hdist : i.val + (j.val - i.val) = j.val :=
    Nat.add_sub_of_le hij
  have hchain :
      utilityNat i.val ≤ utilityNat (i.val + (j.val - i.val)) := by
    refine
      secondPrice_nat_reverse_chain_no_profit_of_adjacent_from
        utilityNat i.val (j.val - i.val) ?_
    intro k hik hk
    have hk_lt_j : k < j.val := by
      simpa [hdist] using hk
    have hj_le_n : j.val ≤ n := Nat.lt_succ_iff.mp j.isLt
    have hk_lt_n : k < n := Nat.lt_of_lt_of_le hk_lt_j hj_le_n
    have hk_le_n : k ≤ n := Nat.le_of_lt hk_lt_n
    have hksucc_le_n : k + 1 ≤ n := Nat.succ_le_of_lt hk_lt_n
    simpa [utilityNat, hk_le_n, hksucc_le_n] using
      hadj ⟨k, hk_lt_n⟩
  have hchain' : utilityNat i.val ≤ utilityNat j.val := by
    simpa [hdist] using hchain
  have hi_le_n : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
  have hj_le_n : j.val ≤ n := Nat.lt_succ_iff.mp j.isLt
  simpa [utilityNat, hi_le_n, hj_le_n] using hchain'

/--
Reward/cost reverse all-pairs finite-chain version: adjacent downward
no-profit inequalities rule out every downward jump along the finite chain.
-/
theorem secondPrice_fin_reverse_chain_no_profit_of_adjacent_between
    {n : ℕ} (reward cost : Fin (n + 1) → ℝ)
    (hadj :
      ∀ k : Fin n,
        reward ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
            - cost ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
          ≤ reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
            - cost ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    reward i - cost i ≤ reward j - cost j :=
  secondPrice_fin_utility_reverse_chain_no_profit_of_adjacent_between
    (fun k => reward k - cost k) hadj hij

/--
Cost-equation version of the finite downward no-profit chain.
-/
theorem secondPrice_fin_reverse_chain_no_profit_of_adjacent_cost_equations
    {n : ℕ} (reward cost : Fin (n + 1) → ℝ)
    (hcost :
      ∀ k : Fin n,
        cost ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩ =
          cost ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
            + (reward ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
              - reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩)) :
    ∀ {i j : Fin (n + 1)}, i ≤ j →
      reward i - cost i ≤ reward j - cost j := by
  intro i j hij
  exact secondPrice_fin_reverse_chain_no_profit_of_adjacent_between reward cost
    (by
      intro k
      have hk := hcost k
      rw [hk]
      linarith)
    hij

/--
Two-sided cost-equation finite no-deviation wrapper: the adjacent source cost
equation rules out profitable jumps between any two finite bands in either
direction.
-/
theorem secondPrice_fin_two_sided_no_profit_of_adjacent_cost_equations
    {n : ℕ} (reward cost : Fin (n + 1) → ℝ)
    (hcost :
      ∀ k : Fin n,
        cost ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ =
          cost ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
            + (reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
              - reward ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩)) :
    (∀ {i j : Fin (n + 1)}, i ≤ j →
      reward j - cost j ≤ reward i - cost i)
    ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
      reward i - cost i ≤ reward j - cost j) :=
  ⟨fun hij =>
      secondPrice_fin_chain_no_profit_of_adjacent_cost_equations
        reward cost hcost hij,
    fun hij =>
      secondPrice_fin_reverse_chain_no_profit_of_adjacent_cost_equations
        reward cost
        (by
          intro k
          have hk := hcost k
          linarith)
        hij⟩

/--
Adjacent second-price cost equations make every finite boundary utility
`reward k - cost k` equal. This is the finite indifference core behind the
source second-price construction.
-/
theorem secondPrice_fin_boundary_utilities_equal_of_adjacent_cost_equations
    {n : ℕ} (reward cost : Fin (n + 1) → ℝ)
    (hcost :
      ∀ k : Fin n,
        cost ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩ =
          cost ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
            + (reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
              - reward ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩)) :
    ∀ i j : Fin (n + 1), reward i - cost i = reward j - cost j := by
  intro i j
  have htwo :=
    secondPrice_fin_two_sided_no_profit_of_adjacent_cost_equations
      reward cost hcost
  rcases le_total i j with hij | hji
  · have hle_ji : reward j - cost j ≤ reward i - cost i := htwo.1 hij
    have hle_ij : reward i - cost i ≤ reward j - cost j := htwo.2 hij
    linarith
  · have hle_ij : reward i - cost i ≤ reward j - cost j := htwo.1 hji
    have hle_ji : reward j - cost j ≤ reward i - cost i := htwo.2 hji
    linarith

/--
Finite source-equation existence wrapper for the second-price construction.
If every boundary cost target from the source formula has a feasible effort
solution, and cost is strictly increasing on feasible efforts, then the
finite boundary efforts exist uniquely and make all boundary utilities equal.
-/
theorem secondPrice_fin_boundaryEfforts_exist_unique_and_indifferent
    {n : ℕ} (reward : Fin (n + 1) → ℝ)
    {e0 baseCost : ℝ} {costFn : ℝ → ℝ}
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hexists :
      ∀ i : Fin (n + 1),
        ∃ tilde, e0 ≤ tilde ∧
          costFn tilde =
            baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩)) :
    ∃ tilde : Fin (n + 1) → ℝ,
      (∀ i : Fin (n + 1),
        e0 ≤ tilde i ∧
          costFn (tilde i) =
            baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
      ∧ (∀ i : Fin (n + 1),
        ∃! z, e0 ≤ z ∧
          costFn z =
            baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
      ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
        reward j - costFn (tilde j) ≤ reward i - costFn (tilde i))
      ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
        reward i - costFn (tilde i) ≤ reward j - costFn (tilde j))
      ∧ (∀ i j : Fin (n + 1),
        reward i - costFn (tilde i) =
          reward j - costFn (tilde j))
      ∧ (∀ i j : Fin (n + 1),
        reward j - costFn (tilde j) ≤ reward i - costFn (tilde i)) := by
  classical
  let tilde : Fin (n + 1) → ℝ := fun i => Classical.choose (hexists i)
  have htilde :
      ∀ i : Fin (n + 1),
        e0 ≤ tilde i ∧
          costFn (tilde i) =
            baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩) := by
    intro i
    exact Classical.choose_spec (hexists i)
  refine ⟨tilde, htilde, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact secondPrice_boundaryEffort_unique_of_exists
      hcost_strict (hexists i)
  · have hcost :
        ∀ k : Fin n,
          costFn (tilde ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) =
            costFn (tilde ⟨k.val,
              Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩)
              + (reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
                - reward ⟨k.val,
                  Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩) := by
      intro k
      have hnext := (htilde ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩).2
      have hprev :=
        (htilde ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩).2
      rw [hnext, hprev]
      ring
    intro i j hij
    exact
        (secondPrice_fin_two_sided_no_profit_of_adjacent_cost_equations
          reward (fun i => costFn (tilde i)) hcost).1 hij
  · have hcost :
        ∀ k : Fin n,
          costFn (tilde ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) =
            costFn (tilde ⟨k.val,
              Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩)
              + (reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
                - reward ⟨k.val,
                  Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩) := by
      intro k
      have hnext := (htilde ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩).2
      have hprev :=
        (htilde ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩).2
      rw [hnext, hprev]
      ring
    intro i j hij
    exact
        (secondPrice_fin_two_sided_no_profit_of_adjacent_cost_equations
          reward (fun i => costFn (tilde i)) hcost).2 hij
  · intro i j
    have hi := (htilde i).2
    have hj := (htilde j).2
    rw [hi, hj]
    ring
  · intro i j
    have hi := (htilde i).2
    have hj := (htilde j).2
    rw [hi, hj]
    linarith

/--
Finite source-equation construction from explicit cost brackets.  This is the
same conclusion as `secondPrice_fin_boundaryEfforts_exist_unique_and_indifferent`,
but each boundary target is justified by an interval on which the cost function
is continuous and crosses the target.
-/
theorem secondPrice_fin_boundaryEfforts_exist_unique_and_indifferent_of_cost_brackets
    {n : ℕ} (reward : Fin (n + 1) → ℝ)
    {e0 baseCost : ℝ} {costFn : ℝ → ℝ} {upper : Fin (n + 1) → ℝ}
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hupper : ∀ i : Fin (n + 1), e0 ≤ upper i)
    (hcost_cont :
      ∀ i : Fin (n + 1), ContinuousOn costFn (Set.Icc e0 (upper i)))
    (hlow :
      ∀ i : Fin (n + 1),
        costFn e0 ≤ baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hhigh :
      ∀ i : Fin (n + 1),
        baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩)
          ≤ costFn (upper i)) :
    ∃ tilde : Fin (n + 1) → ℝ,
      (∀ i : Fin (n + 1),
        e0 ≤ tilde i ∧
          costFn (tilde i) =
            baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
      ∧ (∀ i : Fin (n + 1),
        ∃! z, e0 ≤ z ∧
          costFn z =
            baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
      ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
        reward j - costFn (tilde j) ≤ reward i - costFn (tilde i))
      ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
        reward i - costFn (tilde i) ≤ reward j - costFn (tilde j))
      ∧ (∀ i j : Fin (n + 1),
        reward i - costFn (tilde i) =
          reward j - costFn (tilde j))
      ∧ (∀ i j : Fin (n + 1),
        reward j - costFn (tilde j) ≤ reward i - costFn (tilde i)) := by
  exact secondPrice_fin_boundaryEfforts_exist_unique_and_indifferent
    reward hcost_strict
    (by
      intro i
      rcases secondPrice_boundaryEffort_exists_of_cost_bracket
          (hupper i) (hcost_cont i) (hlow i) (hhigh i) with
        ⟨tilde, htilde_low, _htilde_high, htilde_cost⟩
      exact ⟨tilde, htilde_low, htilde_cost⟩)

/--
Finite source-equation construction from continuous unbounded cost.  This
removes the per-boundary upper-bracket certificate: every finite target is
reached because the source cost function is continuous, tends to infinity, and
the target lies above baseline cost.
-/
theorem secondPrice_fin_boundaryEfforts_exist_unique_and_indifferent_of_continuous_unbounded
    {n : ℕ} (reward : Fin (n + 1) → ℝ)
    {e0 baseCost : ℝ} {costFn : ℝ → ℝ}
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hcost_cont : Continuous costFn)
    (hcost_atTop : Tendsto costFn atTop atTop)
    (hlow :
      ∀ i : Fin (n + 1),
        costFn e0 ≤ baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩)) :
    ∃ tilde : Fin (n + 1) → ℝ,
      (∀ i : Fin (n + 1),
        e0 ≤ tilde i ∧
          costFn (tilde i) =
            baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
      ∧ (∀ i : Fin (n + 1),
        ∃! z, e0 ≤ z ∧
          costFn z =
            baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
      ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
        reward j - costFn (tilde j) ≤ reward i - costFn (tilde i))
      ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
        reward i - costFn (tilde i) ≤ reward j - costFn (tilde j))
      ∧ (∀ i j : Fin (n + 1),
        reward i - costFn (tilde i) =
          reward j - costFn (tilde j))
      ∧ (∀ i j : Fin (n + 1),
        reward j - costFn (tilde j) ≤ reward i - costFn (tilde i)) := by
  exact secondPrice_fin_boundaryEfforts_exist_unique_and_indifferent
    reward hcost_strict
    (by
      intro i
      exact secondPrice_boundaryEffort_exists_of_continuous_unbounded
        hcost_cont hcost_atTop (hlow i))

/--
Continuous-unbounded finite boundary-effort construction from monotone source
rewards.  If the baseline band has weakly lowest reward, every source boundary
cost target lies above baseline cost, so no separate low-target certificate is
needed.
-/
theorem secondPrice_fin_boundaryEfforts_exist_unique_and_indifferent_of_monotone_rewards
    {n : ℕ} (reward : Fin (n + 1) → ℝ)
    {e0 : ℝ} {costFn : ℝ → ℝ}
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hcost_cont : Continuous costFn)
    (hcost_atTop : Tendsto costFn atTop atTop)
    (hreward_base_le :
      ∀ i : Fin (n + 1), reward ⟨0, Nat.succ_pos n⟩ ≤ reward i) :
    ∃ tilde : Fin (n + 1) → ℝ,
      (∀ i : Fin (n + 1),
        e0 ≤ tilde i ∧
          costFn (tilde i) =
            costFn e0 + (reward i - reward ⟨0, Nat.succ_pos n⟩))
      ∧ (∀ i : Fin (n + 1),
        ∃! z, e0 ≤ z ∧
          costFn z =
            costFn e0 + (reward i - reward ⟨0, Nat.succ_pos n⟩))
      ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
        reward j - costFn (tilde j) ≤ reward i - costFn (tilde i))
      ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
        reward i - costFn (tilde i) ≤ reward j - costFn (tilde j))
      ∧ (∀ i j : Fin (n + 1),
        reward i - costFn (tilde i) =
          reward j - costFn (tilde j))
      ∧ (∀ i j : Fin (n + 1),
        reward j - costFn (tilde j) ≤ reward i - costFn (tilde i)) := by
  exact secondPrice_fin_boundaryEfforts_exist_unique_and_indifferent_of_continuous_unbounded
    reward hcost_strict hcost_cont hcost_atTop
    (by
      intro i
      have hreward := hreward_base_le i
      linarith)

/--
Function-level uniqueness for finite source boundary efforts.  If two boundary
effort functions satisfy the same source cost equation at every finite band,
strict monotonicity of cost on feasible efforts forces them to agree pointwise.
-/
theorem secondPrice_fin_boundaryEfforts_function_unique
    {n : ℕ} (reward : Fin (n + 1) → ℝ)
    {e0 baseCost : ℝ} {costFn : ℝ → ℝ}
    {tilde₁ tilde₂ : Fin (n + 1) → ℝ}
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde₁_mem : ∀ i, e0 ≤ tilde₁ i)
    (htilde₂_mem : ∀ i, e0 ≤ tilde₂ i)
    (htilde₁ :
      ∀ i : Fin (n + 1),
        costFn (tilde₁ i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (htilde₂ :
      ∀ i : Fin (n + 1),
        costFn (tilde₂ i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩)) :
    tilde₁ = tilde₂ := by
  funext i
  have hunique :
      ∃! z, e0 ≤ z ∧
        costFn z =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩) :=
    secondPrice_boundaryEffort_unique_of_exists hcost_strict
      ⟨tilde₁ i, htilde₁_mem i, htilde₁ i⟩
  exact hunique.unique ⟨htilde₁_mem i, htilde₁ i⟩
    ⟨htilde₂_mem i, htilde₂ i⟩

/--
Finite second-price best-response bridge.  Once the source boundary equations
make all boundary utilities equal, an applicant is a best response whenever
her actual effort pays the boundary cost for her current band and every
deviation into a band costs at least that band's boundary cost.

This is the direct economic closure step used by the rank-preservation
interface; the model-specific work is proving the two cost facts from the
second-price score thresholds, not assuming best response as a primitive.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_boundary_costs
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward boundaryCost : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost :
      ∀ x, costFn (effort x) = boundaryCost (actualBand x))
    (hdeviationCost :
      ∀ x d, boundaryCost (deviationBand x d) ≤ costFn d)
    (hboundaryUtility :
      ∀ i j : Fin (n + 1),
        reward i - boundaryCost i = reward j - boundaryCost j) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort := by
  intro x d
  let i := actualBand x
  let j := deviationBand x d
  have hleft :
      levelReward (rankLevel (rankOfEffort x (effort x))) - costFn (effort x)
        = reward i - boundaryCost i := by
    rw [hactualLevel x, hactualCost x]
    exact congrArg (fun z => z - boundaryCost i) (hlevelReward i)
  have hright_le :
      levelReward (rankLevel (rankOfEffort x d)) - costFn d
        ≤ reward j - boundaryCost j := by
    rw [hdeviationLevel x d]
    have hrewards : levelReward j.val = reward j := hlevelReward j
    linarith [hrewards, hdeviationCost x d]
  rw [hleft]
  exact le_trans hright_le (le_of_eq (hboundaryUtility j i))

/--
Finite second-price best-response bridge with the source-shaped weak actual
cost condition.  In the displayed second-price effort formula, applicants
inside a band can pay weakly less than the boundary applicant.  Equal boundary
utilities and expensive deviations are still enough: actual utility is at
least the boundary utility for the actual band, and every deviation utility is
at most the boundary utility for the deviation band.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_boundary_costs_actual_le
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward boundaryCost : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ boundaryCost (actualBand x))
    (hdeviationCost :
      ∀ x d, boundaryCost (deviationBand x d) ≤ costFn d)
    (hboundaryUtility :
      ∀ i j : Fin (n + 1),
        reward i - boundaryCost i = reward j - boundaryCost j) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort := by
  intro x d
  let i := actualBand x
  let j := deviationBand x d
  have hactual_lower :
      reward i - boundaryCost i ≤
        levelReward (rankLevel (rankOfEffort x (effort x))) - costFn (effort x) := by
    rw [hactualLevel x]
    have hrewards : levelReward i.val = reward i := hlevelReward i
    linarith [hrewards, hactualCost_le x]
  have hdeviation_upper :
      levelReward (rankLevel (rankOfEffort x d)) - costFn d
        ≤ reward j - boundaryCost j := by
    rw [hdeviationLevel x d]
    have hrewards : levelReward j.val = reward j := hlevelReward j
    linarith [hrewards, hdeviationCost x d]
  exact le_trans hdeviation_upper
    (le_trans (le_of_eq (hboundaryUtility j i)) hactual_lower)

/--
Finite second-price best-response bridge with direction-aware deviation
bounds.  This is closer to the source economics than the uniform boundary-cost
premise: same-band deviations must not reduce cost, upward deviations must pay
the target boundary cost, and downward deviations are checked by a direct
lower-reward/no-profit inequality.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_boundary_costs_directional
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward boundaryCost : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ boundaryCost (actualBand x))
    (hsameCost :
      ∀ x d, deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d)
    (hupCost :
      ∀ x d, actualBand x < deviationBand x d →
        boundaryCost (deviationBand x d) ≤ costFn d)
    (hdownNoProfit :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - boundaryCost (actualBand x))
    (hboundaryUtility :
      ∀ i j : Fin (n + 1),
        reward i - boundaryCost i = reward j - boundaryCost j) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort := by
  intro x d
  let i := actualBand x
  let j := deviationBand x d
  have hactual_reward :
      levelReward (rankLevel (rankOfEffort x (effort x))) = reward i := by
    rw [hactualLevel x]
    exact hlevelReward i
  have hdev_reward :
      levelReward (rankLevel (rankOfEffort x d)) = reward j := by
    rw [hdeviationLevel x d]
    exact hlevelReward j
  have hactual_lower :
      reward i - boundaryCost i ≤
        levelReward (rankLevel (rankOfEffort x (effort x))) -
          costFn (effort x) := by
    rw [hactual_reward]
    linarith [hactualCost_le x]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hdeviation_upper :
        levelReward (rankLevel (rankOfEffort x d)) - costFn d
          ≤ reward j - boundaryCost j := by
      rw [hdev_reward]
      linarith [hupCost x d hij]
    exact le_trans hdeviation_upper
      (le_trans (le_of_eq (hboundaryUtility j i)) hactual_lower)
  · have hsame : j = i := hij.symm
    rw [hdev_reward, hactual_reward]
    have hreward_eq : reward j = reward i := by rw [hsame]
    linarith [hsameCost x d hsame]
  · have hdeviation_upper :
        levelReward (rankLevel (rankOfEffort x d)) - costFn d
          ≤ reward i - boundaryCost i := by
      rw [hdev_reward]
      exact hdownNoProfit x d hij
    exact le_trans hdeviation_upper hactual_lower

/--
Finite second-price best-response bridge with direction-aware deviation bounds,
where downward deviations are checked against the applicant's actual chosen
effort rather than against the boundary effort for her band.  This is the
source-shaped version needed when within-band applicants can pay less than the
boundary type.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_boundary_costs_directional_actual_down
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward boundaryCost : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ boundaryCost (actualBand x))
    (hsameCost :
      ∀ x d, deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d)
    (hupCost :
      ∀ x d, actualBand x < deviationBand x d →
        boundaryCost (deviationBand x d) ≤ costFn d)
    (hdownNoProfitActual :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x))
    (hboundaryUtility :
      ∀ i j : Fin (n + 1),
        reward i - boundaryCost i = reward j - boundaryCost j) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort := by
  intro x d
  let i := actualBand x
  let j := deviationBand x d
  have hactual_reward :
      levelReward (rankLevel (rankOfEffort x (effort x))) = reward i := by
    rw [hactualLevel x]
    exact hlevelReward i
  have hdev_reward :
      levelReward (rankLevel (rankOfEffort x d)) = reward j := by
    rw [hdeviationLevel x d]
    exact hlevelReward j
  have hactual_lower :
      reward i - boundaryCost i ≤
        levelReward (rankLevel (rankOfEffort x (effort x))) -
          costFn (effort x) := by
    rw [hactual_reward]
    linarith [hactualCost_le x]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hdeviation_upper :
        levelReward (rankLevel (rankOfEffort x d)) - costFn d
          ≤ reward j - boundaryCost j := by
      rw [hdev_reward]
      linarith [hupCost x d hij]
    exact le_trans hdeviation_upper
      (le_trans (le_of_eq (hboundaryUtility j i)) hactual_lower)
  · have hsame : j = i := hij.symm
    rw [hdev_reward, hactual_reward]
    have hreward_eq : reward j = reward i := by rw [hsame]
    linarith [hsameCost x d hsame]
  · rw [hdev_reward, hactual_reward]
    exact hdownNoProfitActual x d hij

/--
Feasible-effort version of the direction-aware finite best-response bridge.
The source effort domain is `[e0, ∞)`, so deviation-specific cost comparisons
only need to be proved for deviations that satisfy `e0 <= d`.
-/
theorem secondPrice_fin_sourceRankBestResponseFeasible_of_boundary_costs_directional_actual_down
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ} {e0 : ℝ}
    (reward boundaryCost : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ boundaryCost (actualBand x))
    (hsameCost :
      ∀ x d, e0 ≤ d → deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d)
    (hupCost :
      ∀ x d, e0 ≤ d → actualBand x < deviationBand x d →
        boundaryCost (deviationBand x d) ≤ costFn d)
    (hdownNoProfitActual :
      ∀ x d, e0 ≤ d → deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x))
    (hboundaryUtility :
      ∀ i j : Fin (n + 1),
        reward i - boundaryCost i = reward j - boundaryCost j) :
    SourceRankBestResponseFeasible e0 costFn rankOfEffort rankLevel
      levelReward effort := by
  refine ⟨heffort_feasible, ?_⟩
  intro x d hd
  let i := actualBand x
  let j := deviationBand x d
  have hactual_reward :
      levelReward (rankLevel (rankOfEffort x (effort x))) = reward i := by
    rw [hactualLevel x]
    exact hlevelReward i
  have hdev_reward :
      levelReward (rankLevel (rankOfEffort x d)) = reward j := by
    rw [hdeviationLevel x d]
    exact hlevelReward j
  have hactual_lower :
      reward i - boundaryCost i ≤
        levelReward (rankLevel (rankOfEffort x (effort x))) -
          costFn (effort x) := by
    rw [hactual_reward]
    linarith [hactualCost_le x]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hdeviation_upper :
        levelReward (rankLevel (rankOfEffort x d)) - costFn d
          ≤ reward j - boundaryCost j := by
      rw [hdev_reward]
      linarith [hupCost x d hd hij]
    exact le_trans hdeviation_upper
      (le_trans (le_of_eq (hboundaryUtility j i)) hactual_lower)
  · have hsame : j = i := hij.symm
    rw [hdev_reward, hactual_reward]
    have hreward_eq : reward j = reward i := by rw [hsame]
    linarith [hsameCost x d hd hsame]
  · rw [hdev_reward, hactual_reward]
    exact hdownNoProfitActual x d hd hij

/--
Finite second-price converse reduction.  If an effort profile is a source best
response, the displayed second-price effort formula reaches the same finite
reward band, and every underbid below that formula would create a strict
profitable deviation for some lower-band applicant, then the profile must agree
pointwise with the displayed formula.

The last premise is the source converse step from the appendix; it is kept
visible here rather than encoded as a certificate.
-/
theorem secondPrice_fin_effort_eq_source_formula_of_best_response_and_underbid_witness
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hunderbid_profitable :
      ∀ x,
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ y d,
            levelReward (rankLevel (rankOfEffort y (effort y))) -
                costFn (effort y) <
              levelReward (rankLevel (rankOfEffort y d)) - costFn d)
    (hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort) :
    ∀ x,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  intro x
  let sp :=
    secondPriceEffort e0 gInv g f (tilde (actualBand x))
      (cutoff (actualBand x)) (theta x)
  have hsp_feasible : e0 ≤ sp := by
    simpa [sp] using
      secondPriceEffort_ge_e0 e0 gInv g f (tilde (actualBand x))
        (cutoff (actualBand x)) (theta x)
  have hsp_le_effort : sp ≤ effort x := by
    by_contra hnot
    have hgt : sp > effort x := lt_of_not_ge hnot
    rcases hunderbid_profitable x (by simpa [sp] using hgt) with
      ⟨y, d, hprofit⟩
    have hno_profit := hbest y d
    linarith
  have heffort_cost_le_sp : costFn (effort x) ≤ costFn sp := by
    have hbest_sp := hbest x sp
    have hactual_reward :
        levelReward (rankLevel (rankOfEffort x (effort x))) =
          reward (actualBand x) := by
      rw [hactualLevel x]
      exact hlevelReward (actualBand x)
    have hformula_reward :
        levelReward (rankLevel (rankOfEffort x sp)) =
          reward (actualBand x) := by
      rw [hformulaLevel x]
      exact hlevelReward (actualBand x)
    rw [hactual_reward, hformula_reward] at hbest_sp
    linarith
  have heffort_le_sp : effort x ≤ sp := by
    by_contra hnot
    have hlt : sp < effort x := lt_of_not_ge hnot
    have hcost_lt : costFn sp < costFn (effort x) :=
      hcost_strict hsp_feasible (heffort_feasible x) hlt
    linarith
  exact le_antisymm heffort_le_sp hsp_le_effort

/--
Finite second-price converse reduction with the underbid witness written in
the source's adjacent-boundary form.  For each attempted underbid, the caller
provides the lower-band applicant `y`, a deviation `d` that reaches the
underbid applicant's reward band, the lower applicant's actual boundary cost,
the strictly lower deviation cost, and the displayed adjacent boundary cost
equation.  Lean derives the strict profitable deviation and then invokes the
generic converse reduction above.
-/
theorem secondPrice_fin_effort_eq_source_formula_of_best_response_and_source_underbid_witness
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hsource_underbid :
      ∀ x,
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y d,
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            rankLevel (rankOfEffort y d) = (actualBand x).val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            costFn d < costFn (tilde (actualBand x)) ∧
            costFn (tilde (actualBand x)) =
              costFn (tilde prevBand) +
                (reward (actualBand x) - reward prevBand))
    (hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort) :
    ∀ x,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_of_best_response_and_underbid_witness
      reward tilde cutoff actualBand hcost_strict heffort_feasible
      hactualLevel hformulaLevel hlevelReward ?_ hbest
  intro x hunder
  rcases hsource_underbid x hunder with
    ⟨prevBand, y, d, hyLevel, hdLevel, hyCost, hdCost_lt, hboundaryCost⟩
  refine ⟨y, d, ?_⟩
  have hyReward :
      levelReward (rankLevel (rankOfEffort y (effort y))) =
        reward prevBand := by
    rw [hyLevel]
    exact hlevelReward prevBand
  have hdReward :
      levelReward (rankLevel (rankOfEffort y d)) =
        reward (actualBand x) := by
    rw [hdLevel]
    exact hlevelReward (actualBand x)
  rw [hyReward, hdReward, hyCost]
  exact
    secondPrice_profitable_deviation_of_cost_gap_lt_reward_gap
      (stayReward := reward prevBand)
      (devReward := reward (actualBand x))
      (stayCost := costFn (tilde prevBand))
      (devCost := costFn d)
      (by linarith)

/--
Finite second-price converse reduction with the underbid witness in interval
form.  This matches the source proof more closely: after an underbid, a
lower-band applicant has a nonempty open interval of deviations below the
boundary effort that still reach the underbid applicant's reward band.  Lean
chooses a deviation in that interval, derives the strict cost inequality from
strict monotonicity of cost, and then applies the source-witness converse.
-/
theorem secondPrice_fin_effort_eq_source_formula_of_best_response_and_lower_interval_witness
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hlower_interval :
      ∀ x,
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α, ∃ lower : ℝ,
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            e0 ≤ lower ∧
            e0 ≤ tilde (actualBand x) ∧
            lower < tilde (actualBand x) ∧
            (∀ d,
              lower < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val) ∧
            costFn (tilde (actualBand x)) =
              costFn (tilde prevBand) +
                (reward (actualBand x) - reward prevBand))
    (hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort) :
    ∀ x,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_of_best_response_and_source_underbid_witness
      reward tilde cutoff actualBand hcost_strict heffort_feasible
      hactualLevel hformulaLevel hlevelReward ?_ hbest
  intro x hunder
  rcases hlower_interval x hunder with
    ⟨prevBand, y, lower, hyLevel, hyCost, hlower_feasible, htilde_feasible,
      hlower_lt_tilde, hreach, hboundaryCost⟩
  rcases exists_between hlower_lt_tilde with ⟨d, hlower_d, hd_tilde⟩
  refine ⟨prevBand, y, d, hyLevel, hreach d hlower_d hd_tilde, hyCost, ?_,
    hboundaryCost⟩
  have hd_feasible : e0 ≤ d := le_trans hlower_feasible (le_of_lt hlower_d)
  exact hcost_strict hd_feasible htilde_feasible hd_tilde

/--
Finite second-price converse reduction with a cutoff lower-band witness.  The
remaining source obligation now says: for every underbid, there is a lower-band
boundary applicant whose skill matches the cutoff skill, and every deviation
between the score-matching lower effort and the boundary effort reaches the
underbid applicant's reward band.  Lean derives that this interval is nonempty
from the displayed second-price formula.
-/
theorem secondPrice_fin_effort_eq_source_formula_of_best_response_and_lower_cutoff_witness
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hlower_cutoff :
      ∀ x,
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            f (theta y) = f (cutoff (actualBand x)) ∧
            e0 ≤ gInv (g (effort x) * f (theta x) / f (theta y)) ∧
            (∀ d,
              gInv (g (effort x) * f (theta x) / f (theta y)) < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val) ∧
            costFn (tilde (actualBand x)) =
              costFn (tilde prevBand) +
                (reward (actualBand x) - reward prevBand))
    (hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort) :
    ∀ x,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_of_best_response_and_lower_interval_witness
      reward tilde cutoff actualBand hcost_strict heffort_feasible
    hactualLevel hformulaLevel hlevelReward ?_ hbest
  intro x hunder
  rcases hlower_cutoff x hunder with
    ⟨prevBand, y, hyLevel, hyCost, hcutoff_skill, hlower_feasible, hreach,
      hboundaryCost⟩
  let lower := gInv (g (effort x) * f (theta x) / f (theta y))
  have hlower_lt_tilde : lower < tilde (actualBand x) := by
    simpa [lower] using
      secondPriceEffort_underbid_lower_required_effort_lt_boundary
        (e0 := e0) (tildePrev := tilde (actualBand x))
        (c := cutoff (actualBand x)) (theta := theta x)
        (lowerTheta := theta y) (effort := effort x)
        (gInv := gInv) (g := g) (f := f)
        hg_strict (hf_theta_pos x) (hf_theta_pos y) hcutoff_skill hInv
        (heffort_feasible x) hunder
  have htilde_feasible : e0 ≤ tilde (actualBand x) :=
    le_trans hlower_feasible (le_of_lt hlower_lt_tilde)
  refine
    ⟨prevBand, y, lower, hyLevel, hyCost, hlower_feasible, htilde_feasible,
      hlower_lt_tilde, ?_, hboundaryCost⟩
  intro d hlow hd
  exact hreach d (by simpa [lower] using hlow) hd

/--
Finite second-price converse reduction with the lower-cutoff witness in a more
primitive source form.  The caller supplies the cutoff applicant and interval
reachability; Lean derives feasibility of the score-matching lower effort from
the source skill order `f(c_k) <= f(theta)`.
-/
theorem secondPrice_fin_effort_eq_source_formula_of_best_response_and_ordered_lower_cutoff_witness
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, f (cutoff (actualBand x)) ≤ f (theta x))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hlower_cutoff :
      ∀ x,
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            f (theta y) = f (cutoff (actualBand x)) ∧
            (∀ d,
              gInv (g (effort x) * f (theta x) / f (theta y)) < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val) ∧
            costFn (tilde (actualBand x)) =
              costFn (tilde prevBand) +
                (reward (actualBand x) - reward prevBand))
    (hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort) :
    ∀ x,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_of_best_response_and_lower_cutoff_witness
      reward tilde cutoff actualBand hg_strict hInv hcost_strict
      heffort_feasible hf_theta_pos hactualLevel hformulaLevel hlevelReward
      ?_ hbest
  intro x hunder
  rcases hlower_cutoff x hunder with
    ⟨prevBand, y, hyLevel, hyCost, hcutoff_skill, hreach, hboundaryCost⟩
  refine
    ⟨prevBand, y, hyLevel, hyCost, hcutoff_skill, ?_, hreach,
      hboundaryCost⟩
  exact
    scoreMatchingEffort_ge_e0_of_source_skill_order
      hg_strict hInv (heffort_feasible x) (hg_nonneg (effort x))
      (hf_theta_pos y) (by
        rw [hcutoff_skill]
        exact hcutoff_le_theta x)

/--
Restricted finite converse, ordered-witness source form.  This is the
full-measure-set version of
`secondPrice_fin_effort_eq_source_formula_of_best_response_and_ordered_lower_cutoff_witness`:
the lower score-matching feasibility condition is derived from source skill
order on the good set.
-/
theorem secondPrice_fin_effort_eq_source_formula_on_good_of_ordered_lower_cutoff_witness
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → f (cutoff (actualBand x)) ≤ f (theta x))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hlower_cutoff :
      ∀ x,
        Good x →
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            Good y ∧
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            f (theta y) = f (cutoff (actualBand x)) ∧
            (∀ d,
              gInv (g (effort x) * f (theta x) / f (theta y)) < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val) ∧
            costFn (tilde (actualBand x)) =
              costFn (tilde prevBand) +
                (reward (actualBand x) - reward prevBand))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x)) :
    ∀ x, Good x →
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  intro x hxGood
  let sp :=
    secondPriceEffort e0 gInv g f (tilde (actualBand x))
      (cutoff (actualBand x)) (theta x)
  have hsp_feasible : e0 ≤ sp := by
    simpa [sp] using
      secondPriceEffort_ge_e0 e0 gInv g f (tilde (actualBand x))
        (cutoff (actualBand x)) (theta x)
  have hsp_le_effort : sp ≤ effort x := by
    by_contra hnot
    have hgt : sp > effort x := lt_of_not_ge hnot
    rcases hlower_cutoff x hxGood (by simpa [sp] using hgt) with
      ⟨prevBand, y, hyGood, hyLevel, hyCost, hcutoff_skill, hreach,
        hboundaryCost⟩
    let lower := gInv (g (effort x) * f (theta x) / f (theta y))
    have hlower_feasible : e0 ≤ lower := by
      simpa [lower] using
        scoreMatchingEffort_ge_e0_of_source_skill_order
          hg_strict hInv (heffort_feasible x) (hg_nonneg (effort x))
          (hf_theta_pos y) (by
            rw [hcutoff_skill]
            exact hcutoff_le_theta x hxGood)
    have hlower_lt_tilde : lower < tilde (actualBand x) := by
      simpa [lower] using
        secondPriceEffort_underbid_lower_required_effort_lt_boundary
          (e0 := e0) (tildePrev := tilde (actualBand x))
          (c := cutoff (actualBand x)) (theta := theta x)
          (lowerTheta := theta y) (effort := effort x)
          (gInv := gInv) (g := g) (f := f)
          hg_strict (hf_theta_pos x) (hf_theta_pos y) hcutoff_skill hInv
          (heffort_feasible x) (by simpa [sp] using hgt)
    have htilde_feasible : e0 ≤ tilde (actualBand x) :=
      le_trans hlower_feasible (le_of_lt hlower_lt_tilde)
    rcases exists_between hlower_lt_tilde with ⟨d, hlower_d, hd_tilde⟩
    have hdLevel :
        rankLevel (rankOfEffort y d) = (actualBand x).val :=
      hreach d (by simpa [lower] using hlower_d) hd_tilde
    have hdCost_lt : costFn d < costFn (tilde (actualBand x)) := by
      have hd_feasible : e0 ≤ d :=
        le_trans hlower_feasible (le_of_lt hlower_d)
      exact hcost_strict hd_feasible htilde_feasible hd_tilde
    have hyReward :
        levelReward (rankLevel (rankOfEffort y (effort y))) =
          reward prevBand := by
      rw [hyLevel]
      exact hlevelReward prevBand
    have hdReward :
        levelReward (rankLevel (rankOfEffort y d)) =
          reward (actualBand x) := by
      rw [hdLevel]
      exact hlevelReward (actualBand x)
    have hprofit :
        levelReward (rankLevel (rankOfEffort y (effort y))) -
            costFn (effort y) <
          levelReward (rankLevel (rankOfEffort y d)) - costFn d := by
      rw [hyReward, hdReward, hyCost]
      exact
        secondPrice_profitable_deviation_of_cost_gap_lt_reward_gap
          (stayReward := reward prevBand)
          (devReward := reward (actualBand x))
          (stayCost := costFn (tilde prevBand))
          (devCost := costFn d)
          (by linarith)
    have hno_profit := hbest_good y hyGood d
    exact not_lt_of_ge hno_profit hprofit
  have heffort_cost_le_sp : costFn (effort x) ≤ costFn sp := by
    have hbest_sp := hbest_good x hxGood sp
    have hactual_reward :
        levelReward (rankLevel (rankOfEffort x (effort x))) =
          reward (actualBand x) := by
      rw [hactualLevel x]
      exact hlevelReward (actualBand x)
    have hformula_reward :
        levelReward (rankLevel (rankOfEffort x sp)) =
          reward (actualBand x) := by
      rw [hformulaLevel x]
      exact hlevelReward (actualBand x)
    rw [hactual_reward, hformula_reward] at hbest_sp
    linarith
  have heffort_le_sp : effort x ≤ sp := by
    by_contra hnot
    have hlt : sp < effort x := lt_of_not_ge hnot
    have hcost_lt : costFn sp < costFn (effort x) :=
      hcost_strict hsp_feasible (heffort_feasible x) hlt
    linarith
  exact le_antisymm heffort_le_sp hsp_le_effort

/--
Almost-everywhere finite converse with ordered lower-cutoff witnesses.  The
remaining witness obligation is source-facing: locate the lower cutoff
applicant on the full-measure good set and prove interval reachability.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_good_ordered_lower_cutoff_witness
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → f (cutoff (actualBand x)) ≤ f (theta x))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hlower_cutoff :
      ∀ x,
        Good x →
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            Good y ∧
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            f (theta y) = f (cutoff (actualBand x)) ∧
            (∀ d,
              gInv (g (effort x) * f (theta x) / f (theta y)) < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val) ∧
            costFn (tilde (actualBand x)) =
              costFn (tilde prevBand) +
                (reward (actualBand x) - reward prevBand))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  filter_upwards [hgood_ae] with x hxGood
  exact
    secondPrice_fin_effort_eq_source_formula_on_good_of_ordered_lower_cutoff_witness
      Good reward tilde cutoff actualBand hg_strict hInv hcost_strict
      heffort_feasible hg_nonneg hf_theta_pos hcutoff_le_theta hactualLevel
      hformulaLevel hlevelReward hlower_cutoff hbest_good x hxGood

/--
Almost-everywhere finite converse with ordered lower-cutoff witnesses and
boundary equations.  The adjacent cost equality in the underbid witness is
derived from the displayed finite boundary-effort equations, leaving only the
lower cutoff applicant and interval reachability as the source witness.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_good_ordered_lower_cutoff_witness_boundary_equations
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → f (cutoff (actualBand x)) ≤ f (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hlower_cutoff :
      ∀ x,
        Good x →
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            Good y ∧
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            f (theta y) = f (cutoff (actualBand x)) ∧
            (∀ d,
              gInv (g (effort x) * f (theta x) / f (theta y)) < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_ae_of_good_ordered_lower_cutoff_witness
      Good reward tilde cutoff actualBand hg_strict hInv hcost_strict
      heffort_feasible hg_nonneg hf_theta_pos hcutoff_le_theta hactualLevel
      hformulaLevel hlevelReward ?_ hbest_good hgood_ae
  intro x hxGood hunder
  rcases hlower_cutoff x hxGood hunder with
    ⟨prevBand, y, hyGood, hyLevel, hyCost, hcutoff_skill, hreach⟩
  refine
    ⟨prevBand, y, hyGood, hyLevel, hyCost, hcutoff_skill, hreach, ?_⟩
  have hactual := htilde (actualBand x)
  have hprev := htilde prevBand
  linarith

/--
Almost-everywhere finite converse with lower cutoff applicants.  If good-set
applicants use their boundary efforts, then the lower applicant's reward band
and boundary cost are derived from its band membership.  The remaining source
witness is a lower-band applicant at the cutoff skill and interval
reachability.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_good_lower_cutoff_applicant_boundary_equations
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → f (cutoff (actualBand x)) ≤ f (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hlower_cutoff :
      ∀ x,
        Good x →
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            Good y ∧
            actualBand y = prevBand ∧
            f (theta y) = f (cutoff (actualBand x)) ∧
            (∀ d,
              gInv (g (effort x) * f (theta x) / f (theta y)) < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_ae_of_good_ordered_lower_cutoff_witness_boundary_equations
      Good reward tilde cutoff actualBand hg_strict hInv hcost_strict
      heffort_feasible hg_nonneg hf_theta_pos hcutoff_le_theta htilde
      hactualLevel hformulaLevel hlevelReward ?_ hbest_good hgood_ae
  intro x hxGood hunder
  rcases hlower_cutoff x hxGood hunder with
    ⟨prevBand, y, hyGood, hband, hcutoff_skill, hreach⟩
  refine ⟨prevBand, y, hyGood, ?_, ?_, hcutoff_skill, hreach⟩
  · have hyLevel := hactualLevel y
    simpa [hband] using hyLevel
  · rw [heffort_boundary y hyGood, hband]

/--
Almost-everywhere finite converse with score-derived interval reachability.
The source witness only gives the lower cutoff applicant.  Lean derives that
any effort in the open score-matching interval reaches exactly the underbid
applicant's band from two visible band-threshold facts: strictly overtaking
the underbid score reaches at least that band, while staying below the boundary
effort reaches no higher than that band.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_good_lower_cutoff_applicant_score_reach_boundary_equations
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → f (cutoff (actualBand x)) ≤ f (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hscore_overtake_reaches :
      ∀ x y d, Good x → Good y →
        g (effort x) * f (theta x) < g d * f (theta y) →
          actualBand x ≤ deviationBand y d)
    (hbelow_boundary_no_higher :
      ∀ x y d, Good x → Good y → d < tilde (actualBand x) →
        deviationBand y d ≤ actualBand x)
    (hlower_cutoff :
      ∀ x,
        Good x →
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            Good y ∧
            actualBand y = prevBand ∧
            f (theta y) = f (cutoff (actualBand x)))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_ae_of_good_lower_cutoff_applicant_boundary_equations
      Good reward tilde cutoff actualBand hg_strict hInv hcost_strict
      heffort_feasible hg_nonneg hf_theta_pos hcutoff_le_theta htilde
      hactualLevel hformulaLevel hlevelReward heffort_boundary ?_
      hbest_good hgood_ae
  intro x hxGood hunder
  rcases hlower_cutoff x hxGood hunder with
    ⟨prevBand, y, hyGood, hband, hcutoff_skill⟩
  refine ⟨prevBand, y, hyGood, hband, hcutoff_skill, ?_⟩
  intro d hlower_lt hd_boundary
  have hscore_lt :
      g (effort x) * f (theta x) < g d * f (theta y) :=
    scoreMatchingEffort_score_lt_of_lt
      hg_strict hInv (hf_theta_pos y) hlower_lt
  have hge : actualBand x ≤ deviationBand y d :=
    hscore_overtake_reaches x y d hxGood hyGood hscore_lt
  have hle : deviationBand y d ≤ actualBand x :=
    hbelow_boundary_no_higher x y d hxGood hyGood hd_boundary
  have hband_eq : deviationBand y d = actualBand x :=
    le_antisymm hle hge
  simpa [hband_eq] using hdeviationLevel y d

/--
Almost-everywhere finite converse from global lower-cutoff support.  If the
source model supplies a lower-band cutoff applicant for every finite boundary,
the underbid-specific existential witness follows by instantiating that
support at the underbid applicant's band.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_global_lower_cutoff_support_score_reach_boundary_equations
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → f (cutoff (actualBand x)) ≤ f (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hscore_overtake_reaches :
      ∀ x y d, Good x → Good y →
        g (effort x) * f (theta x) < g d * f (theta y) →
          actualBand x ≤ deviationBand y d)
    (hbelow_boundary_no_higher :
      ∀ x y d, Good x → Good y → d < tilde (actualBand x) →
        deviationBand y d ≤ actualBand x)
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        f (theta y) = f (cutoff i))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_ae_of_good_lower_cutoff_applicant_score_reach_boundary_equations
      Good reward tilde cutoff actualBand deviationBand hg_strict hInv
      hcost_strict heffort_feasible hg_nonneg hf_theta_pos hcutoff_le_theta
      htilde hactualLevel hdeviationLevel hformulaLevel hlevelReward
      heffort_boundary hscore_overtake_reaches hbelow_boundary_no_higher
      ?_ hbest_good hgood_ae
  intro x _hxGood _hunder
  exact hlower_cutoff_support (actualBand x)

/--
Same global-support finite converse, with the source cutoff/type order exposed
instead of the derived `f(cutoff) <= f(theta)` inequality.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_global_lower_cutoff_support_score_reach_boundary_equations_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hscore_overtake_reaches :
      ∀ x y d, Good x → Good y →
        g (effort x) * f (theta x) < g d * f (theta y) →
          actualBand x ≤ deviationBand y d)
    (hbelow_boundary_no_higher :
      ∀ x y d, Good x → Good y → d < tilde (actualBand x) →
        deviationBand y d ≤ actualBand x)
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        f (theta y) = f (cutoff i))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_ae_of_global_lower_cutoff_support_score_reach_boundary_equations
      Good reward tilde cutoff actualBand deviationBand hg_strict hInv
      hcost_strict heffort_feasible hg_nonneg hf_theta_pos ?_ htilde
      hactualLevel hdeviationLevel hformulaLevel hlevelReward
      heffort_boundary hscore_overtake_reaches hbelow_boundary_no_higher
      hlower_cutoff_support hbest_good hgood_ae
  intro x hxGood
  exact hf_mono (hcutoff_le_theta x hxGood)

/--
Finite converse with source threshold semantics.  This variant replaces the
two direct score/boundary reach hypotheses by the usual finite-band threshold
facts: boundary efforts are monotone, a deviation assigned to a band pays at
least that band's boundary effort, and any deviation whose assigned band remains
below a target band has score no larger than an applicant in the target band.
The lower-cutoff support is stated as an actual cutoff type rather than only as
an equality after applying `f`.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_thresholds_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_lower_score_bound :
      ∀ x y d, Good x → Good y →
        deviationBand y d < actualBand x →
          g d * f (theta y) ≤ g (effort x) * f (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_ae_of_global_lower_cutoff_support_score_reach_boundary_equations_of_cutoff_order
      Good reward tilde cutoff actualBand deviationBand hg_strict hInv
      hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
      hcutoff_le_theta htilde hactualLevel hdeviationLevel hformulaLevel
      hlevelReward heffort_boundary ?_ ?_ ?_ hbest_good hgood_ae
  · intro x y d hxGood hyGood hscore_lt
    by_contra hnot
    have hlt : deviationBand y d < actualBand x := lt_of_not_ge hnot
    have hle :
        g d * f (theta y) ≤ g (effort x) * f (theta x) :=
      hdeviation_lower_score_bound x y d hxGood hyGood hlt
    exact not_lt_of_ge hle hscore_lt
  · intro x y d _hxGood _hyGood hd
    by_contra hnot
    have hlt : actualBand x < deviationBand y d := lt_of_not_ge hnot
    have htilde_le : tilde (actualBand x) ≤ tilde (deviationBand y d) :=
      htilde_mono (le_of_lt hlt)
    exact not_lt_of_ge (le_trans htilde_le (hdeviation_boundary y d)) hd
  · intro i
    rcases hlower_cutoff_support i with
      ⟨prevBand, y, hyGood, hband, htheta⟩
    exact ⟨prevBand, y, hyGood, hband, by rw [htheta]⟩

/--
Finite converse with band-target threshold semantics.  This strengthens
`secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_thresholds_of_cutoff_order`
by deriving the lower-score premise from a per-band threshold statement: any
deviation assigned below band `i` has score at most band `i`'s boundary target.
Cutoff/type order then puts the target applicant's boundary target below their
realized score.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_band_targets_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_below_target :
      ∀ y d i, Good y →
        deviationBand y d < i →
          g d * f (theta y) ≤ g (tilde i) * f (cutoff i))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_thresholds_of_cutoff_order
      Good reward tilde cutoff actualBand deviationBand hg_strict hInv
      hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
      hcutoff_le_theta htilde_mono hdeviation_boundary ?_
      htilde hactualLevel hdeviationLevel hformulaLevel hlevelReward
      heffort_boundary hlower_cutoff_support hbest_good hgood_ae
  intro x y d hxGood hyGood hlt
  have hdev_target :
      g d * f (theta y) ≤
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) :=
    hdeviation_below_target y d (actualBand x) hyGood hlt
  have htarget_actual :
      g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x) :=
    mul_le_mul_of_nonneg_left
      (hf_mono (hcutoff_le_theta x hxGood))
      (hg_nonneg (tilde (actualBand x)))
  have hscore :=
    le_trans hdev_target htarget_actual
  simpa [heffort_boundary x hxGood] using hscore

/--
Finite converse with per-band deviation score upper bounds.  This is a
model-construction-friendly wrapper around the band-target threshold theorem:
if every deviation score is bounded by an upper bound for its assigned band,
and lower-band upper bounds lie below later boundary targets, then deviations
assigned below a target band have score below that target.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_deviation_upper_bounds_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff bandUpper : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_score_le_upper :
      ∀ y d, Good y →
        g d * f (theta y) ≤ bandUpper (deviationBand y d))
    (hupper_le_target :
      ∀ {i j : Fin (n + 1)}, i < j →
        bandUpper i ≤ g (tilde j) * f (cutoff j))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_band_targets_of_cutoff_order
      Good reward tilde cutoff actualBand deviationBand hg_strict hInv
      hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
      hcutoff_le_theta htilde_mono hdeviation_boundary ?_ htilde
      hactualLevel hdeviationLevel hformulaLevel hlevelReward
      heffort_boundary hlower_cutoff_support hbest_good hgood_ae
  intro y d i hyGood hlt
  exact le_trans (hdeviation_score_le_upper y d hyGood)
    (hupper_le_target hlt)

/--
Finite converse with monotone band targets.  If every per-band deviation upper
bound lies below its own boundary target and boundary targets are monotone
across bands, Lean derives the all-pairs lower-upper-bound condition needed by
the finite converse.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_deviation_upper_bounds_and_monotone_targets_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff bandUpper : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_score_le_upper :
      ∀ y d, Good y →
        g d * f (theta y) ≤ bandUpper (deviationBand y d))
    (hupper_le_own_target :
      ∀ i : Fin (n + 1), bandUpper i ≤ g (tilde i) * f (cutoff i))
    (hbandTarget_mono :
      Monotone (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i)))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_deviation_upper_bounds_of_cutoff_order
      Good reward tilde cutoff bandUpper actualBand deviationBand hg_strict
      hInv hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
      hcutoff_le_theta htilde_mono hdeviation_boundary
      hdeviation_score_le_upper ?_ htilde hactualLevel hdeviationLevel
      hformulaLevel hlevelReward heffort_boundary hlower_cutoff_support
      hbest_good hgood_ae
  intro i j hij
  exact le_trans (hupper_le_own_target i) (hbandTarget_mono (le_of_lt hij))

/--
Finite converse with source monotonicity for boundary targets.  This replaces
the boundary-target monotonicity premise by monotonicity of `tilde`, monotonicity
of `cutoff`, monotonicity of `g`/`f`, and nonnegativity.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_deviation_upper_bounds_and_source_mono_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff bandUpper : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_nonneg : ∀ i : Fin (n + 1), 0 ≤ f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_score_le_upper :
      ∀ y d, Good y →
        g d * f (theta y) ≤ bandUpper (deviationBand y d))
    (hupper_le_own_target :
      ∀ i : Fin (n + 1), bandUpper i ≤ g (tilde i) * f (cutoff i))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hlower_cutoff_support :
      ∀ i : Fin (n + 1), ∃ prevBand : Fin (n + 1), ∃ y : α,
        Good y ∧
        actualBand y = prevBand ∧
        theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  exact
    secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_deviation_upper_bounds_and_monotone_targets_of_cutoff_order
      Good reward tilde cutoff bandUpper actualBand deviationBand hg_strict hInv
      hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
      hcutoff_le_theta htilde_mono hdeviation_boundary
      hdeviation_score_le_upper hupper_le_own_target
      (secondPrice_bandTarget_mono_of_mono hg_strict.monotone hg_nonneg
        hf_mono hf_cutoff_nonneg htilde_mono hcutoff_mono)
      htilde hactualLevel hdeviationLevel hformulaLevel hlevelReward
      heffort_boundary hlower_cutoff_support hbest_good hgood_ae

/--
Finite converse with source monotonicity and primitive cutoff-type support.
The source construction uses applicants located at the band cutoffs; the actual
band of such an applicant can be recovered internally, so callers should not
have to provide a separate `prevBand` witness.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_cutoff_type_support_deviation_upper_bounds_and_source_mono_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff bandUpper : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_nonneg : ∀ i : Fin (n + 1), 0 ≤ f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_score_le_upper :
      ∀ y d, Good y →
        g d * f (theta y) ≤ bandUpper (deviationBand y d))
    (hupper_le_own_target :
      ∀ i : Fin (n + 1), bandUpper i ≤ g (tilde i) * f (cutoff i))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hcutoff_type_support :
      ∀ i : Fin (n + 1), ∃ y : α, Good y ∧ theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_ae_of_global_cutoff_support_deviation_upper_bounds_and_source_mono_of_cutoff_order
      Good reward tilde cutoff bandUpper actualBand deviationBand hg_strict hInv
      hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
      hf_cutoff_nonneg hcutoff_mono hcutoff_le_theta htilde_mono
      hdeviation_boundary hdeviation_score_le_upper hupper_le_own_target htilde
      hactualLevel hdeviationLevel hformulaLevel hlevelReward heffort_boundary
      ?_ hbest_good hgood_ae
  intro i
  rcases hcutoff_type_support i with ⟨y, hyGood, htheta⟩
  exact ⟨actualBand y, y, hyGood, rfl, htheta⟩

/--
Finite converse with source monotonicity, primitive cutoff-type support, and
the direct source threshold statement for deviation scores.  This removes the
implementation-only `bandUpper` function from the caller-facing assumptions.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_cutoff_type_support_source_thresholds_and_source_mono_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_nonneg : ∀ i : Fin (n + 1), 0 ≤ f (cutoff i))
    (hcutoff_mono : Monotone cutoff)
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (htilde_mono : Monotone tilde)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_score_le_own_target :
      ∀ y d, Good y →
        g d * f (theta y) ≤
          g (tilde (deviationBand y d)) * f (cutoff (deviationBand y d)))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hcutoff_type_support :
      ∀ i : Fin (n + 1), ∃ y : α, Good y ∧ theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  refine
    secondPrice_fin_effort_eq_source_formula_ae_of_cutoff_type_support_deviation_upper_bounds_and_source_mono_of_cutoff_order
      Good reward tilde cutoff
      (fun i : Fin (n + 1) => g (tilde i) * f (cutoff i))
      actualBand deviationBand hg_strict hInv hcost_strict heffort_feasible
      hg_nonneg hf_mono hf_theta_pos hf_cutoff_nonneg hcutoff_mono
      hcutoff_le_theta htilde_mono hdeviation_boundary ?_ ?_ htilde
      hactualLevel hdeviationLevel hformulaLevel hlevelReward heffort_boundary
      hcutoff_type_support hbest_good hgood_ae
  · intro y d hyGood
    exact hdeviation_score_le_own_target y d hyGood
  · intro i
    exact le_rfl

/--
Finite converse with source threshold semantics, primitive cutoff support, and
boundary-effort monotonicity derived from the displayed cost equations and
monotone rewards.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_cutoff_type_support_source_thresholds_and_reward_mono_of_cutoff_order
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 baseCost : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hcutoff_mono : Monotone cutoff)
    (hcutoff_le_theta :
      ∀ x, Good x → cutoff (actualBand x) ≤ theta x)
    (hreward_mono : Monotone reward)
    (hdeviation_boundary :
      ∀ y d, tilde (deviationBand y d) ≤ d)
    (hdeviation_score_le_own_target :
      ∀ y d, Good y →
        g d * f (theta y) ≤
          g (tilde (deviationBand y d)) * f (cutoff (deviationBand y d)))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (heffort_boundary :
      ∀ x, Good x → effort x = tilde (actualBand x))
    (hcutoff_type_support :
      ∀ i : Fin (n + 1), ∃ y : α, Good y ∧ theta y = cutoff i)
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  have hgap_mono :
      Monotone (fun i : Fin (n + 1) =>
        reward i - reward ⟨0, Nat.succ_pos n⟩) := by
    intro i j hij
    exact sub_le_sub_right (hreward_mono hij) _
  have hf_cutoff_nonneg : ∀ i : Fin (n + 1), 0 ≤ f (cutoff i) := by
    intro i
    rcases hcutoff_type_support i with ⟨y, _hyGood, htheta⟩
    exact le_of_lt (by simpa [htheta] using hf_theta_pos y)
  have htilde_mono : Monotone tilde :=
    fun i j hij =>
      secondPrice_boundaryEffort_mono_of_rewardGap_mono
        hcost_strict (htilde_feasible i) (htilde_feasible j)
        (htilde i) (htilde j) (hgap_mono hij)
  exact
    secondPrice_fin_effort_eq_source_formula_ae_of_cutoff_type_support_source_thresholds_and_source_mono_of_cutoff_order
      Good reward tilde cutoff actualBand deviationBand hg_strict hInv
      hcost_strict heffort_feasible hg_nonneg hf_mono hf_theta_pos
      hf_cutoff_nonneg hcutoff_mono hcutoff_le_theta htilde_mono
      hdeviation_boundary hdeviation_score_le_own_target htilde
      hactualLevel hdeviationLevel hformulaLevel hlevelReward heffort_boundary
      hcutoff_type_support hbest_good hgood_ae

/--
Restricted finite converse for the source "up to measure zero" reading.  On a
good set of applicants, best-response inequalities and lower-cutoff witnesses
force equality with the displayed second-price formula, provided the lower-band
witness produced by any underbid is also in the good set.
-/
theorem secondPrice_fin_effort_eq_source_formula_on_good_of_lower_cutoff_witness
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hlower_cutoff :
      ∀ x,
        Good x →
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            Good y ∧
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            f (theta y) = f (cutoff (actualBand x)) ∧
            e0 ≤ gInv (g (effort x) * f (theta x) / f (theta y)) ∧
            (∀ d,
              gInv (g (effort x) * f (theta x) / f (theta y)) < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val) ∧
            costFn (tilde (actualBand x)) =
              costFn (tilde prevBand) +
                (reward (actualBand x) - reward prevBand))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x)) :
    ∀ x, Good x →
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  intro x hxGood
  let sp :=
    secondPriceEffort e0 gInv g f (tilde (actualBand x))
      (cutoff (actualBand x)) (theta x)
  have hsp_feasible : e0 ≤ sp := by
    simpa [sp] using
      secondPriceEffort_ge_e0 e0 gInv g f (tilde (actualBand x))
        (cutoff (actualBand x)) (theta x)
  have hsp_le_effort : sp ≤ effort x := by
    by_contra hnot
    have hgt : sp > effort x := lt_of_not_ge hnot
    rcases hlower_cutoff x hxGood (by simpa [sp] using hgt) with
      ⟨prevBand, y, hyGood, hyLevel, hyCost, hcutoff_skill, hlower_feasible,
        hreach, hboundaryCost⟩
    let lower := gInv (g (effort x) * f (theta x) / f (theta y))
    have hlower_lt_tilde : lower < tilde (actualBand x) := by
      simpa [lower] using
        secondPriceEffort_underbid_lower_required_effort_lt_boundary
          (e0 := e0) (tildePrev := tilde (actualBand x))
          (c := cutoff (actualBand x)) (theta := theta x)
          (lowerTheta := theta y) (effort := effort x)
          (gInv := gInv) (g := g) (f := f)
          hg_strict (hf_theta_pos x) (hf_theta_pos y) hcutoff_skill hInv
          (heffort_feasible x) (by simpa [sp] using hgt)
    have htilde_feasible : e0 ≤ tilde (actualBand x) :=
      le_trans hlower_feasible (le_of_lt hlower_lt_tilde)
    rcases exists_between hlower_lt_tilde with ⟨d, hlower_d, hd_tilde⟩
    have hdLevel :
        rankLevel (rankOfEffort y d) = (actualBand x).val :=
      hreach d (by simpa [lower] using hlower_d) hd_tilde
    have hdCost_lt : costFn d < costFn (tilde (actualBand x)) := by
      have hd_feasible : e0 ≤ d :=
        le_trans hlower_feasible (le_of_lt hlower_d)
      exact hcost_strict hd_feasible htilde_feasible hd_tilde
    have hyReward :
        levelReward (rankLevel (rankOfEffort y (effort y))) =
          reward prevBand := by
      rw [hyLevel]
      exact hlevelReward prevBand
    have hdReward :
        levelReward (rankLevel (rankOfEffort y d)) =
          reward (actualBand x) := by
      rw [hdLevel]
      exact hlevelReward (actualBand x)
    have hprofit :
        levelReward (rankLevel (rankOfEffort y (effort y))) -
            costFn (effort y) <
          levelReward (rankLevel (rankOfEffort y d)) - costFn d := by
      rw [hyReward, hdReward, hyCost]
      exact
        secondPrice_profitable_deviation_of_cost_gap_lt_reward_gap
          (stayReward := reward prevBand)
          (devReward := reward (actualBand x))
          (stayCost := costFn (tilde prevBand))
          (devCost := costFn d)
          (by linarith)
    have hno_profit := hbest_good y hyGood d
    exact not_lt_of_ge hno_profit hprofit
  have heffort_cost_le_sp : costFn (effort x) ≤ costFn sp := by
    have hbest_sp := hbest_good x hxGood sp
    have hactual_reward :
        levelReward (rankLevel (rankOfEffort x (effort x))) =
          reward (actualBand x) := by
      rw [hactualLevel x]
      exact hlevelReward (actualBand x)
    have hformula_reward :
        levelReward (rankLevel (rankOfEffort x sp)) =
          reward (actualBand x) := by
      rw [hformulaLevel x]
      exact hlevelReward (actualBand x)
    rw [hactual_reward, hformula_reward] at hbest_sp
    linarith
  have heffort_le_sp : effort x ≤ sp := by
    by_contra hnot
    have hlt : sp < effort x := lt_of_not_ge hnot
    have hcost_lt : costFn sp < costFn (effort x) :=
      hcost_strict hsp_feasible (heffort_feasible x) hlt
    linarith
  exact le_antisymm heffort_le_sp hsp_le_effort

/--
Almost-everywhere finite converse.  If the source best-response inequalities
and lower-cutoff witnesses hold on a full-measure good set, then the displayed
second-price effort formula is unique up to measure zero.
-/
theorem secondPrice_fin_effort_eq_source_formula_ae_of_good_lower_cutoff_witness
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (Good : α → Prop)
    (reward : Fin (n + 1) → ℝ)
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hformulaLevel :
      ∀ x,
        rankLevel
            (rankOfEffort x
              (secondPriceEffort e0 gInv g f (tilde (actualBand x))
                (cutoff (actualBand x)) (theta x))) =
          (actualBand x).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hlower_cutoff :
      ∀ x,
        Good x →
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
            (cutoff (actualBand x)) (theta x) > effort x →
          ∃ prevBand : Fin (n + 1), ∃ y : α,
            Good y ∧
            rankLevel (rankOfEffort y (effort y)) = prevBand.val ∧
            costFn (effort y) = costFn (tilde prevBand) ∧
            f (theta y) = f (cutoff (actualBand x)) ∧
            e0 ≤ gInv (g (effort x) * f (theta x) / f (theta y)) ∧
            (∀ d,
              gInv (g (effort x) * f (theta x) / f (theta y)) < d →
              d < tilde (actualBand x) →
                rankLevel (rankOfEffort y d) = (actualBand x).val) ∧
            costFn (tilde (actualBand x)) =
              costFn (tilde prevBand) +
                (reward (actualBand x) - reward prevBand))
    (hbest_good :
      ∀ x, Good x →
        ∀ d,
          levelReward (rankLevel (rankOfEffort x d)) - costFn d ≤
            levelReward (rankLevel (rankOfEffort x (effort x))) -
              costFn (effort x))
    (hgood_ae : ∀ᵐ x ∂μ, Good x) :
    ∀ᵐ x ∂μ,
      effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x) := by
  filter_upwards [hgood_ae] with x hxGood
  exact
    secondPrice_fin_effort_eq_source_formula_on_good_of_lower_cutoff_witness
      Good reward tilde cutoff actualBand hg_strict hInv hcost_strict
      heffort_feasible hf_theta_pos hactualLevel hformulaLevel hlevelReward
      hlower_cutoff hbest_good x hxGood

/--
Finite second-price best-response bridge from the displayed boundary-effort
cost equations.  The equal-boundary-utility condition is derived here from
`cost(tilde i) = baseCost + (reward i - reward 0)`, so callers do not need to
provide it as a separate certificate.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost :
      ∀ x, costFn (effort x) = costFn (tilde (actualBand x)))
    (hdeviationCost :
      ∀ x d, costFn (tilde (deviationBand x d)) ≤ costFn d) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort := by
  refine secondPrice_fin_sourceRankBestResponse_of_boundary_costs
    reward (fun i => costFn (tilde i)) actualBand deviationBand
    hactualLevel hdeviationLevel hlevelReward hactualCost hdeviationCost ?_
  intro i j
  have hi := htilde i
  have hj := htilde j
  change reward i - costFn (tilde i) = reward j - costFn (tilde j)
  rw [hi, hj]
  ring

/--
Finite second-price best-response bridge from boundary effort equations and
source-shaped effort thresholds.  The deviation-cost premise is derived from
monotone cost: any deviation that lands in a band must exert at least that
band's boundary effort.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_boundary_effort_thresholds
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ} {e0 : ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualEffort :
      ∀ x, effort x = tilde (actualBand x))
    (hdeviationEffort :
      ∀ x d, tilde (deviationBand x d) ≤ d) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort := by
  refine secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations
    reward tilde actualBand deviationBand htilde hactualLevel
    hdeviationLevel hlevelReward ?_ ?_
  · intro x
    rw [hactualEffort x]
  · intro x d
    exact hcost_mono
      (htilde_feasible (deviationBand x d))
      (le_trans (htilde_feasible (deviationBand x d)) (hdeviationEffort x d))
      (hdeviationEffort x d)

/--
Finite second-price best-response bridge from boundary effort equations with a
weak actual-cost premise.  This is the source-shaped version: applicants may
use a within-band second-price effort whose cost is below the boundary effort
for their realized band.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations_actual_le
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)))
    (hdeviationCost :
      ∀ x d, costFn (tilde (deviationBand x d)) ≤ costFn d) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort := by
  refine secondPrice_fin_sourceRankBestResponse_of_boundary_costs_actual_le
    reward (fun i => costFn (tilde i)) actualBand deviationBand
    hactualLevel hdeviationLevel hlevelReward hactualCost_le
    hdeviationCost ?_
  intro i j
  have hi := htilde i
  have hj := htilde j
  change reward i - costFn (tilde i) = reward j - costFn (tilde j)
  rw [hi, hj]
  ring

/--
Finite second-price best-response bridge from boundary effort equations with
direction-aware deviation bounds.  Equal boundary utilities are derived from
the source cost equations; callers supply only the economically separate
same-band, upward, and downward no-profit ingredients.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations_directional
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)))
    (hsameCost :
      ∀ x d, deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d)
    (hupCost :
      ∀ x d, actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d)
    (hdownNoProfit :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (tilde (actualBand x))) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort := by
  refine secondPrice_fin_sourceRankBestResponse_of_boundary_costs_directional
    reward (fun i => costFn (tilde i)) actualBand deviationBand
    hactualLevel hdeviationLevel hlevelReward hactualCost_le
    hsameCost hupCost hdownNoProfit ?_
  intro i j
  have hi := htilde i
  have hj := htilde j
  change reward i - costFn (tilde i) = reward j - costFn (tilde j)
  rw [hi, hj]
  ring

/--
Finite second-price best-response bridge from boundary effort equations with
direction-aware deviation bounds and the source-shaped downward comparison
against actual chosen effort.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations_directional_actual_down
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)))
    (hsameCost :
      ∀ x d, deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d)
    (hupCost :
      ∀ x d, actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d)
    (hdownNoProfitActual :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x)) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort := by
  refine secondPrice_fin_sourceRankBestResponse_of_boundary_costs_directional_actual_down
    reward (fun i => costFn (tilde i)) actualBand deviationBand
    hactualLevel hdeviationLevel hlevelReward hactualCost_le
    hsameCost hupCost hdownNoProfitActual ?_
  intro i j
  have hi := htilde i
  have hj := htilde j
  change reward i - costFn (tilde i) = reward j - costFn (tilde j)
  rw [hi, hj]
  ring

/--
Feasible-effort version of the boundary-equation, direction-aware finite
best-response bridge.  Equal boundary utilities are derived from the displayed
boundary cost equations, while all deviation checks are restricted to feasible
efforts.
-/
theorem secondPrice_fin_sourceRankBestResponseFeasible_of_boundary_effort_equations_directional_actual_down
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ} {e0 : ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)))
    (hsameCost :
      ∀ x d, e0 ≤ d → deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d)
    (hupCost :
      ∀ x d, e0 ≤ d → actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d)
    (hdownNoProfitActual :
      ∀ x d, e0 ≤ d → deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x)) :
    SourceRankBestResponseFeasible e0 costFn rankOfEffort rankLevel
      levelReward effort := by
  refine
    secondPrice_fin_sourceRankBestResponseFeasible_of_boundary_costs_directional_actual_down
      reward (fun i => costFn (tilde i)) actualBand deviationBand
      heffort_feasible hactualLevel hdeviationLevel hlevelReward
      hactualCost_le hsameCost hupCost hdownNoProfitActual ?_
  intro i j
  have hi := htilde i
  have hj := htilde j
  change reward i - costFn (tilde i) = reward j - costFn (tilde j)
  rw [hi, hj]
  ring

/--
Finite second-price best-response bridge for the displayed effort formula.
The actual-cost, same-band, and upward-deviation cost comparisons are derived
from source score-boundary reachability and monotone cost.  The remaining
downward no-profit condition is left explicit because lower-band deviations
need not pay the lower band's boundary effort.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_effort_formula_directional
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdownNoProfit :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (tilde (actualBand x))) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort := by
  have hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)) :=
    secondPrice_actualCost_le_boundary_of_effort_formula
      tilde cutoff actualBand theta effort hg_strict hInv hcost_mono
      htilde_feasible hf_theta_pos hactual_reaches_boundary
      heffort_formula
  have hsameCost :
      ∀ x d, deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d :=
    secondPrice_sameBandCost_le_of_effort_formula
      tilde cutoff actualBand deviationBand theta effort hg_strict hInv
      hcost_mono hf_theta_pos hdeviation_same_feasible
      hsame_reaches_boundary heffort_formula
  have hupCost :
      ∀ x d, actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d :=
    secondPrice_upwardCost_ge_boundary_of_score_boundary
      tilde cutoff actualBand deviationBand hg_strict hcost_mono
      htilde_feasible hf_cutoff_pos hdeviation_up_feasible
      hup_reaches_boundary
  exact
    secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations_directional
      reward tilde actualBand deviationBand htilde hactualLevel
      hdeviationLevel hlevelReward hactualCost_le hsameCost hupCost
      hdownNoProfit

/--
Finite second-price best-response bridge for the displayed effort formula with
the source-shaped downward comparison against the applicant's actual chosen
effort.  The actual-cost, same-band, and upward-deviation cost comparisons are
still derived from boundary reachability and monotone cost.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_effort_formula_directional_actual_down
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdownNoProfitActual :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x)) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort := by
  have hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)) :=
    secondPrice_actualCost_le_boundary_of_effort_formula
      tilde cutoff actualBand theta effort hg_strict hInv hcost_mono
      htilde_feasible hf_theta_pos hactual_reaches_boundary
      heffort_formula
  have hsameCost :
      ∀ x d, deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d :=
    secondPrice_sameBandCost_le_of_effort_formula
      tilde cutoff actualBand deviationBand theta effort hg_strict hInv
      hcost_mono hf_theta_pos hdeviation_same_feasible
      hsame_reaches_boundary heffort_formula
  have hupCost :
      ∀ x d, actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d :=
    secondPrice_upwardCost_ge_boundary_of_score_boundary
      tilde cutoff actualBand deviationBand hg_strict hcost_mono
      htilde_feasible hf_cutoff_pos hdeviation_up_feasible
      hup_reaches_boundary
  exact
    secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations_directional_actual_down
      reward tilde actualBand deviationBand htilde hactualLevel
      hdeviationLevel hlevelReward hactualCost_le hsameCost hupCost
      hdownNoProfitActual

/--
Almost-everywhere finite second-price best-response bridge for the displayed
effort formula.  This is just the pointwise source-formula theorem lifted to
the measure-zero convention used by the paper.
-/
theorem secondPrice_fin_sourceRankBestResponseAE_of_effort_formula_directional
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdownNoProfit :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (tilde (actualBand x))) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
  sourceRankBestResponseAE_of_sourceRankBestResponse
    (secondPrice_fin_sourceRankBestResponse_of_effort_formula_directional
      reward tilde cutoff actualBand deviationBand hg_strict hInv hcost_mono
      htilde_feasible hf_theta_pos hf_cutoff_pos hdeviation_same_feasible
      hdeviation_up_feasible hactual_reaches_boundary hsame_reaches_boundary
      hup_reaches_boundary heffort_formula htilde hactualLevel
      hdeviationLevel hlevelReward hdownNoProfit)

/--
Almost-everywhere finite second-price best-response bridge for the displayed
effort formula with the source-shaped actual-effort downward comparison.
-/
theorem secondPrice_fin_sourceRankBestResponseAE_of_effort_formula_directional_actual_down
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdownNoProfitActual :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x)) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
  sourceRankBestResponseAE_of_sourceRankBestResponse
    (secondPrice_fin_sourceRankBestResponse_of_effort_formula_directional_actual_down
      reward tilde cutoff actualBand deviationBand hg_strict hInv hcost_mono
      htilde_feasible hf_theta_pos hf_cutoff_pos hdeviation_same_feasible
      hdeviation_up_feasible hactual_reaches_boundary hsame_reaches_boundary
      hup_reaches_boundary heffort_formula htilde hactualLevel
      hdeviationLevel hlevelReward hdownNoProfitActual)

/--
Finite second-price best-response bridge for the displayed effort formula,
deriving lower-band no-profit from the convex boundary-gap argument.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_effort_formula_convex_down
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d)) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort := by
  have hdown_boundary_gap :
      ∀ x d, deviationBand x d < actualBand x →
        reward (actualBand x) - reward (deviationBand x d) =
          costFn (tilde (actualBand x)) -
            costFn (tilde (deviationBand x d)) := by
    intro x d _hdown
    have hactual := htilde (actualBand x)
    have hdeviation := htilde (deviationBand x d)
    linarith
  have hdown_actual_le_boundary :
      ∀ x d, deviationBand x d < actualBand x →
        effort x ≤ tilde (actualBand x) := by
    intro x d _hdown
    rw [heffort_formula x]
    exact
      secondPriceEffort_le_boundary_of_reaches_boundary_score_of_rightInverse
        hg_strict (hf_theta_pos x) hInv (htilde_feasible (actualBand x))
        (hactual_reaches_boundary x)
  have hdownNoProfitActual :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x) := by
    intro x d hdown
    exact
      secondPrice_downward_no_profit_of_convex_boundary_gap
        hcost_conv hcost_strict
        (hdown_deviation_feasible x d hdown)
        (htilde_feasible (deviationBand x d))
        (hdown_actual_gt_deviation x d hdown)
        (hdown_actual_le_boundary x d hdown)
        (hdown_interval_len x d hdown)
        (hdown_boundary_gap x d hdown)
  exact
    secondPrice_fin_sourceRankBestResponse_of_effort_formula_directional_actual_down
      reward tilde cutoff actualBand deviationBand hg_strict hInv
      (hcost_strict.monotoneOn) htilde_feasible hf_theta_pos hf_cutoff_pos
      hdeviation_same_feasible hdeviation_up_feasible
      hactual_reaches_boundary hsame_reaches_boundary hup_reaches_boundary
      heffort_formula htilde hactualLevel hdeviationLevel hlevelReward
      hdownNoProfitActual

/--
Feasible-effort finite best-response bridge for the displayed effort formula,
deriving lower-band no-profit from the convex boundary-gap argument.  Unlike
the unrestricted bridge, this theorem does not require every real-valued
deviation to be feasible; it proves best response only against deviations
`d` satisfying the source effort-domain condition `e0 <= d`.
-/
theorem secondPrice_fin_sourceRankBestResponseFeasible_of_effort_formula_convex_down
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d)) :
    SourceRankBestResponseFeasible e0 costFn rankOfEffort rankLevel
      levelReward effort := by
  have heffort_feasible : ∀ x, e0 ≤ effort x := by
    intro x
    rw [heffort_formula x]
    exact secondPriceEffort_ge_e0 e0 gInv g f
      (tilde (actualBand x)) (cutoff (actualBand x)) (theta x)
  have hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)) :=
    secondPrice_actualCost_le_boundary_of_effort_formula
      tilde cutoff actualBand theta effort hg_strict hInv
      (hcost_strict.monotoneOn) htilde_feasible hf_theta_pos
      hactual_reaches_boundary heffort_formula
  have hsameCost :
      ∀ x d, e0 ≤ d → deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d := by
    intro x d hd hsame
    rw [heffort_formula x]
    exact
      secondPriceEffort_cost_le_of_reaches_boundary_score_of_rightInverse
        hg_strict (hf_theta_pos x) hInv (hcost_strict.monotoneOn) hd
        (hsame_reaches_boundary x d hsame)
  have hupCost :
      ∀ x d, e0 ≤ d → actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d := by
    intro x d hd hup
    have hscore : g (tilde (deviationBand x d)) ≤ g d := by
      exact le_of_mul_le_mul_right
        (hup_reaches_boundary x d hup)
        (hf_cutoff_pos (deviationBand x d))
    have htilde_le : tilde (deviationBand x d) ≤ d :=
      hg_strict.le_iff_le.mp hscore
    exact hcost_strict.monotoneOn
      (htilde_feasible (deviationBand x d)) hd htilde_le
  have hdown_boundary_gap :
      ∀ x d, deviationBand x d < actualBand x →
        reward (actualBand x) - reward (deviationBand x d) =
          costFn (tilde (actualBand x)) -
            costFn (tilde (deviationBand x d)) := by
    intro x d _hdown
    have hactual := htilde (actualBand x)
    have hdeviation := htilde (deviationBand x d)
    linarith
  have hdown_actual_le_boundary :
      ∀ x d, deviationBand x d < actualBand x →
        effort x ≤ tilde (actualBand x) := by
    intro x d _hdown
    rw [heffort_formula x]
    exact
      secondPriceEffort_le_boundary_of_reaches_boundary_score_of_rightInverse
        hg_strict (hf_theta_pos x) hInv (htilde_feasible (actualBand x))
        (hactual_reaches_boundary x)
  have hdownNoProfitActual :
      ∀ x d, e0 ≤ d → deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x) := by
    intro x d hd hdown
    exact
      secondPrice_downward_no_profit_of_convex_boundary_gap
        hcost_conv hcost_strict hd
        (htilde_feasible (deviationBand x d))
        (hdown_actual_gt_deviation x d hdown)
        (hdown_actual_le_boundary x d hdown)
        (hdown_interval_len x d hdown)
        (hdown_boundary_gap x d hdown)
  exact
    secondPrice_fin_sourceRankBestResponseFeasible_of_boundary_effort_equations_directional_actual_down
      reward tilde actualBand deviationBand heffort_feasible htilde
      hactualLevel hdeviationLevel hlevelReward hactualCost_le hsameCost
      hupCost hdownNoProfitActual

/--
Feasible-effort finite best-response bridge with same/upward reachability
needed only for feasible deviations.  This is the strictly source-domain
variant used by score-threshold classifiers: the source effort set is
`[e0, ∞)`, so off-domain real numbers need not be assigned meaningful
counterfactual score bands.
-/
theorem secondPrice_fin_sourceRankBestResponseFeasible_of_effort_formula_convex_down_feasible_reach
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, e0 ≤ d → deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, e0 ≤ d → actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d)) :
    SourceRankBestResponseFeasible e0 costFn rankOfEffort rankLevel
      levelReward effort := by
  have heffort_feasible : ∀ x, e0 ≤ effort x := by
    intro x
    rw [heffort_formula x]
    exact secondPriceEffort_ge_e0 e0 gInv g f
      (tilde (actualBand x)) (cutoff (actualBand x)) (theta x)
  have hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)) :=
    secondPrice_actualCost_le_boundary_of_effort_formula
      tilde cutoff actualBand theta effort hg_strict hInv
      (hcost_strict.monotoneOn) htilde_feasible hf_theta_pos
      hactual_reaches_boundary heffort_formula
  have hsameCost :
      ∀ x d, e0 ≤ d → deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d := by
    intro x d hd hsame
    rw [heffort_formula x]
    exact
      secondPriceEffort_cost_le_of_reaches_boundary_score_of_rightInverse
        hg_strict (hf_theta_pos x) hInv (hcost_strict.monotoneOn) hd
        (hsame_reaches_boundary x d hd hsame)
  have hupCost :
      ∀ x d, e0 ≤ d → actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d := by
    intro x d hd hup
    have hscore : g (tilde (deviationBand x d)) ≤ g d := by
      exact le_of_mul_le_mul_right
        (hup_reaches_boundary x d hd hup)
        (hf_cutoff_pos (deviationBand x d))
    have htilde_le : tilde (deviationBand x d) ≤ d :=
      hg_strict.le_iff_le.mp hscore
    exact hcost_strict.monotoneOn
      (htilde_feasible (deviationBand x d)) hd htilde_le
  have hdown_boundary_gap :
      ∀ x d, deviationBand x d < actualBand x →
        reward (actualBand x) - reward (deviationBand x d) =
          costFn (tilde (actualBand x)) -
            costFn (tilde (deviationBand x d)) := by
    intro x d _hdown
    have hactual := htilde (actualBand x)
    have hdeviation := htilde (deviationBand x d)
    linarith
  have hdown_actual_le_boundary :
      ∀ x d, deviationBand x d < actualBand x →
        effort x ≤ tilde (actualBand x) := by
    intro x d _hdown
    rw [heffort_formula x]
    exact
      secondPriceEffort_le_boundary_of_reaches_boundary_score_of_rightInverse
        hg_strict (hf_theta_pos x) hInv (htilde_feasible (actualBand x))
        (hactual_reaches_boundary x)
  have hdownNoProfitActual :
      ∀ x d, e0 ≤ d → deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x) := by
    intro x d hd hdown
    exact
      secondPrice_downward_no_profit_of_convex_boundary_gap
        hcost_conv hcost_strict hd
        (htilde_feasible (deviationBand x d))
        (hdown_actual_gt_deviation x d hdown)
        (hdown_actual_le_boundary x d hdown)
        (hdown_interval_len x d hdown)
        (hdown_boundary_gap x d hdown)
  exact
    secondPrice_fin_sourceRankBestResponseFeasible_of_boundary_effort_equations_directional_actual_down
      reward tilde actualBand deviationBand heffort_feasible htilde
      hactualLevel hdeviationLevel hlevelReward hactualCost_le hsameCost
      hupCost hdownNoProfitActual

/--
Finite-band second-price best-response theorem with no rank/score overload.
The conclusion is stated directly in finite reward bands, while rank
preservation can be paired separately with the tie-broken score-order theorem.
-/
theorem secondPrice_fin_finiteBandBestResponseFeasible_of_effort_formula_convex_down_feasible_reach
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, e0 ≤ d → deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, e0 ≤ d → actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d)) :
    FiniteBandBestResponseFeasible e0 costFn reward actualBand
      deviationBand effort := by
  have heffort_feasible : ∀ x, e0 ≤ effort x := by
    intro x
    rw [heffort_formula x]
    exact secondPriceEffort_ge_e0 e0 gInv g f
      (tilde (actualBand x)) (cutoff (actualBand x)) (theta x)
  have hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)) :=
    secondPrice_actualCost_le_boundary_of_effort_formula
      tilde cutoff actualBand theta effort hg_strict hInv
      (hcost_strict.monotoneOn) htilde_feasible hf_theta_pos
      hactual_reaches_boundary heffort_formula
  have hsameCost :
      ∀ x d, e0 ≤ d → deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d := by
    intro x d hd hsame
    rw [heffort_formula x]
    exact
      secondPriceEffort_cost_le_of_reaches_boundary_score_of_rightInverse
        hg_strict (hf_theta_pos x) hInv (hcost_strict.monotoneOn) hd
        (hsame_reaches_boundary x d hd hsame)
  have hupCost :
      ∀ x d, e0 ≤ d → actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d := by
    intro x d hd hup
    have hscore : g (tilde (deviationBand x d)) ≤ g d := by
      exact le_of_mul_le_mul_right
        (hup_reaches_boundary x d hd hup)
        (hf_cutoff_pos (deviationBand x d))
    have htilde_le : tilde (deviationBand x d) ≤ d :=
      hg_strict.le_iff_le.mp hscore
    exact hcost_strict.monotoneOn
      (htilde_feasible (deviationBand x d)) hd htilde_le
  have hdown_boundary_gap :
      ∀ x d, deviationBand x d < actualBand x →
        reward (actualBand x) - reward (deviationBand x d) =
          costFn (tilde (actualBand x)) -
            costFn (tilde (deviationBand x d)) := by
    intro x d _hdown
    have hactual := htilde (actualBand x)
    have hdeviation := htilde (deviationBand x d)
    linarith
  have hdown_actual_le_boundary :
      ∀ x d, deviationBand x d < actualBand x →
        effort x ≤ tilde (actualBand x) := by
    intro x d _hdown
    rw [heffort_formula x]
    exact
      secondPriceEffort_le_boundary_of_reaches_boundary_score_of_rightInverse
        hg_strict (hf_theta_pos x) hInv (htilde_feasible (actualBand x))
        (hactual_reaches_boundary x)
  have hdownNoProfitActual :
      ∀ x d, e0 ≤ d → deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x) := by
    intro x d hd hdown
    exact
      secondPrice_downward_no_profit_of_convex_boundary_gap
        hcost_conv hcost_strict hd
        (htilde_feasible (deviationBand x d))
        (hdown_actual_gt_deviation x d hdown)
        (hdown_actual_le_boundary x d hdown)
        (hdown_interval_len x d hdown)
        (hdown_boundary_gap x d hdown)
  refine ⟨heffort_feasible, ?_⟩
  intro x d hd
  let i := actualBand x
  let j := deviationBand x d
  have hboundaryUtility :
      ∀ a b : Fin (n + 1),
        reward a - costFn (tilde a) = reward b - costFn (tilde b) := by
    intro a b
    have ha := htilde a
    have hb := htilde b
    change reward a - costFn (tilde a) = reward b - costFn (tilde b)
    rw [ha, hb]
    ring
  have hactual_lower :
      reward i - costFn (tilde i) ≤
        reward i - costFn (effort x) := by
    dsimp [i]
    linarith [hactualCost_le x]
  rcases lt_trichotomy i j with hij | hij | hij
  · have hdeviation_upper :
        reward j - costFn d ≤ reward j - costFn (tilde j) := by
      dsimp [j]
      linarith [hupCost x d hd hij]
    exact le_trans hdeviation_upper
      (le_trans (le_of_eq (hboundaryUtility j i)) hactual_lower)
  · have hsame : j = i := hij.symm
    have hsame_cost := hsameCost x d hd (by simpa [i, j] using hsame)
    have hreward_eq : reward j = reward i := by rw [hsame]
    linarith
  · exact hdownNoProfitActual x d hd hij

/--
Finite second-price best-response bridge where the downward interval-length
condition is derived from the paper's four multiplicative score equalities.
This is the source-shaped version of the convex downward-deviation step:
the high-skill applicant's move from the lower score to the higher score is
shorter than the corresponding lower-skill boundary move by Appendix
Lemma `order_g`.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_effort_formula_convex_down_from_score_equalities
    {α : Type*} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (downSkillLow downSkillHigh downScoreLow downScoreHigh : α → ℝ → ℝ)
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_skillLow_pos :
      ∀ x d, deviationBand x d < actualBand x → 0 < downSkillLow x d)
    (hdown_skill_order :
      ∀ x d, deviationBand x d < actualBand x →
        downSkillLow x d < downSkillHigh x d)
    (hdown_scoreLow_nonneg :
      ∀ x d, deviationBand x d < actualBand x → 0 ≤ downScoreLow x d)
    (hdown_score_order :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d < downScoreHigh x d)
    (hdown_deviation_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d = g d * downSkillHigh x d)
    (hdown_actual_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d = g (effort x) * downSkillHigh x d)
    (hdown_boundaryLow_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreLow x d =
          g (tilde (deviationBand x d)) * downSkillLow x d)
    (hdown_boundaryHigh_score :
      ∀ x d, deviationBand x d < actualBand x →
        downScoreHigh x d =
          g (tilde (actualBand x)) * downSkillLow x d) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort := by
  have hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d) := by
    intro x d hdown
    exact
      source_multiplicative_score_equalities_imply_effort_interval_order
        (g := g)
        (skillLow := downSkillLow x d)
        (skillHigh := downSkillHigh x d)
        (scoreLow := downScoreLow x d)
        (scoreHigh := downScoreHigh x d)
        (e := d)
        (eToHigh := effort x)
        (eHighToLow := tilde (deviationBand x d))
        (eHigh := tilde (actualBand x))
        hg_conc hg_strict.monotone hg_strict
        (hdown_skillLow_pos x d hdown)
        (hdown_skill_order x d hdown)
        (hdown_scoreLow_nonneg x d hdown)
        (hdown_score_order x d hdown)
        (hdown_deviation_score x d hdown)
        (hdown_actual_score x d hdown)
        (hdown_boundaryLow_score x d hdown)
        (hdown_boundaryHigh_score x d hdown)
  exact
    secondPrice_fin_sourceRankBestResponse_of_effort_formula_convex_down
      reward tilde cutoff actualBand deviationBand hg_strict hInv hcost_conv
      hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
      hdeviation_same_feasible hdeviation_up_feasible hactual_reaches_boundary
      hsame_reaches_boundary hup_reaches_boundary heffort_formula htilde
      hactualLevel hdeviationLevel hlevelReward hdown_deviation_feasible
      hdown_actual_gt_deviation hdown_interval_len

/--
Almost-everywhere finite second-price best-response bridge for the displayed
effort formula, with lower-band no-profit derived from convex boundary gaps.
-/
theorem secondPrice_fin_sourceRankBestResponseAE_of_effort_formula_convex_down
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d)) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
  sourceRankBestResponseAE_of_sourceRankBestResponse
    (secondPrice_fin_sourceRankBestResponse_of_effort_formula_convex_down
      reward tilde cutoff actualBand deviationBand hg_strict hInv hcost_conv
      hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
      hdeviation_same_feasible hdeviation_up_feasible hactual_reaches_boundary
      hsame_reaches_boundary hup_reaches_boundary heffort_formula htilde
      hactualLevel hdeviationLevel hlevelReward hdown_deviation_feasible
      hdown_actual_gt_deviation hdown_interval_len)

/--
Almost-everywhere finite best-response bridge from a source score-threshold
classifier.  Instead of assuming that every deviation assigned to a band
directly clears that band's boundary effort, the caller supplies the
paper-shaped score condition: a deviation assigned to band `j` reaches
`g(tilde j) * f(cutoff j)`.  Same-band reachability is immediate, and upward
reachability follows from the source fact that a lower-band type lies below
the higher band's cutoff.
-/
theorem secondPrice_fin_sourceRankBestResponseAE_of_score_thresholds_convex_down
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hInv : Function.RightInverse gInv g)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hf_mono : Monotone f)
    (hdeviation_feasible : ∀ (x : α) (d : ℝ), e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hdeviation_reaches_target :
      ∀ (x : α) (d : ℝ),
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (theta x))
    (hup_cutoff_upper :
      ∀ (x : α) (d : ℝ), actualBand x < deviationBand x d →
        theta x ≤ cutoff (deviationBand x d))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ (x : α) (d : ℝ),
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_actual_gt_deviation :
      ∀ (x : α) (d : ℝ), deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ (x : α) (d : ℝ), deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d)) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort := by
  have hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d := by
    intro x d _hsame
    exact hdeviation_feasible x d
  have hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d := by
    intro x d _hup
    exact hdeviation_feasible x d
  have hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d := by
    intro x d _hdown
    exact hdeviation_feasible x d
  have hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x) := by
    intro x d hsame
    simpa [hsame] using hdeviation_reaches_target x d
  have hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)) := by
    intro x d hup
    exact le_trans (hdeviation_reaches_target x d)
      (mul_le_mul_of_nonneg_left
        (hf_mono (hup_cutoff_upper x d hup)) (hg_nonneg d))
  exact
    secondPrice_fin_sourceRankBestResponseAE_of_effort_formula_convex_down
      reward tilde cutoff actualBand deviationBand hg_strict hInv hcost_conv
      hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
      hdeviation_same_feasible hdeviation_up_feasible hactual_reaches_boundary
      hsame_reaches_boundary hup_reaches_boundary heffort_formula htilde
      hactualLevel hdeviationLevel hlevelReward hdown_deviation_feasible
      hdown_actual_gt_deviation hdown_interval_len

/--
Feasible-effort a.e. finite best-response bridge from a source
score-threshold classifier.  This is the paper-domain variant of
`secondPrice_fin_sourceRankBestResponseAE_of_score_thresholds_convex_down`:
deviations are checked only when they satisfy `e0 <= d`, matching the source
effort domain.
-/
theorem secondPrice_fin_sourceRankBestResponseFeasibleAE_of_score_thresholds_convex_down
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hInv : Function.RightInverse gInv g)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hf_mono : Monotone f)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hdeviation_reaches_target :
      ∀ (x : α) (d : ℝ),
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (theta x))
    (hup_cutoff_upper :
      ∀ (x : α) (d : ℝ), actualBand x < deviationBand x d →
        theta x ≤ cutoff (deviationBand x d))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ (x : α) (d : ℝ),
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_actual_gt_deviation :
      ∀ (x : α) (d : ℝ), deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ (x : α) (d : ℝ), deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d)) :
    SourceRankBestResponseFeasibleAE μ e0 costFn rankOfEffort rankLevel
      levelReward effort := by
  have hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x) := by
    intro x d hsame
    simpa [hsame] using hdeviation_reaches_target x d
  have hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)) := by
    intro x d hup
    exact le_trans (hdeviation_reaches_target x d)
      (mul_le_mul_of_nonneg_left
        (hf_mono (hup_cutoff_upper x d hup)) (hg_nonneg d))
  exact
    sourceRankBestResponseFeasibleAE_of_sourceRankBestResponseFeasible
      (secondPrice_fin_sourceRankBestResponseFeasible_of_effort_formula_convex_down
        reward tilde cutoff actualBand deviationBand hg_strict hInv hcost_conv
        hcost_strict htilde_feasible hf_theta_pos hf_cutoff_pos
        hactual_reaches_boundary hsame_reaches_boundary hup_reaches_boundary
        heffort_formula htilde hactualLevel hdeviationLevel hlevelReward
        hdown_actual_gt_deviation hdown_interval_len)

/--
Almost-everywhere version of the weak-actual-cost finite second-price bridge.
-/
theorem secondPrice_fin_sourceRankBestResponseAE_of_boundary_effort_equations_actual_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)))
    (hdeviationCost :
      ∀ x d, costFn (tilde (deviationBand x d)) ≤ costFn d) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
  sourceRankBestResponseAE_of_sourceRankBestResponse
    (secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations_actual_le
      reward tilde actualBand deviationBand htilde hactualLevel
      hdeviationLevel hlevelReward hactualCost_le hdeviationCost)

/--
Almost-everywhere finite second-price best-response bridge from boundary
effort equations and effort-threshold comparisons.
-/
theorem secondPrice_fin_sourceRankBestResponseAE_of_boundary_effort_thresholds
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ} {e0 : ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualEffort :
      ∀ x, effort x = tilde (actualBand x))
    (hdeviationEffort :
      ∀ x d, tilde (deviationBand x d) ≤ d) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
  sourceRankBestResponseAE_of_sourceRankBestResponse
    (secondPrice_fin_sourceRankBestResponse_of_boundary_effort_thresholds
      reward tilde actualBand deviationBand hcost_mono htilde_feasible
      htilde hactualLevel hdeviationLevel hlevelReward hactualEffort
      hdeviationEffort)

/--
Finite second-price best-response bridge for the displayed boundary-effort
function itself.  The actual effort profile is `tilde (actualBand x)`, so no
separate actual-effort equality premise is needed.
-/
theorem secondPrice_fin_sourceRankBestResponse_of_boundary_effort_function
    {α : Type*} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ} {e0 : ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (tilde (actualBand x))) =
          (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdeviationEffort :
      ∀ x d, tilde (deviationBand x d) ≤ d) :
    SourceRankBestResponse costFn rankOfEffort rankLevel levelReward
      (fun x => tilde (actualBand x)) :=
  secondPrice_fin_sourceRankBestResponse_of_boundary_effort_thresholds
    reward tilde actualBand deviationBand hcost_mono htilde_feasible htilde
    hactualLevel hdeviationLevel hlevelReward (fun _ => rfl)
    hdeviationEffort

/--
Almost-everywhere finite second-price best-response bridge for the displayed
boundary-effort function itself.
-/
theorem secondPrice_fin_sourceRankBestResponseAE_of_boundary_effort_function
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ} {e0 : ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (hcost_mono : MonotoneOn costFn (Set.Ici e0))
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (tilde (actualBand x))) =
          (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdeviationEffort :
      ∀ x d, tilde (deviationBand x d) ≤ d) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward
      (fun x => tilde (actualBand x)) :=
  sourceRankBestResponseAE_of_sourceRankBestResponse
    (secondPrice_fin_sourceRankBestResponse_of_boundary_effort_function
      reward tilde actualBand deviationBand hcost_mono htilde_feasible htilde
      hactualLevel hdeviationLevel hlevelReward hdeviationEffort)

/--
Almost-everywhere version of the finite second-price best-response bridge.
The pointwise finite construction is enough to satisfy the source's
measure-zero convention under any applicant law.
-/
theorem secondPrice_fin_sourceRankBestResponseAE_of_boundary_effort_equations
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {n : ℕ}
    {costFn : ℝ → ℝ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {effort : α → ℝ}
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost :
      ∀ x, costFn (effort x) = costFn (tilde (actualBand x)))
    (hdeviationCost :
      ∀ x d, costFn (tilde (deviationBand x d)) ≤ costFn d) :
    SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
  sourceRankBestResponseAE_of_sourceRankBestResponse
    (secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations
      reward tilde actualBand deviationBand htilde hactualLevel
      hdeviationLevel hlevelReward hactualCost hdeviationCost)

/--
Two-level reward reachability from the concrete high-band reach predicate.  If
reaching a high applicant's score forces a deviation into the high band, then
the deviation receives at least that applicant's realized two-level reward.
-/
theorem secondPrice_twoLevel_deviation_reward_reach_of_score_reaches_high
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {score tie skill effort : α → ℝ} {g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ}
    {lowReward highReward : ℝ}
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hlow_le_high : lowReward ≤ highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hscore_reaches_high :
      ∀ x y d, actualHigh y → score y ≤ g d * skill x →
        reachesHigh x d) :
    ∀ x y d, score y ≤ g d * skill x →
      levelReward (rankLevel (tieBrokenRank μ score tie y)) ≤
        levelReward (rankLevel (rankOfEffort x d)) := by
  intro x y d hscore_le
  have hy_actual_level :
      rankLevel (rankOfEffort y (effort y)) =
        if actualHigh y then 1 else 0 := by
    rw [hlevel y (effort y)]
    by_cases hy : actualHigh y
    · have hreaches : reachesHigh y (effort y) := (hactual_reaches y).2 hy
      simp [hy, hreaches]
    · have hnreaches : ¬ reachesHigh y (effort y) := by
        intro hreaches
        exact hy ((hactual_reaches y).1 hreaches)
      simp [hy, hnreaches]
  have hy_post_level :
      rankLevel (tieBrokenRank μ score tie y) =
        if actualHigh y then 1 else 0 := by
    rw [← hpost_actual y]
    exact hy_actual_level
  rw [hy_post_level, hlevel x d]
  by_cases hy : actualHigh y
  · have hx_reaches : reachesHigh x d :=
      hscore_reaches_high x y d hy hscore_le
    simp [hy, hx_reaches, hlevel_one]
  · by_cases hx_reaches : reachesHigh x d
    · simp [hy, hx_reaches, hlevel_zero, hlevel_one, hlow_le_high]
    · simp [hy, hx_reaches, hlevel_zero]

/--
Local-post version of
`secondPrice_twoLevel_deviation_reward_reach_of_score_reaches_high`, used when
the realized post-rank relation is available only off a null set.
-/
theorem secondPrice_twoLevel_deviation_reward_reach_of_score_reaches_high_at
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {score tie skill effort : α → ℝ} {g : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ} {rankLevel : ℝ → ℕ}
    {levelReward : ℕ → ℝ}
    {lowReward highReward : ℝ}
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hlow_le_high : lowReward ≤ highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (hscore_reaches_high :
      ∀ x y d, actualHigh y → score y ≤ g d * skill x →
        reachesHigh x d)
    {x y : α} {d : ℝ}
    (hpost_actual_y :
      rankLevel (rankOfEffort y (effort y)) =
        rankLevel (tieBrokenRank μ score tie y))
    (hscore_le : score y ≤ g d * skill x) :
    levelReward (rankLevel (tieBrokenRank μ score tie y)) ≤
      levelReward (rankLevel (rankOfEffort x d)) := by
  have hy_actual_level :
      rankLevel (rankOfEffort y (effort y)) =
        if actualHigh y then 1 else 0 := by
    rw [hlevel y (effort y)]
    by_cases hy : actualHigh y
    · have hreaches : reachesHigh y (effort y) := (hactual_reaches y).2 hy
      simp [hy, hreaches]
    · have hnreaches : ¬ reachesHigh y (effort y) := by
        intro hreaches
        exact hy ((hactual_reaches y).1 hreaches)
      simp [hy, hnreaches]
  have hy_post_level :
      rankLevel (tieBrokenRank μ score tie y) =
        if actualHigh y then 1 else 0 := by
    rw [← hpost_actual_y]
    exact hy_actual_level
  rw [hy_post_level, hlevel x d]
  by_cases hy : actualHigh y
  · have hx_reaches : reachesHigh x d :=
      hscore_reaches_high x y d hy hscore_le
    simp [hy, hx_reaches, hlevel_one]
  · by_cases hx_reaches : reachesHigh x d
    · simp [hy, hx_reaches, hlevel_zero, hlevel_one, hlow_le_high]
    · simp [hy, hx_reaches, hlevel_zero]

/--
Finite second-price boundary equations feed directly into the continuum
rank-preservation bridge once the source gamma construction is available as a
uniform pre-rank/lexicographic contour statement.  This theorem keeps the two
remaining source-model ingredients visible: the boundary cost comparisons that
make deviations expensive, and the gamma construction property.
-/
theorem secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_and_gamma_lex_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost :
      ∀ x, costFn (effort x) = costFn (tilde (actualBand x)))
    (hdeviationCost :
      ∀ x d, costFn (tilde (deviationBand x d)) ≤ costFn d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hlex :
      ∀ x y,
        (score y < score x ∨ score y = score x ∧ tie y ≤ tie x) ↔
          preRank y ≤ preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
    secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations
      reward tilde actualBand deviationBand htilde hactualLevel
      hdeviationLevel hlevelReward hactualCost hdeviationCost
  have hbestAE :
      SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
    sourceRankBestResponseAE_of_sourceRankBestResponse hbest
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_lex_preRank_ae_post_actual
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hlex

/--
Finite second-price boundary equations plus the source-shaped gamma
construction where the public tie key is the source pre-rank label.  This
avoids a raw lexicographic-order certificate when the score order and tie key
are available separately.
-/
theorem secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_and_score_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost :
      ∀ x, costFn (effort x) = costFn (tilde (actualBand x)))
    (hdeviationCost :
      ∀ x d, costFn (tilde (deviationBand x d)) ≤ costFn d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
    secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations
      reward tilde actualBand deviationBand htilde hactualLevel
      hdeviationLevel hlevelReward hactualCost hdeviationCost
  have hbestAE :
      SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
    sourceRankBestResponseAE_of_sourceRankBestResponse hbest
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_ae_post_actual
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Finite second-price boundary equations plus the source-shaped gamma
construction, with weak actual boundary costs.  This is the finite
rank-preservation bridge needed for the displayed within-band second-price
effort formula: actual applicants may pay weakly less than their band's
boundary effort while deviations into a band still have to pay at least that
boundary effort.
-/
theorem secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_actual_le_and_score_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)))
    (hdeviationCost :
      ∀ x d, costFn (tilde (deviationBand x d)) ≤ costFn d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
    secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations_actual_le
      reward tilde actualBand deviationBand htilde hactualLevel
      hdeviationLevel hlevelReward hactualCost_le hdeviationCost
  have hbestAE :
      SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
    sourceRankBestResponseAE_of_sourceRankBestResponse hbest
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_ae_post_actual
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Finite second-price boundary equations plus the source-shaped gamma
construction, with direction-aware deviation checks.  This avoids the
over-strong requirement that every downward deviation pay the target band's
boundary cost.
-/
theorem secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_directional_and_score_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)))
    (hsameCost :
      ∀ x d, deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d)
    (hupCost :
      ∀ x d, actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d)
    (hdownNoProfit :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (tilde (actualBand x)))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
    secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations_directional
      reward tilde actualBand deviationBand htilde hactualLevel
      hdeviationLevel hlevelReward hactualCost_le hsameCost hupCost
      hdownNoProfit
  have hbestAE :
      SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
    sourceRankBestResponseAE_of_sourceRankBestResponse hbest
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_ae_post_actual
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Finite second-price boundary equations plus the source-shaped gamma
construction, with direction-aware deviation checks and the source-shaped
downward comparison against actual effort.
-/
theorem secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_directional_actual_down_and_score_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn g : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)))
    (hsameCost :
      ∀ x d, deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d)
    (hupCost :
      ∀ x d, actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d)
    (hdownNoProfitActual :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x)
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
    secondPrice_fin_sourceRankBestResponse_of_boundary_effort_equations_directional_actual_down
      reward tilde actualBand deviationBand htilde hactualLevel
      hdeviationLevel hlevelReward hactualCost_le hsameCost hupCost
      hdownNoProfitActual
  have hbestAE :
      SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
    sourceRankBestResponseAE_of_sourceRankBestResponse hbest
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_ae_post_actual
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Within a finite reward band, the source score expression
`max(boundary target, baseline score)` is monotone in source type.  The
between-band separation step is separate; together they imply the global score
order used by the finite rank-preservation bridge.
-/
theorem finiteBand_within_score_mono_of_source_max_formula
    {α β : Type*} {preRank theta score : α → ℝ} {band : α → β}
    {bandTarget : β → ℝ} {e0 : ℝ} {g f : ℝ → ℝ}
    (hf_mono : Monotone f)
    (hbaseline_nonneg : 0 ≤ g e0)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (band x)) (g e0 * f (theta x))) :
    ∀ x y, band y = band x → preRank y ≤ preRank x → score y ≤ score x := by
  intro x y hband hpre
  rw [hscore_formula y, hscore_formula x, hband]
  exact max_le_max le_rfl
    (mul_le_mul_of_nonneg_left (hf_mono (htheta_mono x y hpre))
      hbaseline_nonneg)

/--
Between finite reward bands, it is enough to show that all lower-band scores
are bounded by the higher band's boundary target.  The displayed second-price
score formula then implies the higher-band applicant's score is at least that
target.
-/
theorem finiteBand_between_score_mono_of_boundary_targets
    {α β : Type*} [Preorder β] {score : α → ℝ} {band : α → β}
    {bandTarget : β → ℝ} {e0 : ℝ} {g f : ℝ → ℝ} {theta : α → ℝ}
    (hscore_formula :
      ∀ x, score x = max (bandTarget (band x)) (g e0 * f (theta x)))
    (hprevious_bands_below_target :
      ∀ x y, band y < band x → score y ≤ bandTarget (band x)) :
    ∀ x y, band y < band x → score y ≤ score x := by
  intro x y hband
  exact le_trans (hprevious_bands_below_target x y hband) (by
    rw [hscore_formula x]
    exact le_max_left _ _)

/--
Per-band score upper bounds are enough to prove the previous-band
boundary-target condition used by the finite second-price endpoint.
-/
theorem finiteBand_previous_bands_below_target_of_band_upper_bounds
    {α β : Type*} [Preorder β] {score : α → ℝ} {band : α → β}
    {bandUpper bandTarget : β → ℝ}
    (hscore_le_upper : ∀ y, score y ≤ bandUpper (band y))
    (hupper_le_target :
      ∀ {i j}, i < j → bandUpper i ≤ bandTarget j) :
    ∀ x y, band y < band x → score y ≤ bandTarget (band x) := by
  intro x y hband
  exact le_trans (hscore_le_upper y) (hupper_le_target hband)

/--
Source max-score version of the previous-band boundary-target condition.
If each realized score is the maximum of its own boundary target and baseline
score, boundary targets are monotone across bands, and the baseline score is
already below the applicant's own band target, then every lower-band score is
below any higher band's boundary target.
-/
theorem finiteBand_previous_bands_below_target_of_source_max_formula
    {α β : Type*} [Preorder β] {score theta : α → ℝ} {band : α → β}
    {bandTarget : β → ℝ} {e0 : ℝ} {g f : ℝ → ℝ}
    (hscore_formula :
      ∀ x, score x = max (bandTarget (band x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (band x)) :
    ∀ x y, band y < band x → score y ≤ bandTarget (band x) := by
  intro x y hband
  rw [hscore_formula y]
  have htarget : bandTarget (band y) ≤ bandTarget (band x) :=
    hbandTarget_mono (le_of_lt hband)
  have hbase : g e0 * f (theta y) ≤ bandTarget (band x) :=
    le_trans (hbaseline_le_bandTarget y) htarget
  exact max_le htarget hbase

/--
Source max-score version of the previous-band separation condition with only a
lower-to-later baseline bound.  This mirrors the finite K-level proof: for a
lower-band applicant, both its boundary target and its baseline score are below
the later band's boundary target, so its max-score is also below that target.
-/
theorem finiteBand_previous_bands_below_target_of_source_max_formula_lower_baseline
    {α β : Type*} [Preorder β] {score theta : α → ℝ} {band : α → β}
    {bandTarget : β → ℝ} {e0 : ℝ} {g f : ℝ → ℝ}
    (hscore_formula :
      ∀ x, score x = max (bandTarget (band x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_later_target :
      ∀ x y, band y < band x → g e0 * f (theta y) ≤ bandTarget (band x)) :
    ∀ x y, band y < band x → score y ≤ bandTarget (band x) := by
  intro x y hband
  rw [hscore_formula y]
  have htarget : bandTarget (band y) ≤ bandTarget (band x) :=
    hbandTarget_mono (le_of_lt hband)
  have hbase : g e0 * f (theta y) ≤ bandTarget (band x) :=
    hbaseline_le_later_target x y hband
  exact max_le htarget hbase

/--
Cutoff-interval version of the lower-to-later baseline bound.  If every
lower-band applicant's source type is at most the later band's cutoff, then
monotone effort and type factors put the lower baseline score below the later
boundary target.
-/
theorem finiteBand_lower_baseline_le_later_target_of_cutoff_interval_order
    {α β : Type*} [Preorder β] {theta : α → ℝ} {band : α → β}
    {tilde cutoff : β → ℝ} {e0 : ℝ} {g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hf_mono : Monotone f)
    (hf_theta_nonneg : ∀ x, 0 ≤ f (theta x))
    (htilde_feasible : ∀ i, e0 ≤ tilde i)
    (hcutoff_interval_upper :
      ∀ x y, band y < band x → theta y ≤ cutoff (band x)) :
    ∀ x y, band y < band x →
      g e0 * f (theta y) ≤ g (tilde (band x)) * f (cutoff (band x)) := by
  intro x y hband
  have hg_le : g e0 ≤ g (tilde (band x)) :=
    hg_mono (htilde_feasible (band x))
  have hf_le : f (theta y) ≤ f (cutoff (band x)) :=
    hf_mono (hcutoff_interval_upper x y hband)
  exact mul_le_mul hg_le hf_le (hf_theta_nonneg y) (hg_nonneg (tilde (band x)))

/--
Band order from a source rank-level representation.  If the finite band index
is the value of a monotone source rank-level map applied to the pre-effort
rank, then pre-rank order implies band order.
-/
theorem finiteBand_order_of_rankLevel_value
    {α : Type*} {n : ℕ} {preRank : α → ℝ} {rankLevel : ℝ → ℕ}
    {band : α → Fin (n + 1)}
    (hrankLevel_mono : Monotone rankLevel)
    (hband_val : ∀ x, (band x).val = rankLevel (preRank x)) :
    ∀ x y, preRank y ≤ preRank x → band y ≤ band x := by
  intro x y hpre
  rw [Fin.le_iff_val_le_val, hband_val y, hband_val x]
  exact hrankLevel_mono hpre

/--
Cutoff interval order from rank-level cutoff semantics.  If the finite band
index is the source rank-level value, and each displayed cutoff bounds all
strictly lower source levels from above, then every lower-band applicant lies
below the later band's cutoff.
-/
theorem finiteBand_cutoff_interval_upper_of_rankLevel_value
    {α : Type*} {n : ℕ} {preRank theta : α → ℝ} {rankLevel : ℝ → ℕ}
    {band : α → Fin (n + 1)} {cutoff : Fin (n + 1) → ℝ}
    (hband_val : ∀ x, (band x).val = rankLevel (preRank x))
    (hcutoff_upper_by_level :
      ∀ i : Fin (n + 1), ∀ y, rankLevel (preRank y) < i.val →
        theta y ≤ cutoff i) :
    ∀ x y, band y < band x → theta y ≤ cutoff (band x) := by
  intro x y hband
  exact hcutoff_upper_by_level (band x) y (by
    rw [← hband_val y]
    exact Fin.lt_def.mp hband)

/--
Score-target classifier from rank-level threshold semantics.  If the
deviation score is the source multiplicative score and each finite rank level
has a displayed lower score target, then any deviation assigned to a band
reaches that band's target.
-/
theorem finiteBand_deviation_reaches_target_of_rankLevel_target_lower
    {α : Type*} {n : ℕ} {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {theta : α → ℝ}
    {deviationBand : α → ℝ → Fin (n + 1)}
    {tilde cutoff : Fin (n + 1) → ℝ} {g f : ℝ → ℝ}
    (hdeviationLevel :
      ∀ (x : α) (d : ℝ),
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hdeviation_score :
      ∀ (x : α) (d : ℝ), rankOfEffort x d = g d * f (theta x))
    (hrankLevel_target_lower :
      ∀ i : Fin (n + 1), ∀ z,
        rankLevel z = i.val → g (tilde i) * f (cutoff i) ≤ z) :
    ∀ (x : α) (d : ℝ),
      g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
        g d * f (theta x) := by
  intro x d
  rw [← hdeviation_score x d]
  exact hrankLevel_target_lower (deviationBand x d) (rankOfEffort x d)
    (hdeviationLevel x d)

/--
Actual-band classifier from displayed second-price score bounds.  The
post-effort score is derived from the second-price formula; the caller supplies
only the source band semantics saying that scores between the displayed lower
target and upper band bound have the displayed rank level.
-/
theorem finiteBand_actualLevel_of_secondPrice_score_band_bounds
    {α : Type*} {n : ℕ} {gInv g f : ℝ → ℝ} {e0 : ℝ}
    {rankOfEffort : α → ℝ → ℝ} {rankLevel : ℝ → ℕ}
    {theta : α → ℝ}
    (tilde cutoff bandUpper : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_mono : Monotone g)
    (hInv : Function.RightInverse gInv g)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hdeviation_score :
      ∀ (x : α) (d : ℝ), rankOfEffort x d = g d * f (theta x))
    (hactual_score_upper :
      ∀ x,
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
            (g e0 * f (theta x)) ≤
          bandUpper (actualBand x))
    (hrank_score_band :
      ∀ i : Fin (n + 1), ∀ z,
        g (tilde i) * f (cutoff i) ≤ z →
        z ≤ bandUpper i →
        rankLevel z = i.val) :
    ∀ x,
      rankLevel
          (rankOfEffort x
            (secondPriceEffort e0 gInv g f (tilde (actualBand x))
              (cutoff (actualBand x)) (theta x))) =
        (actualBand x).val := by
  intro x
  rw [hdeviation_score x]
  let z :=
    g (secondPriceEffort e0 gInv g f (tilde (actualBand x))
      (cutoff (actualBand x)) (theta x)) * f (theta x)
  have hscore :
      z =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x)) := by
    dsimp [z]
    exact secondPriceEffort_score_eq_max_of_rightInverse
      hg_mono (hf_theta_pos x) hInv
  have htarget_le : g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤ z := by
    rw [hscore]
    exact le_max_left _ _
  have hupper : z ≤ bandUpper (actualBand x) := by
    rw [hscore]
    exact hactual_score_upper x
  exact hrank_score_band (actualBand x) z htarget_le hupper

/--
Finite-band source-order rank preservation from the displayed max-score
formula and the source tie key.  Once the score is monotone in the source
rank and ties are broken by the source rank itself, the tie-broken post-rank is
pointwise equal to the pre-rank; no separate gamma/PIT certificate is needed.
-/
theorem finiteBand_rankPreservationAE_of_source_max_formula_and_tie_eq_preRank
    {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] [PartialOrder β]
    {preRank score tie theta : α → ℝ} {band : α → β}
    {bandTarget : β → ℝ} {e0 : ℝ} {g f : ℝ → ℝ}
    (rankLevel : ℝ → ℕ)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hband_order :
      ∀ x y, preRank y ≤ preRank x → band y ≤ band x)
    (hf_mono : Monotone f)
    (hbaseline_nonneg : 0 ≤ g e0)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (band x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (band x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hprevious_bands_below_target :
      ∀ x y, band y < band x → score y ≤ bandTarget (band x) :=
    finiteBand_previous_bands_below_target_of_source_max_formula
      hscore_formula hbandTarget_mono hbaseline_le_bandTarget
  have hscore_within_band :
      ∀ x y, band y = band x → preRank y ≤ preRank x →
        score y ≤ score x :=
    finiteBand_within_score_mono_of_source_max_formula
      hf_mono hbaseline_nonneg htheta_mono hscore_formula
  have hscore_between_bands :
      ∀ x y, band y < band x → score y ≤ score x :=
    finiteBand_between_score_mono_of_boundary_targets
      hscore_formula hprevious_bands_below_target
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x := by
    intro x y hpre
    have hband_le : band y ≤ band x := hband_order x y hpre
    rcases lt_or_eq_of_le hband_le with hlt | heq
    · exact hscore_between_bands x y hlt
    · exact hscore_within_band x y heq hpre
  have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
      hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
  exact Filter.Eventually.of_forall (fun x => by
    change rankLevel (tieBrokenRank μ score tie x) = rankLevel (preRank x)
    rw [hrank_eq x])

/--
Finite-band rank preservation from the displayed source max-score formula and
the source tie key, using the paper's previous-band separation condition
directly.  This is weaker than requiring every baseline score to sit below its
own band's target; the source proof only needs lower-band scores to be below
later boundary targets.
-/
theorem finiteBand_rankPreservationAE_of_source_max_formula_previous_bands_and_tie_eq_preRank
    {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] [PartialOrder β]
    {preRank score tie theta : α → ℝ} {band : α → β}
    {bandTarget : β → ℝ} {e0 : ℝ} {g f : ℝ → ℝ}
    (rankLevel : ℝ → ℕ)
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hband_order :
      ∀ x y, preRank y ≤ preRank x → band y ≤ band x)
    (hf_mono : Monotone f)
    (hbaseline_nonneg : 0 ≤ g e0)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (band x)) (g e0 * f (theta x)))
    (hprevious_bands_below_target :
      ∀ x y, band y < band x → score y ≤ bandTarget (band x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hscore_within_band :
      ∀ x y, band y = band x → preRank y ≤ preRank x →
        score y ≤ score x :=
    finiteBand_within_score_mono_of_source_max_formula
      hf_mono hbaseline_nonneg htheta_mono hscore_formula
  have hscore_between_bands :
      ∀ x y, band y < band x → score y ≤ score x :=
    finiteBand_between_score_mono_of_boundary_targets
      hscore_formula hprevious_bands_below_target
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x := by
    intro x y hpre
    have hband_le : band y ≤ band x := hband_order x y hpre
    rcases lt_or_eq_of_le hband_le with hlt | heq
    · exact hscore_between_bands x y hlt
    · exact hscore_within_band x y heq hpre
  have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
      hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
  exact Filter.Eventually.of_forall (fun x => by
    change rankLevel (tieBrokenRank μ score tie x) = rankLevel (preRank x)
    rw [hrank_eq x])

/--
Displayed finite second-price score equation.  If the actual effort is the
source second-price effort formula, the skill component is `f theta`, and the
realized score is the source max expression
`max {g(tilde_k) f(c_k), g(e0) f(theta)}`, then the multiplicative score
identity `score = g(effort) * skill` is derived rather than supplied as a
separate premise.
-/
theorem secondPrice_fin_score_eq_of_effort_formula_and_source_max_formula
    {α : Type*} {n : ℕ}
    {gInv g f : ℝ → ℝ} {e0 : ℝ}
    {score skill theta effort : α → ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (hg_mono : Monotone g)
    (hInv : Function.RightInverse gInv g)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (hskill_source : ∀ x, skill x = f (theta x))
    (hscore_formula :
      ∀ x, score x =
        max (g (tilde (actualBand x)) * f (cutoff (actualBand x)))
          (g e0 * f (theta x))) :
    ∀ x, score x = g (effort x) * skill x := by
  intro x
  rw [hscore_formula x, heffort_formula x, hskill_source x]
  exact (secondPriceEffort_score_eq_max_of_rightInverse
    hg_mono (hf_theta_pos x) hInv).symm

/--
Finite second-price boundary equations, effort-threshold comparisons, and the
source pre-rank tie key imply almost-everywhere rank preservation.  This is the
most source-shaped finite bridge: deviation costs are not premises but follow
from monotone cost and the boundary-effort thresholds.
-/
theorem secondPrice_fin_rankPreservationAE_of_boundary_effort_thresholds_and_score_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualEffort :
      ∀ x, effort x = tilde (actualBand x))
    (hdeviationEffort :
      ∀ x d, tilde (deviationBand x d) ≤ d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hprevious_bands_below_target :
      ∀ x y, actualBand y < actualBand x →
        score y ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbestAE :
      SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
    secondPrice_fin_sourceRankBestResponseAE_of_boundary_effort_thresholds
      reward tilde actualBand deviationBand
      (hcost_strict.monotoneOn) htilde_feasible htilde hactualLevel
      hdeviationLevel hlevelReward hactualEffort hdeviationEffort
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x := by
    have hscore_within_band :
        ∀ x y, actualBand y = actualBand x → preRank y ≤ preRank x →
          score y ≤ score x :=
      finiteBand_within_score_mono_of_source_max_formula
        hf_mono (hg_nonneg e0) htheta_mono hscore_formula
    have hscore_between_bands :
        ∀ x y, actualBand y < actualBand x → score y ≤ score x :=
      finiteBand_between_score_mono_of_boundary_targets
        hscore_formula hprevious_bands_below_target
    intro x y hpre
    have hband_le : actualBand y ≤ actualBand x :=
      hactualBand_order x y hpre
    rcases lt_or_eq_of_le hband_le with hlt | heq
    · exact hscore_between_bands x y hlt
    · exact hscore_within_band x y heq hpre
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_ae_post_actual
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Finite second-price rank-preservation endpoint with the displayed source
max-score formula.  The previous-band separation condition is derived from
monotone boundary targets and the fact that each baseline score is below its
own band's boundary target.
-/
theorem secondPrice_fin_rankPreservationAE_of_boundary_effort_thresholds_and_source_max_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualEffort :
      ∀ x, effort x = tilde (actualBand x))
    (hdeviationEffort :
      ∀ x d, tilde (deviationBand x d) ≤ d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  exact
    secondPrice_fin_rankPreservationAE_of_boundary_effort_thresholds_and_score_order_tie_eq_preRank
      K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
      levelReward reward tilde actualBand deviationBand bandTarget htilde
      hactualLevel hdeviationLevel hlevelReward hactualEffort
      hdeviationEffort hpre_bound hpost_bound hcost_conv hcost_strict
      hg_conc hg_cont hg_strict hg_nonneg heffort_feasible htilde_feasible
      hskill_pos hskill_eq hrankSkill_strict hpre_level_rank_order
      hscore_level_mono hscore_eq hpost_actual_ae hequal_score_level
      hpreRank_meas hscore_meas htie_meas hrankLevel_meas hpre_dist
      hpre_range hactualBand_order hf_mono htheta_mono
      hscore_formula
      (finiteBand_previous_bands_below_target_of_source_max_formula
        hscore_formula hbandTarget_mono hbaseline_le_bandTarget)
      htie_eq

/--
Finite second-price rank-preservation endpoint with weak actual costs and the
displayed source max-score formula.  This is the most useful bridge for the
within-band second-price effort formula before proving the full continuum
construction: score monotonicity is derived from the source max formula, while
best response uses only `actual cost ≤ boundary cost` and the deviation
boundary-cost lower bound.
-/
theorem secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_actual_le_and_source_max_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)))
    (hdeviationCost :
      ∀ x d, costFn (tilde (deviationBand x d)) ≤ costFn d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  exact
    secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_actual_le_and_score_order_tie_eq_preRank
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward reward tilde actualBand deviationBand htilde hactualLevel
      hdeviationLevel hlevelReward hactualCost_le hdeviationCost hpre_bound
      hpost_bound hcost_conv hcost_strict hg_conc hg_cont hg_strict
      hg_nonneg heffort_feasible hskill_pos hskill_eq hrankSkill_strict
      hpre_level_rank_order hscore_level_mono hscore_eq
      hpost_actual_ae
      hequal_score_level hpreRank_meas hscore_meas htie_meas hrankLevel_meas
      hpre_dist hpre_range
      (by
        have hprevious_bands_below_target :
            ∀ x y, actualBand y < actualBand x →
              score y ≤ bandTarget (actualBand x) :=
          finiteBand_previous_bands_below_target_of_source_max_formula
            hscore_formula hbandTarget_mono hbaseline_le_bandTarget
        have hscore_within_band :
            ∀ x y, actualBand y = actualBand x → preRank y ≤ preRank x →
              score y ≤ score x :=
          finiteBand_within_score_mono_of_source_max_formula
            hf_mono (hg_nonneg e0) htheta_mono hscore_formula
        have hscore_between_bands :
            ∀ x y, actualBand y < actualBand x → score y ≤ score x :=
          finiteBand_between_score_mono_of_boundary_targets
            hscore_formula hprevious_bands_below_target
        intro x y hpre
        have hband_le : actualBand y ≤ actualBand x :=
          hactualBand_order x y hpre
        rcases lt_or_eq_of_le hband_le with hlt | heq
        · exact hscore_between_bands x y hlt
        · exact hscore_within_band x y heq hpre)
      htie_eq

/--
Finite second-price rank-preservation endpoint with direction-aware deviation
checks and the displayed source max-score formula.  This is the finite
source-shaped route that avoids both the over-strong downward boundary-cost
premise and a raw score-monotonicity certificate.
-/
theorem secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_directional_and_source_max_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)))
    (hsameCost :
      ∀ x d, deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d)
    (hupCost :
      ∀ x d, actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d)
    (hdownNoProfit :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (tilde (actualBand x)))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  exact
    secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_directional_and_score_order_tie_eq_preRank
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward reward tilde actualBand deviationBand htilde hactualLevel
      hdeviationLevel hlevelReward hactualCost_le hsameCost hupCost
      hdownNoProfit hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      (Filter.Eventually.of_forall hpost_actual) hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range
      (by
        have hprevious_bands_below_target :
            ∀ x y, actualBand y < actualBand x →
              score y ≤ bandTarget (actualBand x) :=
          finiteBand_previous_bands_below_target_of_source_max_formula
            hscore_formula hbandTarget_mono hbaseline_le_bandTarget
        have hscore_within_band :
            ∀ x y, actualBand y = actualBand x → preRank y ≤ preRank x →
              score y ≤ score x :=
          finiteBand_within_score_mono_of_source_max_formula
            hf_mono (hg_nonneg e0) htheta_mono hscore_formula
        have hscore_between_bands :
            ∀ x y, actualBand y < actualBand x → score y ≤ score x :=
          finiteBand_between_score_mono_of_boundary_targets
            hscore_formula hprevious_bands_below_target
        intro x y hpre
        have hband_le : actualBand y ≤ actualBand x :=
          hactualBand_order x y hpre
        rcases lt_or_eq_of_le hband_le with hlt | heq
        · exact hscore_between_bands x y hlt
        · exact hscore_within_band x y heq hpre)
      htie_eq

/--
Finite second-price rank-preservation endpoint with direction-aware deviation
checks, the source-shaped actual-effort downward comparison, and the displayed
source max-score formula.
-/
theorem secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_directional_actual_down_and_source_max_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)))
    (hsameCost :
      ∀ x d, deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d)
    (hupCost :
      ∀ x d, actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d)
    (hdownNoProfitActual :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  exact
    secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_directional_actual_down_and_score_order_tie_eq_preRank
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward reward tilde actualBand deviationBand htilde hactualLevel
      hdeviationLevel hlevelReward hactualCost_le hsameCost hupCost
      hdownNoProfitActual hpre_bound hpost_bound hcost_conv hcost_strict
      hg_conc hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos
      hskill_eq hrankSkill_strict hpre_level_rank_order hscore_level_mono
      hscore_eq (Filter.Eventually.of_forall hpost_actual) hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range
      (by
        have hprevious_bands_below_target :
            ∀ x y, actualBand y < actualBand x →
              score y ≤ bandTarget (actualBand x) :=
          finiteBand_previous_bands_below_target_of_source_max_formula
            hscore_formula hbandTarget_mono hbaseline_le_bandTarget
        have hscore_within_band :
            ∀ x y, actualBand y = actualBand x → preRank y ≤ preRank x →
              score y ≤ score x :=
          finiteBand_within_score_mono_of_source_max_formula
            hf_mono (hg_nonneg e0) htheta_mono hscore_formula
        have hscore_between_bands :
            ∀ x y, actualBand y < actualBand x → score y ≤ score x :=
          finiteBand_between_score_mono_of_boundary_targets
            hscore_formula hprevious_bands_below_target
        intro x y hpre
        have hband_le : actualBand y ≤ actualBand x :=
          hactualBand_order x y hpre
        rcases lt_or_eq_of_le hband_le with hlt | heq
        · exact hscore_between_bands x y hlt
        · exact hscore_within_band x y heq hpre)
      htie_eq

/--
Finite second-price rank-preservation endpoint for the displayed source
second-price effort formula.  It derives the actual, same-band, and upward
cost inequalities from boundary-reachability facts, keeps the lower-band
no-profit condition explicit, and derives global score order from the source
max-score formula.
-/
theorem secondPrice_fin_rankPreservationAE_of_effort_formula_directional_and_source_max_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdownNoProfit :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (tilde (actualBand x)))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)) :=
    secondPrice_actualCost_le_boundary_of_effort_formula
      tilde cutoff actualBand theta effort hg_strict hInv
      (hcost_strict.monotoneOn) htilde_feasible hf_theta_pos
      hactual_reaches_boundary heffort_formula
  have hsameCost :
      ∀ x d, deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d :=
    secondPrice_sameBandCost_le_of_effort_formula
      tilde cutoff actualBand deviationBand theta effort hg_strict hInv
      (hcost_strict.monotoneOn) hf_theta_pos hdeviation_same_feasible
      hsame_reaches_boundary heffort_formula
  have hupCost :
      ∀ x d, actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d :=
    secondPrice_upwardCost_ge_boundary_of_score_boundary
      tilde cutoff actualBand deviationBand hg_strict
      (hcost_strict.monotoneOn) htilde_feasible hf_cutoff_pos
      hdeviation_up_feasible hup_reaches_boundary
  exact
    secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_directional_and_source_max_order_tie_eq_preRank
      K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
      levelReward reward tilde actualBand deviationBand bandTarget htilde
      hactualLevel hdeviationLevel hlevelReward hactualCost_le hsameCost
      hupCost hdownNoProfit hpre_bound hpost_bound hcost_conv hcost_strict
      hg_conc hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos
      hskill_eq hrankSkill_strict hpre_level_rank_order hscore_level_mono
      hscore_eq hpost_actual hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hactualBand_order
      hf_mono htheta_mono hscore_formula hbandTarget_mono
      hbaseline_le_bandTarget htie_eq

/--
Finite second-price rank-preservation endpoint for the displayed source
second-price effort formula with the source-shaped actual-effort downward
comparison.  Actual, same-band, and upward costs are derived from
boundary-reachability facts; score order is derived from the source max-score
formula.
-/
theorem secondPrice_fin_rankPreservationAE_of_effort_formula_directional_actual_down_and_source_max_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdownNoProfitActual :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hactualCost_le :
      ∀ x, costFn (effort x) ≤ costFn (tilde (actualBand x)) :=
    secondPrice_actualCost_le_boundary_of_effort_formula
      tilde cutoff actualBand theta effort hg_strict hInv
      (hcost_strict.monotoneOn) htilde_feasible hf_theta_pos
      hactual_reaches_boundary heffort_formula
  have hsameCost :
      ∀ x d, deviationBand x d = actualBand x →
        costFn (effort x) ≤ costFn d :=
    secondPrice_sameBandCost_le_of_effort_formula
      tilde cutoff actualBand deviationBand theta effort hg_strict hInv
      (hcost_strict.monotoneOn) hf_theta_pos hdeviation_same_feasible
      hsame_reaches_boundary heffort_formula
  have hupCost :
      ∀ x d, actualBand x < deviationBand x d →
        costFn (tilde (deviationBand x d)) ≤ costFn d :=
    secondPrice_upwardCost_ge_boundary_of_score_boundary
      tilde cutoff actualBand deviationBand hg_strict
      (hcost_strict.monotoneOn) htilde_feasible hf_cutoff_pos
      hdeviation_up_feasible hup_reaches_boundary
  exact
    secondPrice_fin_rankPreservationAE_of_boundary_effort_equations_directional_actual_down_and_source_max_order_tie_eq_preRank
      K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
      levelReward reward tilde actualBand deviationBand bandTarget htilde
      hactualLevel hdeviationLevel hlevelReward hactualCost_le hsameCost
      hupCost hdownNoProfitActual hpre_bound hpost_bound hcost_conv hcost_strict
      hg_conc hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos
      hskill_eq hrankSkill_strict hpre_level_rank_order hscore_level_mono
      hscore_eq hpost_actual hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hactualBand_order
      hf_mono htheta_mono hscore_formula hbandTarget_mono
      hbaseline_le_bandTarget htie_eq

/--
Finite second-price rank-preservation endpoint for the displayed source
second-price effort formula, deriving the lower-band no-profit check from the
convex boundary-gap argument.  This is the source-shaped finite version of the
paper's downward-deviation step: a downward deviation lies to the left of its
lower boundary, the actual effort lies below its own boundary, and the boundary
interval is longer, so convex cost makes the deviation's cost saving no larger
than the lost reward.
-/
theorem secondPrice_fin_rankPreservationAE_of_effort_formula_convex_down_and_source_max_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn gInv g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde cutoff : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (hInv : Function.RightInverse gInv g)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hf_theta_pos : ∀ x, 0 < f (theta x))
    (hf_cutoff_pos : ∀ i : Fin (n + 1), 0 < f (cutoff i))
    (hdeviation_same_feasible :
      ∀ x d, deviationBand x d = actualBand x → e0 ≤ d)
    (hdeviation_up_feasible :
      ∀ x d, actualBand x < deviationBand x d → e0 ≤ d)
    (hactual_reaches_boundary :
      ∀ x, g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
        g (tilde (actualBand x)) * f (theta x))
    (hsame_reaches_boundary :
      ∀ x d, deviationBand x d = actualBand x →
        g (tilde (actualBand x)) * f (cutoff (actualBand x)) ≤
          g d * f (theta x))
    (hup_reaches_boundary :
      ∀ x d, actualBand x < deviationBand x d →
        g (tilde (deviationBand x d)) * f (cutoff (deviationBand x d)) ≤
          g d * f (cutoff (deviationBand x d)))
    (heffort_formula :
      ∀ x, effort x =
        secondPriceEffort e0 gInv g f (tilde (actualBand x))
          (cutoff (actualBand x)) (theta x))
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (effort x)) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdown_deviation_feasible :
      ∀ x d, deviationBand x d < actualBand x → e0 ≤ d)
    (hdown_actual_gt_deviation :
      ∀ x d, deviationBand x d < actualBand x → d < effort x)
    (hdown_interval_len :
      ∀ x d, deviationBand x d < actualBand x →
        effort x - d < tilde (actualBand x) - tilde (deviationBand x d))
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hdown_boundary_gap :
      ∀ x d, deviationBand x d < actualBand x →
        reward (actualBand x) - reward (deviationBand x d) =
          costFn (tilde (actualBand x)) -
            costFn (tilde (deviationBand x d)) := by
    intro x d _hdown
    have hactual := htilde (actualBand x)
    have hdeviation := htilde (deviationBand x d)
    linarith
  have hdown_actual_le_boundary :
      ∀ x d, deviationBand x d < actualBand x →
        effort x ≤ tilde (actualBand x) := by
    intro x d _hdown
    rw [heffort_formula x]
    exact
      secondPriceEffort_le_boundary_of_reaches_boundary_score_of_rightInverse
        hg_strict (hf_theta_pos x) hInv (htilde_feasible (actualBand x))
        (hactual_reaches_boundary x)
  have hdownNoProfitActual :
      ∀ x d, deviationBand x d < actualBand x →
        reward (deviationBand x d) - costFn d ≤
          reward (actualBand x) - costFn (effort x) := by
    intro x d hdown
    exact
      secondPrice_downward_no_profit_of_convex_boundary_gap
        hcost_conv hcost_strict
        (hdown_deviation_feasible x d hdown)
        (htilde_feasible (deviationBand x d))
        (hdown_actual_gt_deviation x d hdown)
        (hdown_actual_le_boundary x d hdown)
        (hdown_interval_len x d hdown)
        (hdown_boundary_gap x d hdown)
  exact
    secondPrice_fin_rankPreservationAE_of_effort_formula_directional_actual_down_and_source_max_order_tie_eq_preRank
      K preRank rankOfEffort rankLevel rankSkill skill score tie theta effort
      levelReward reward tilde cutoff actualBand deviationBand bandTarget hInv
      htilde_feasible hf_theta_pos hf_cutoff_pos hdeviation_same_feasible
      hdeviation_up_feasible hactual_reaches_boundary hsame_reaches_boundary
      hup_reaches_boundary heffort_formula htilde hactualLevel hdeviationLevel
      hlevelReward hdownNoProfitActual hpre_bound hpost_bound hcost_conv
      hcost_strict hg_conc hg_cont hg_strict hg_nonneg heffort_feasible
      hskill_pos hskill_eq hrankSkill_strict hpre_level_rank_order
      hscore_level_mono hscore_eq hpost_actual hequal_score_level
      hpreRank_meas hscore_meas htie_meas hrankLevel_meas hpre_dist
      hpre_range hactualBand_order hf_mono htheta_mono hscore_formula
      hbandTarget_mono hbaseline_le_bandTarget htie_eq

/--
Finite second-price rank-preservation endpoint where the actual effort profile
is the boundary-effort function itself.  This removes the separate
`effort = tilde actualBand` and actual-effort-feasibility premises from the
source-facing theorem surface.
-/
theorem secondPrice_fin_rankPreservationAE_of_boundary_effort_function_and_source_max_order_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {n : ℕ}
    {costFn g f : ℝ → ℝ} {e0 : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta : α → ℝ) (levelReward : ℕ → ℝ)
    (reward : Fin (n + 1) → ℝ) {baseCost : ℝ}
    (tilde : Fin (n + 1) → ℝ)
    (actualBand : α → Fin (n + 1))
    (deviationBand : α → ℝ → Fin (n + 1))
    (bandTarget : Fin (n + 1) → ℝ)
    (htilde :
      ∀ i : Fin (n + 1),
        costFn (tilde i) =
          baseCost + (reward i - reward ⟨0, Nat.succ_pos n⟩))
    (hactualLevel :
      ∀ x,
        rankLevel (rankOfEffort x (tilde (actualBand x))) = (actualBand x).val)
    (hdeviationLevel :
      ∀ x d,
        rankLevel (rankOfEffort x d) = (deviationBand x d).val)
    (hlevelReward :
      ∀ i : Fin (n + 1), levelReward i.val = reward i)
    (hdeviationEffort :
      ∀ x d, tilde (deviationBand x d) ≤ d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (htilde_feasible : ∀ i : Fin (n + 1), e0 ≤ tilde i)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (tilde (actualBand x)) * skill x)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (tilde (actualBand x))) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hactualBand_order :
      ∀ x y, preRank y ≤ preRank x → actualBand y ≤ actualBand x)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x, score x = max (bandTarget (actualBand x)) (g e0 * f (theta x)))
    (hbandTarget_mono : Monotone bandTarget)
    (hbaseline_le_bandTarget :
      ∀ x, g e0 * f (theta x) ≤ bandTarget (actualBand x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  exact
    secondPrice_fin_rankPreservationAE_of_boundary_effort_thresholds_and_source_max_order_tie_eq_preRank
      K preRank rankOfEffort rankLevel rankSkill skill score tie theta
      (fun x => tilde (actualBand x)) levelReward reward tilde actualBand
      deviationBand bandTarget htilde hactualLevel hdeviationLevel
      hlevelReward (fun _ => rfl) hdeviationEffort hpre_bound hpost_bound
      hcost_conv hcost_strict hg_conc hg_cont hg_strict hg_nonneg
      (fun x => htilde_feasible (actualBand x)) htilde_feasible hskill_pos
      hskill_eq hrankSkill_strict hpre_level_rank_order hscore_level_mono
      hscore_eq (Filter.Eventually.of_forall hpost_actual) hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hactualBand_order
      hf_mono htheta_mono hscore_formula hbandTarget_mono
      hbaseline_le_bandTarget htie_eq

/--
Two-level second-price source model plus dense gamma construction imply
almost-everywhere rank preservation.  This combines the concrete two-level
best-response proof with the source-shaped PIT endpoint: no positive
score/tie mass gaps and dense realized tie-broken ranks.
-/
theorem secondPrice_twoLevel_rankPreservationAE_of_score_boundaries_and_gamma_dense
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {costFn gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hInv : Function.RightInverse gInv g)
    (hbase_min : ∀ d, costFn e0 ≤ costFn d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      costFn tilde = costFn e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_low : ∀ x, ¬ actualHigh x → effort x = e0)
    (heffort_high :
      ∀ x, actualHigh x →
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x))
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hbelow :
      ∀ t ε, 0 < t → t ≤ 1 → 0 < ε →
        ∃ x, t - ε ≤ tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x ≤ t)
    (habove :
      ∀ t ε, 0 ≤ t → t < 1 → 0 < ε →
        ∃ x, t ≤ tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x ≤ t + ε)
    (hgap :
      ∀ {x z},
        (score x < score z ∨ score x = score z ∧ tie x < tie z) →
          μ (tieBrokenLowerContour score tie z ∩
            (tieBrokenLowerContour score tie x)ᶜ) ≠ 0) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
    secondPrice_twoLevel_sourceRankBestResponse_of_score_boundaries
      hg_strict hInv (hcost_strict.monotoneOn) hbase_min htilde_feasible
      htilde_cost hlevel_zero hlevel_one hactual_reaches hlevel
      heffort_low heffort_high hf_cutoff_pos hf_low_le_cutoff hf_high_pos
      hboundary_reaches_high (fun _ d _ => hg_nonneg d) hreaches_boundary
      hdeviation_feasible
  have hbestAE :
      SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
    sourceRankBestResponseAE_of_sourceRankBestResponse hbest
  have heffort_feasible : ∀ x, e0 ≤ effort x := by
    intro x
    by_cases hx : actualHigh x
    · rw [heffort_high x hx]
      exact secondPriceEffort_ge_e0 e0 gInv g f tilde c (theta x)
    · rw [heffort_low x hx]
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_lex_gap_dense
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hbelow habove hgap

/--
Two-level second-price source model plus the open-interval-density gamma
construction imply almost-everywhere rank preservation.  This is the
source-shaped version of the dense endpoint: every open rank interval contains
a realized tie-broken rank.
-/
theorem secondPrice_twoLevel_rankPreservationAE_of_score_boundaries_and_gamma_interval_dense
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {costFn gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hInv : Function.RightInverse gInv g)
    (hbase_min : ∀ d, costFn e0 ≤ costFn d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      costFn tilde = costFn e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_low : ∀ x, ¬ actualHigh x → effort x = e0)
    (heffort_high :
      ∀ x, actualHigh x →
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x))
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hdense :
      ∀ a b, 0 ≤ a → a < b → b ≤ 1 →
        ∃ x, a < tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x < b)
    (hgap :
      ∀ {x z},
        (score x < score z ∨ score x = score z ∧ tie x < tie z) →
          μ (tieBrokenLowerContour score tie z ∩
            (tieBrokenLowerContour score tie x)ᶜ) ≠ 0) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
    secondPrice_twoLevel_sourceRankBestResponse_of_score_boundaries
      hg_strict hInv (hcost_strict.monotoneOn) hbase_min htilde_feasible
      htilde_cost hlevel_zero hlevel_one hactual_reaches hlevel
      heffort_low heffort_high hf_cutoff_pos hf_low_le_cutoff hf_high_pos
      hboundary_reaches_high (fun _ d _ => hg_nonneg d) hreaches_boundary
      hdeviation_feasible
  have hbestAE :
      SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
    sourceRankBestResponseAE_of_sourceRankBestResponse hbest
  have heffort_feasible : ∀ x, e0 ≤ effort x := by
    intro x
    by_cases hx : actualHigh x
    · rw [heffort_high x hx]
      exact secondPriceEffort_ge_e0 e0 gInv g f tilde c (theta x)
    · rw [heffort_low x hx]
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_lex_gap_interval_dense
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hdense hgap

/--
Two-level second-price source model plus open-interval-density gamma, using
the source-shaped reward-reachability route instead of a global equal-score
deviation-rank certificate.  The extra two-level premise says that if a
deviation reaches the score of an actually high applicant, then it reaches the
high band.
-/
theorem secondPrice_twoLevel_rankPreservationAE_of_score_boundaries_and_gamma_interval_dense_reward_reach
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {costFn gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hInv : Function.RightInverse gInv g)
    (hbase_min : ∀ d, costFn e0 ≤ costFn d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      costFn tilde = costFn e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hlow_le_high : lowReward ≤ highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_low : ∀ x, ¬ actualHigh x → effort x = e0)
    (heffort_high :
      ∀ x, actualHigh x →
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x))
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
    (hscore_reaches_high :
      ∀ x y d, actualHigh y → score y ≤ g d * skill x →
        reachesHigh x d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hdense :
      ∀ a b, 0 ≤ a → a < b → b ≤ 1 →
        ∃ x, a < tieBrokenRank μ score tie x ∧
          tieBrokenRank μ score tie x < b)
    (hgap :
      ∀ {x z},
        (score x < score z ∨ score x = score z ∧ tie x < tie z) →
          μ (tieBrokenLowerContour score tie z ∩
            (tieBrokenLowerContour score tie x)ᶜ) ≠ 0) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
    secondPrice_twoLevel_sourceRankBestResponse_of_score_boundaries
      hg_strict hInv (hcost_strict.monotoneOn) hbase_min htilde_feasible
      htilde_cost hlevel_zero hlevel_one hactual_reaches hlevel
      heffort_low heffort_high hf_cutoff_pos hf_low_le_cutoff hf_high_pos
      hboundary_reaches_high (fun _ d _ => hg_nonneg d) hreaches_boundary
      hdeviation_feasible
  have heffort_feasible : ∀ x, e0 ≤ effort x := by
    intro x
    by_cases hx : actualHigh x
    · rw [heffort_high x hx]
      exact secondPriceEffort_ge_e0 e0 gInv g f tilde c (theta x)
    · rw [heffort_low x hx]
  have hdeviation_reaches_reward :
      ∀ x y d, score y ≤ g d * skill x →
        levelReward (rankLevel (tieBrokenRank μ score tie y)) ≤
          levelReward (rankLevel (rankOfEffort x d)) :=
    secondPrice_twoLevel_deviation_reward_reach_of_score_reaches_high
      hlevel_zero hlevel_one hlow_le_high hactual_reaches hlevel
      hpost_actual hscore_reaches_high
  have hgamma_scalar :
      ∀ t, 0 ≤ t → t ≤ 1 →
        μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
    tieBrokenRank_scalar_cdf_of_lex_gap_and_interval_dense
      hscore_meas htie_meas hdense hgap
  exact
    rank_preservation_ae_eq_of_source_equilibrium_tieBrokenRank_scalar_cdf_reward_reach
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbest hpost_actual hdeviation_reaches_reward hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hgamma_scalar

/--
Two-level second-price source model plus the displayed source score formula
and source pre-rank tie key imply almost-everywhere rank preservation.  This
route derives the gamma scalar CDF from monotone score order and `tie = preRank`
instead of using separate dense/no-gap atom-filling premises.
-/
theorem secondPrice_twoLevel_rankPreservationAE_of_score_boundaries_and_source_rank_formula
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {costFn gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hInv : Function.RightInverse gInv g)
    (hbase_min : ∀ d, costFn e0 ≤ costFn d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      costFn tilde = costFn e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_low : ∀ x, ¬ actualHigh x → effort x = e0)
    (heffort_high :
      ∀ x, actualHigh x →
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x))
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x,
        score x =
          g (secondPriceEffort e0 gInv g f tilde c (theta x))
            * f (theta x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
    secondPrice_twoLevel_sourceRankBestResponse_of_score_boundaries
      hg_strict hInv (hcost_strict.monotoneOn) hbase_min htilde_feasible
      htilde_cost hlevel_zero hlevel_one hactual_reaches hlevel
      heffort_low heffort_high hf_cutoff_pos hf_low_le_cutoff hf_high_pos
      hboundary_reaches_high (fun _ d _ => hg_nonneg d) hreaches_boundary
      hdeviation_feasible
  have hbestAE :
      SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
    sourceRankBestResponseAE_of_sourceRankBestResponse hbest
  have heffort_feasible : ∀ x, e0 ≤ effort x := by
    intro x
    by_cases hx : actualHigh x
    · rw [heffort_high x hx]
      exact secondPriceEffort_ge_e0 e0 gInv g f tilde c (theta x)
    · rw [heffort_low x hx]
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x :=
    secondPriceEffort_score_mono_of_type_mono
      hg_strict.monotone hf_pos hf_mono (hg_nonneg e0) hInv
      htheta_mono hscore_formula
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Two-level second-price source-rank-formula endpoint using reward reachability
instead of a global equal-score deviation-rank certificate.  The gamma scalar
CDF is still derived internally from source score monotonicity and
`tie = preRank`.
-/
theorem secondPrice_twoLevel_rankPreservationAE_of_score_boundaries_and_source_rank_formula_reward_reach
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {costFn gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hInv : Function.RightInverse gInv g)
    (hbase_min : ∀ d, costFn e0 ≤ costFn d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      costFn tilde = costFn e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hlow_le_high : lowReward ≤ highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_low : ∀ x, ¬ actualHigh x → effort x = e0)
    (heffort_high :
      ∀ x, actualHigh x →
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x))
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
    (hscore_reaches_high :
      ∀ x y d, actualHigh y → score y ≤ g d * skill x →
        reachesHigh x d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hscore_eq : ∀ x, score x = g (effort x) * skill x)
    (hpost_actual :
      ∀ x, rankLevel (rankOfEffort x (effort x)) =
        rankLevel (tieBrokenRank μ score tie x))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x,
        score x =
          g (secondPriceEffort e0 gInv g f tilde c (theta x))
            * f (theta x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
    secondPrice_twoLevel_sourceRankBestResponse_of_score_boundaries
      hg_strict hInv (hcost_strict.monotoneOn) hbase_min htilde_feasible
      htilde_cost hlevel_zero hlevel_one hactual_reaches hlevel
      heffort_low heffort_high hf_cutoff_pos hf_low_le_cutoff hf_high_pos
      hboundary_reaches_high (fun _ d _ => hg_nonneg d) hreaches_boundary
      hdeviation_feasible
  have heffort_feasible : ∀ x, e0 ≤ effort x := by
    intro x
    by_cases hx : actualHigh x
    · rw [heffort_high x hx]
      exact secondPriceEffort_ge_e0 e0 gInv g f tilde c (theta x)
    · rw [heffort_low x hx]
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x :=
    secondPriceEffort_score_mono_of_type_mono
      hg_strict.monotone hf_pos hf_mono (hg_nonneg e0) hInv
      htheta_mono hscore_formula
  have hdeviation_reaches_reward :
      ∀ x y d, score y ≤ g d * skill x →
        levelReward (rankLevel (tieBrokenRank μ score tie y)) ≤
          levelReward (rankLevel (rankOfEffort x d)) :=
    secondPrice_twoLevel_deviation_reward_reach_of_score_reaches_high
      hlevel_zero hlevel_one hlow_le_high hactual_reaches hlevel
      hpost_actual hscore_reaches_high
  have hgamma_scalar :
      ∀ t, 0 ≤ t → t ≤ 1 →
        μ {x | tieBrokenRank μ score tie x ≤ t} = ENNReal.ofReal t :=
    tieBrokenRank_scalar_cdf_of_score_mono_and_tie_eq_preRank
      hpreRank_meas hscore_meas htie_meas hpre_dist hpre_range
      hscore_mono htie_eq
  exact
    rank_preservation_ae_eq_of_source_equilibrium_tieBrokenRank_scalar_cdf_reward_reach
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbest hpost_actual hdeviation_reaches_reward hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hgamma_scalar

/--
Two-level second-price source model with the source's piecewise score formula:
low-band applicants use baseline effort, high-band applicants use the
displayed second-price effort, and the high band is upward closed in source
rank.  This endpoint derives both score monotonicity and the multiplicative
score equation internally, avoiding a uniform score-formula premise.
-/
theorem secondPrice_twoLevel_rankPreservationAE_of_score_boundaries_and_piecewise_source_formula
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {costFn gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hInv : Function.RightInverse gInv g)
    (hbase_min : ∀ d, costFn e0 ≤ costFn d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      costFn tilde = costFn e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_low : ∀ x, ¬ actualHigh x → effort x = e0)
    (heffort_high :
      ∀ x, actualHigh x →
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x))
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hskill_source : ∀ x, skill x = f (theta x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hequal_score_level :
      ∀ x y dx dy,
        g dx * skill x = g dy * skill y →
          rankLevel (rankOfEffort x dx) =
            rankLevel (rankOfEffort y dy))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hactualHigh_upper :
      ∀ x y, preRank y ≤ preRank x → actualHigh y → actualHigh x)
    (hscore_low :
      ∀ x, ¬ actualHigh x → score x = g e0 * f (theta x))
    (hscore_high :
      ∀ x, actualHigh x →
        score x =
          g (secondPriceEffort e0 gInv g f tilde c (theta x))
            * f (theta x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
    secondPrice_twoLevel_sourceRankBestResponse_of_score_boundaries
      hg_strict hInv (hcost_strict.monotoneOn) hbase_min htilde_feasible
      htilde_cost hlevel_zero hlevel_one hactual_reaches hlevel
      heffort_low heffort_high hf_cutoff_pos hf_low_le_cutoff hf_high_pos
      hboundary_reaches_high (fun _ d _ => hg_nonneg d) hreaches_boundary
      hdeviation_feasible
  have hbestAE :
      SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
    sourceRankBestResponseAE_of_sourceRankBestResponse hbest
  have heffort_feasible : ∀ x, e0 ≤ effort x := by
    intro x
    by_cases hx : actualHigh x
    · rw [heffort_high x hx]
      exact secondPriceEffort_ge_e0 e0 gInv g f tilde c (theta x)
    · rw [heffort_low x hx]
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x :=
    secondPriceEffort_piecewise_score_mono_of_type_mono
      hg_strict.monotone hf_pos hf_mono (hg_nonneg e0) hInv
      htheta_mono hactualHigh_upper hscore_low hscore_high
  have hscore_eq :
      ∀ x, score x = g (effort x) * skill x := by
    intro x
    by_cases hx : actualHigh x
    · rw [hscore_high x hx, heffort_high x hx, hskill_source x]
    · rw [hscore_low x hx, heffort_low x hx, hskill_source x]
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_ae_post_actual
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hequal_score_level hpreRank_meas hscore_meas
      htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono htie_eq

/--
Two-level second-price source model with the source's piecewise score formula,
using reward reachability instead of a global equal-score deviation-rank
certificate.  The reachability premise is local to the displayed low/high
source model and the realized post-rank relation may hold only a.e.
-/
theorem secondPrice_twoLevel_rankPreservationAE_of_score_boundaries_and_piecewise_source_formula_reward_reach
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {costFn gInv g f : ℝ → ℝ} {e0 lowReward highReward tilde c : ℝ}
    (K : ℕ) (preRank : α → ℝ) (rankOfEffort : α → ℝ → ℝ)
    (rankLevel : ℝ → ℕ) (rankSkill : ℝ → ℝ)
    (skill score tie theta effort : α → ℝ) (levelReward : ℕ → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hInv : Function.RightInverse gInv g)
    (hbase_min : ∀ d, costFn e0 ≤ costFn d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      costFn tilde = costFn e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hlow_le_high : lowReward ≤ highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_low : ∀ x, ¬ actualHigh x → effort x = e0)
    (heffort_high :
      ∀ x, actualHigh x →
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x))
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d)
    (hscore_reaches_high :
      ∀ x y d, actualHigh y → score y ≤ g d * skill x →
        reachesHigh x d)
    (hpre_bound : ∀ x, rankLevel (preRank x) < K)
    (hpost_bound :
      ∀ x, rankLevel (tieBrokenRank μ score tie x) < K)
    (hcost_conv : ConvexOn ℝ (Set.Ici e0) costFn)
    (hcost_strict : StrictMonoOn costFn (Set.Ici e0))
    (hg_conc : ConcaveOn ℝ Set.univ g)
    (hg_cont : Continuous g)
    (hg_strict : StrictMono g)
    (hg_nonneg : ∀ z, 0 ≤ g z)
    (hskill_pos : ∀ x, 0 < skill x)
    (hskill_eq : ∀ x, skill x = rankSkill (preRank x))
    (hskill_source : ∀ x, skill x = f (theta x))
    (hrankSkill_strict : StrictMono rankSkill)
    (hpre_level_rank_order :
      ∀ x y, rankLevel (preRank y) < rankLevel (preRank x) →
        preRank y < preRank x)
    (hscore_level_mono :
      ∀ x y, score y ≤ score x →
        rankLevel (tieBrokenRank μ score tie y) ≤
          rankLevel (tieBrokenRank μ score tie x))
    (hpost_actual_ae :
      ∀ᵐ x ∂μ,
        rankLevel (rankOfEffort x (effort x)) =
          rankLevel (tieBrokenRank μ score tie x))
    (hpreRank_meas : Measurable preRank)
    (hscore_meas : Measurable score)
    (htie_meas : Measurable tie)
    (hrankLevel_meas : Measurable rankLevel)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hactualHigh_upper :
      ∀ x y, preRank y ≤ preRank x → actualHigh y → actualHigh x)
    (hscore_low :
      ∀ x, ¬ actualHigh x → score x = g e0 * f (theta x))
    (hscore_high :
      ∀ x, actualHigh x →
        score x =
          g (secondPriceEffort e0 gInv g f tilde c (theta x))
            * f (theta x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hbest :
      SourceRankBestResponse costFn rankOfEffort rankLevel levelReward effort :=
    secondPrice_twoLevel_sourceRankBestResponse_of_score_boundaries
      hg_strict hInv (hcost_strict.monotoneOn) hbase_min htilde_feasible
      htilde_cost hlevel_zero hlevel_one hactual_reaches hlevel
      heffort_low heffort_high hf_cutoff_pos hf_low_le_cutoff hf_high_pos
      hboundary_reaches_high (fun _ d _ => hg_nonneg d) hreaches_boundary
      hdeviation_feasible
  have hbestAE :
      SourceRankBestResponseAE μ costFn rankOfEffort rankLevel levelReward effort :=
    sourceRankBestResponseAE_of_sourceRankBestResponse hbest
  have heffort_feasible : ∀ x, e0 ≤ effort x := by
    intro x
    by_cases hx : actualHigh x
    · rw [heffort_high x hx]
      exact secondPriceEffort_ge_e0 e0 gInv g f tilde c (theta x)
    · rw [heffort_low x hx]
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x :=
    secondPriceEffort_piecewise_score_mono_of_type_mono
      hg_strict.monotone hf_pos hf_mono (hg_nonneg e0) hInv
      htheta_mono hactualHigh_upper hscore_low hscore_high
  have hscore_eq :
      ∀ x, score x = g (effort x) * skill x := by
    intro x
    by_cases hx : actualHigh x
    · rw [hscore_high x hx, heffort_high x hx, hskill_source x]
    · rw [hscore_low x hx, heffort_low x hx, hskill_source x]
  have hdeviation_reaches_reward :
      ∀ x y d,
        rankLevel (rankOfEffort y (effort y)) =
          rankLevel (tieBrokenRank μ score tie y) →
        score y ≤ g d * skill x →
          levelReward (rankLevel (tieBrokenRank μ score tie y)) ≤
            levelReward (rankLevel (rankOfEffort x d)) := by
    intro x y d hpost_y hscore_le
    exact
      secondPrice_twoLevel_deviation_reward_reach_of_score_reaches_high_at
        hlevel_zero hlevel_one hlow_le_high hactual_reaches hlevel
        hscore_reaches_high hpost_y hscore_le
  exact
    rank_preservation_ae_eq_of_source_equilibriumAE_tieBrokenRank_score_mono_tie_eq_preRank_local_post_actual_reward_reach
      K preRank rankOfEffort rankLevel rankSkill skill score tie effort
      levelReward hpre_bound hpost_bound hcost_conv hcost_strict hg_conc
      hg_cont hg_strict hg_nonneg heffort_feasible hskill_pos hskill_eq
      hrankSkill_strict hpre_level_rank_order hscore_level_mono hscore_eq
      hbestAE hpost_actual_ae hdeviation_reaches_reward hpreRank_meas
      hscore_meas htie_meas hrankLevel_meas hpre_dist hpre_range hscore_mono
      htie_eq

/--
Two-level source-formula rank preservation without an incentive wrapper.  The
paper's source-tie convention and the displayed low/high second-price score
formulas make the post-effort score monotone in the source rank, so the
tie-broken rank equals the source pre-rank pointwise.
-/
theorem secondPrice_twoLevel_rankPreservationAE_of_piecewise_source_formula_and_tie_eq_preRank
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ]
    {gInv g f : ℝ → ℝ} {e0 tilde c : ℝ}
    (rankLevel : ℝ → ℕ) (preRank score tie theta : α → ℝ)
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    (hpreRank_meas : Measurable preRank)
    (hpre_dist :
      Measure.map preRank μ = volume.restrict (Set.Icc (0 : ℝ) 1))
    (hpre_range : ∀ x, preRank x ∈ Set.Icc (0 : ℝ) 1)
    (hg_mono : Monotone g)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (hbaseline_nonneg : 0 ≤ g e0)
    (hInv : Function.RightInverse gInv g)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hactualHigh_upper :
      ∀ x y, preRank y ≤ preRank x → actualHigh y → actualHigh x)
    (hscore_low :
      ∀ x, ¬ actualHigh x → score x = g e0 * f (theta x))
    (hscore_high :
      ∀ x, actualHigh x →
        score x =
          g (secondPriceEffort e0 gInv g f tilde c (theta x))
            * f (theta x))
    (htie_eq : ∀ x, tie x = preRank x) :
    (fun x => rankLevel (tieBrokenRank μ score tie x)) =ᵐ[μ]
      (fun x => rankLevel (preRank x)) := by
  have hscore_mono :
      ∀ x y, preRank y ≤ preRank x → score y ≤ score x :=
    secondPriceEffort_piecewise_score_mono_of_type_mono
      hg_mono hf_pos hf_mono hbaseline_nonneg hInv htheta_mono
      hactualHigh_upper hscore_low hscore_high
  have hrank_eq : ∀ x, tieBrokenRank μ score tie x = preRank x :=
    tieBrokenRank_eq_preRank_of_score_mono_and_tie_eq_preRank
      hpreRank_meas hpre_dist hpre_range hscore_mono htie_eq
  exact Filter.Eventually.of_forall (fun x => by
    change rankLevel (tieBrokenRank μ score tie x) = rankLevel (preRank x)
    rw [hrank_eq x])

/--
Two-sided all-pairs finite-chain no-profit wrapper: if adjacent upward and
downward no-profit inequalities both hold, then every pair of bands is
ordered by the corresponding no-profit inequality in the direction of the
deviation.
-/
theorem secondPrice_fin_two_sided_no_profit_between
    {n : ℕ} (reward cost : Fin (n + 1) → ℝ)
    (hadjUp :
      ∀ k : Fin n,
        reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
            - cost ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
          ≤ reward ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
            - cost ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩)
    (hadjDown :
      ∀ k : Fin n,
        reward ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
            - cost ⟨k.val, Nat.lt_trans k.isLt (Nat.lt_succ_self n)⟩
          ≤ reward ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
            - cost ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩) :
    (∀ {i j : Fin (n + 1)}, i ≤ j →
      reward j - cost j ≤ reward i - cost i)
    ∧ (∀ {i j : Fin (n + 1)}, i ≤ j →
      reward i - cost i ≤ reward j - cost j) :=
  ⟨fun hij => secondPrice_fin_chain_no_profit_of_adjacent_between
      reward cost hadjUp hij,
    fun hij => secondPrice_fin_reverse_chain_no_profit_of_adjacent_between
      reward cost hadjDown hij⟩

/--
Boundary efforts are monotone over any ordered band index when the reward gaps
and boundary cost equations are monotone over that index.
-/
theorem secondPrice_orderedBand_boundaryEffort_mono_of_rewardGap_mono
    {β : Type*} [Preorder β]
    {e0 baseCost : ℝ} {gap tilde : β → ℝ} {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (htilde_mem : ∀ k, e0 ≤ tilde k)
    (hcost : ∀ k, cost (tilde k) = baseCost + gap k)
    (hgap_mono : Monotone gap) :
    Monotone tilde := by
  intro low high hle
  exact secondPrice_boundaryEffort_mono_of_rewardGap_mono
    hcost_strict (htilde_mem low) (htilde_mem high)
    (hcost low) (hcost high) (hgap_mono hle)

/--
If a source reward-gap parameter is unchanged at two ordered-band indices,
the corresponding boundary efforts are equal.
-/
theorem secondPrice_orderedBand_boundaryEffort_eq_of_rewardGap_eq
    {β : Type*}
    {e0 baseCost : ℝ} {gap tilde : β → ℝ} {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (htilde_mem : ∀ k, e0 ≤ tilde k)
    (hcost : ∀ k, cost (tilde k) = baseCost + gap k)
    {low high : β}
    (hgap : gap low = gap high) :
    tilde low = tilde high :=
  secondPrice_boundaryEffort_eq_of_rewardGap_eq
    hcost_strict (htilde_mem low) (htilde_mem high)
    (hcost low) (hcost high) hgap

/--
Strictly increasing reward gaps produce strictly increasing boundary efforts
over an ordered band index, under the same explicit boundary equations.
-/
theorem secondPrice_orderedBand_boundaryEffort_strictMono_of_rewardGap_strictMono
    {β : Type*} [Preorder β]
    {e0 baseCost : ℝ} {gap tilde : β → ℝ} {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (htilde_mem : ∀ k, e0 ≤ tilde k)
    (hcost : ∀ k, cost (tilde k) = baseCost + gap k)
    (hgap_strict : StrictMono gap) :
    StrictMono tilde := by
  intro low high hlt
  exact secondPrice_boundaryEffort_strictMono_of_rewardGap_strictMono
    hcost_strict (htilde_mem low) (htilde_mem high)
    (hcost low) (hcost high) (hgap_strict hlt)

/--
Pointwise all-band comparative statics for the source boundary equation.  When
two policies share the same cost function and baseline cost, the boundary
effort at each band moves in the same direction as that band's reward-gap
target.
-/
theorem secondPrice_allBand_boundaryEffort_comparative_statics_of_gap_order
    {β : Type*}
    {e0 baseCost : ℝ} {gapOld gapNew tildeOld tildeNew : β → ℝ}
    {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (htildeOld_mem : ∀ k, e0 ≤ tildeOld k)
    (htildeNew_mem : ∀ k, e0 ≤ tildeNew k)
    (hcostOld : ∀ k, cost (tildeOld k) = baseCost + gapOld k)
    (hcostNew : ∀ k, cost (tildeNew k) = baseCost + gapNew k) :
    (∀ k, gapOld k ≤ gapNew k → tildeOld k ≤ tildeNew k)
    ∧ (∀ k, gapOld k = gapNew k → tildeOld k = tildeNew k)
    ∧ (∀ k, gapNew k ≤ gapOld k → tildeNew k ≤ tildeOld k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hgap
    exact secondPrice_boundaryEffort_mono_of_rewardGap_mono
      hcost_strict (htildeOld_mem k) (htildeNew_mem k)
      (hcostOld k) (hcostNew k) hgap
  · intro k hgap
    exact secondPrice_boundaryEffort_eq_of_rewardGap_eq
      hcost_strict (htildeOld_mem k) (htildeNew_mem k)
      (hcostOld k) (hcostNew k) hgap
  · intro k hgap
    exact secondPrice_boundaryEffort_mono_of_rewardGap_mono
      hcost_strict (htildeNew_mem k) (htildeOld_mem k)
      (hcostNew k) (hcostOld k) hgap

/--
Strict pointwise version of the all-band comparative-statics bridge: if a
band's reward-gap target strictly increases under the same source boundary
equation, then that band's boundary effort strictly increases.
-/
theorem secondPrice_allBand_boundaryEffort_strict_of_gap_strict
    {β : Type*}
    {e0 baseCost : ℝ} {gapOld gapNew tildeOld tildeNew : β → ℝ}
    {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (htildeOld_mem : ∀ k, e0 ≤ tildeOld k)
    (htildeNew_mem : ∀ k, e0 ≤ tildeNew k)
    (hcostOld : ∀ k, cost (tildeOld k) = baseCost + gapOld k)
    (hcostNew : ∀ k, cost (tildeNew k) = baseCost + gapNew k) :
    ∀ k, gapOld k < gapNew k → tildeOld k < tildeNew k := by
  intro k hgap
  exact secondPrice_boundaryEffort_strictMono_of_rewardGap_strictMono
    hcost_strict (htildeOld_mem k) (htildeNew_mem k)
    (hcostOld k) (hcostNew k) hgap

end LBG22StrategicRanking
