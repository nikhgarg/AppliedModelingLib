import LBG22StrategicRanking.RankBoundaryRepairs
import LBG22StrategicRanking.SecondPriceFinite
import Mathlib.Order.Interval.Set.Monotone

/-!
# Finite-level equilibrium from effort primitives

The boundary score of each reward band is constructed from the preceding
band's effort at the next cutoff and the adjacent reward increment. All
inverse, cost, and production comparisons are restricted to feasible effort
and score intervals. Positive baseline production is retained by clipping
the inverse input at its actual lower endpoint.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- Minimal effort for a target production level, with the source baseline
floor and the inverse constructed on the actual feasible effort interval. -/
noncomputable def sourceEffortAtScore (production : ℝ → ℝ) (effortMax z : ℝ) : ℝ :=
  effortIntervalInverse production effortMax (max z (production 0))

/-- Actual effort cost of reaching a production target, including targets
already attainable at zero effort. -/
noncomputable def sourceCostAtScore (cost production : ℝ → ℝ) (effortMax z : ℝ) : ℝ :=
  cost (sourceEffortAtScore production effortMax z)

theorem sourceEffortAtScore_spec {production : ℝ → ℝ} {effortMax z : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : MonotoneOn production (Icc 0 effortMax)) (hz : z ≤ production effortMax) :
    sourceEffortAtScore production effortMax z ∈ Icc (0 : ℝ) effortMax ∧
      production (sourceEffortAtScore production effortMax z) = max z (production 0) :=
  effortIntervalInverse_spec hmax hg
    ⟨le_max_right _ _, max_le hz (hg_mono ⟨le_rfl, hmax⟩ ⟨hmax, le_rfl⟩ hmax)⟩

theorem sourceEffortAtScore_at_production {production : ℝ → ℝ} {effortMax e : ℝ}
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (he : e ∈ Icc (0 : ℝ) effortMax) :
    sourceEffortAtScore production effortMax (production e) = e := by
  unfold sourceEffortAtScore
  rw [max_eq_left (hg_mono.monotoneOn ⟨le_rfl, he.1.trans he.2⟩ he he.1)]
  exact hg_mono.injOn.leftInvOn_invFunOn he

theorem sourceEffortAtScore_zero {production : ℝ → ℝ} {effortMax : ℝ}
    (hmax : 0 ≤ effortMax) (hg_mono : StrictMonoOn production (Icc 0 effortMax))
    (hg_zero : 0 ≤ production 0) : sourceEffortAtScore production effortMax 0 = 0 := by
  change effortIntervalInverse production effortMax (max 0 (production 0)) = 0
  rw [max_eq_right hg_zero]
  exact hg_mono.injOn.leftInvOn_invFunOn ⟨le_rfl, hmax⟩

theorem sourceEffortAtScore_monotoneOn {production : ℝ → ℝ} {effortMax : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) :
    MonotoneOn (sourceEffortAtScore production effortMax) (Iic (production effortMax)) := by
  intro a ha b hb hab
  have hia := sourceEffortAtScore_spec hmax hg hg_mono.monotoneOn ha
  have hib := sourceEffortAtScore_spec hmax hg hg_mono.monotoneOn hb
  exact (hg_mono.le_iff_le hia.1 hib.1).mp
    (by rw [hia.2, hib.2]; exact max_le_max_right _ hab)

/-- Minimal effort is convex in target production on its actual feasible
domain, including the region below positive baseline production. -/
theorem sourceEffortAtScore_convexOn {production : ℝ → ℝ} {effortMax : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax))
    (hg_conc : ConcaveOn ℝ (Icc 0 effortMax) production) :
    ConvexOn ℝ (Iic (production effortMax)) (sourceEffortAtScore production effortMax) := by
  refine ⟨convex_Iic _, ?_⟩
  intro a ha b hb u v hu hv huv
  have hia := sourceEffortAtScore_spec hmax hg hg_mono.monotoneOn ha
  have hib := sourceEffortAtScore_spec hmax hg hg_mono.monotoneOn hb
  have hiavg := sourceEffortAtScore_spec hmax hg hg_mono.monotoneOn
    ((convex_Iic _) ha hb hu hv huv)
  have hblend := (convex_Icc _ _) hia.1 hib.1 hu hv huv
  apply (hg_mono.le_iff_le hiavg.1 hblend).mp
  rw [hiavg.2]
  apply max_le
  · calc
      u • a + v • b ≤ u • production (sourceEffortAtScore production effortMax a) +
          v • production (sourceEffortAtScore production effortMax b) := by
            rw [hia.2, hib.2]
            exact add_le_add (smul_le_smul_of_nonneg_left (le_max_left _ _) hu)
              (smul_le_smul_of_nonneg_left (le_max_left _ _) hv)
      _ ≤ production (u • sourceEffortAtScore production effortMax a +
          v • sourceEffortAtScore production effortMax b) := hg_conc.2 hia.1 hib.1 hu hv huv
  · exact hg_mono.monotoneOn ⟨le_rfl, hmax⟩ hblend hblend.1

theorem sourceCostAtScore_monotoneOn {cost production : ℝ → ℝ} {effortMax : ℝ}
    (hmax : 0 ≤ effortMax) (hcost_mono : MonotoneOn cost (Icc 0 effortMax))
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) :
    MonotoneOn (sourceCostAtScore cost production effortMax) (Iic (production effortMax)) := by
  intro a ha b hb hab
  exact hcost_mono (sourceEffortAtScore_spec hmax hg hg_mono.monotoneOn ha).1
    (sourceEffortAtScore_spec hmax hg hg_mono.monotoneOn hb).1
    (sourceEffortAtScore_monotoneOn hmax hg hg_mono ha hb hab)

theorem sourceCostAtScore_convexOn {cost production : ℝ → ℝ} {effortMax : ℝ}
    (hmax : 0 ≤ effortMax) (hcost_mono : MonotoneOn cost (Icc 0 effortMax))
    (hcost_convex : ConvexOn ℝ (Icc 0 effortMax) cost)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax))
    (hg_conc : ConcaveOn ℝ (Icc 0 effortMax) production) :
    ConvexOn ℝ (Iic (production effortMax)) (sourceCostAtScore cost production effortMax) := by
  refine ⟨convex_Iic _, ?_⟩
  intro a ha b hb u v hu hv huv
  have hia := sourceEffortAtScore_spec hmax hg hg_mono.monotoneOn ha
  have hib := sourceEffortAtScore_spec hmax hg hg_mono.monotoneOn hb
  exact (hcost_mono
    (sourceEffortAtScore_spec hmax hg hg_mono.monotoneOn ((convex_Iic _) ha hb hu hv huv)).1
    ((convex_Icc _ _) hia.1 hib.1 hu hv huv)
    ((sourceEffortAtScore_convexOn hmax hg hg_mono hg_conc).2 ha hb hu hv huv)).trans
      (hcost_convex.2 hia.1 hib.1 hu hv huv)

theorem sourceCostAtScore_zero {cost production : ℝ → ℝ} {effortMax : ℝ}
    (hmax : 0 ≤ effortMax) (hcost_zero : cost 0 = 0)
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : 0 ≤ production 0) :
    sourceCostAtScore cost production effortMax 0 = 0 := by
  unfold sourceCostAtScore
  rw [sourceEffortAtScore_zero hmax hg_mono hg_zero, hcost_zero]

private theorem convex_gap_le_on_Iic {C : ℝ → ℝ} {upper a b c d : ℝ}
    (hconv : ConvexOn ℝ (Iic upper) C) (hmono : MonotoneOn C (Iic upper))
    (hab : a < b) (hcd : c < d) (hac : a ≤ c) (hbd : b ≤ d)
    (hlen : b - a ≤ d - c) (hd : d ≤ upper) :
    C b - C a ≤ C d - C c := by
  have had : a < d := hac.trans_lt hcd
  have hs1 := hconv.slope_mono (hab.le.trans (hbd.trans hd))
    (show b ∈ Iic upper \ {a} from ⟨hbd.trans hd, by simpa using hab.ne'⟩)
    (show d ∈ Iic upper \ {a} from ⟨hd, by simpa using had.ne'⟩) hbd
  have hs2 := hconv.slope_mono hd
    (show a ∈ Iic upper \ {d} from ⟨had.le.trans hd, by simpa using had.ne⟩)
    (show c ∈ Iic upper \ {d} from ⟨hcd.le.trans hd, by simpa using hcd.ne⟩) hac
  have hslope : slope C a b ≤ slope C c d := by
    exact hs1.trans (by simpa only [slope_comm] using hs2)
  have hsnonneg : 0 ≤ slope C c d := by
    rw [slope_def_field]
    exact div_nonneg (sub_nonneg.mpr (hmono (hcd.le.trans hd) hd hcd.le)) (sub_nonneg.mpr hcd.le)
  have hprod := (mul_le_mul_of_nonneg_left hslope (sub_nonneg.mpr hab.le)).trans
    (mul_le_mul_of_nonneg_right hlen hsnonneg)
  have hleft : (b - a) * slope C a b = C b - C a := by
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hab.ne']
  have hright : (d - c) * slope C c d = C d - C c := by
    rw [slope_def_field]
    field_simp [sub_ne_zero.mpr hcd.ne']
  simpa only [hleft, hright] using hprod

/-- Higher skill weakly reduces the incremental effort cost of moving
between two attainable score targets. This single-crossing property follows
from source cost convexity and production concavity on feasible domains,
including a positive zero-effort production floor. -/
theorem sourceCostAtScore_gap_antitone_skill
    {cost production : ℝ → ℝ} {effortMax lowerScore upperScore lowSkill highSkill : ℝ}
    (hmax : 0 ≤ effortMax) (hcost_mono : MonotoneOn cost (Icc 0 effortMax))
    (hcost_convex : ConvexOn ℝ (Icc 0 effortMax) cost)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax))
    (hg_conc : ConcaveOn ℝ (Icc 0 effortMax) production)
    (hlo : 0 ≤ lowerScore) (hscore : lowerScore ≤ upperScore)
    (hskill : 0 < lowSkill) (hskill_order : lowSkill ≤ highSkill)
    (hfeasible : upperScore / lowSkill ≤ production effortMax) :
    sourceCostAtScore cost production effortMax (upperScore / highSkill) -
        sourceCostAtScore cost production effortMax (lowerScore / highSkill) ≤
      sourceCostAtScore cost production effortMax (upperScore / lowSkill) -
        sourceCostAtScore cost production effortMax (lowerScore / lowSkill) := by
  rcases eq_or_lt_of_le hscore with rfl | hscore
  · simp
  have hhigh : 0 < highSkill := hskill.trans_le hskill_order
  have hupper : 0 ≤ upperScore := hlo.trans hscore.le
  have hlow_order : lowerScore / highSkill ≤ lowerScore / lowSkill :=
    (div_le_div_iff₀ hhigh hskill).mpr (mul_le_mul_of_nonneg_left hskill_order hlo)
  have hupp_order : upperScore / highSkill ≤ upperScore / lowSkill :=
    (div_le_div_iff₀ hhigh hskill).mpr (mul_le_mul_of_nonneg_left hskill_order hupper)
  have hlen : upperScore / highSkill - lowerScore / highSkill ≤
      upperScore / lowSkill - lowerScore / lowSkill := by
    have h := (div_le_div_iff₀ hhigh hskill).mpr
      (mul_le_mul_of_nonneg_left hskill_order (sub_nonneg.mpr hscore.le))
    simpa only [sub_div] using h
  exact convex_gap_le_on_Iic
    (sourceCostAtScore_convexOn hmax hcost_mono hcost_convex hg hg_mono hg_conc)
    (sourceCostAtScore_monotoneOn hmax hcost_mono hg hg_mono)
    ((div_lt_div_iff_of_pos_right hhigh).mpr hscore)
    ((div_lt_div_iff_of_pos_right hskill).mpr hscore)
    hlow_order hupp_order hlen hfeasible

/-- The next boundary effort is defined by indifference with the preceding
band at the next cutoff skill, using the source's adjacent reward increment. -/
noncomputable def sourceBoundaryStepEffort (cost production : ℝ → ℝ)
    (effortMax previousScore cutoffSkill rewardIncrement : ℝ) : ℝ :=
  effortIntervalInverse cost effortMax
    (sourceCostAtScore cost production effortMax (previousScore / cutoffSkill) + rewardIncrement)

noncomputable def sourceBoundaryStepScore (cost production : ℝ → ℝ)
    (effortMax previousScore cutoffSkill rewardIncrement : ℝ) : ℝ :=
  production (sourceBoundaryStepEffort cost production effortMax previousScore cutoffSkill rewardIncrement) * cutoffSkill

/-- A feasible positive reward increment constructs the next boundary effort
and score, proves the exact indifference equation, and strictly separates
the new band from the preceding score and its own zero-effort baseline. -/
theorem sourceBoundaryStep_properties
    {cost production : ℝ → ℝ} {effortMax previousScore cutoffSkill rewardIncrement : ℝ}
    (hmax : 0 ≤ effortMax) (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax))
    (hskill : 0 < cutoffSkill) (hgap : 0 < rewardIncrement)
    (hscore : previousScore / cutoffSkill ≤ production effortMax)
    (hbudget : sourceCostAtScore cost production effortMax (previousScore / cutoffSkill) +
      rewardIncrement ≤ 1) :
    let e := sourceBoundaryStepEffort cost production effortMax previousScore cutoffSkill rewardIncrement
    let z := sourceBoundaryStepScore cost production effortMax previousScore cutoffSkill rewardIncrement
    e ∈ Icc (0 : ℝ) effortMax ∧
      cost e = sourceCostAtScore cost production effortMax (previousScore / cutoffSkill) + rewardIncrement ∧
      max previousScore (production 0 * cutoffSkill) < z ∧
      z ≤ production effortMax * cutoffSkill ∧
      sourceCostAtScore cost production effortMax (z / cutoffSkill) = cost e := by
  let old := sourceEffortAtScore production effortMax (previousScore / cutoffSkill)
  let e := sourceBoundaryStepEffort cost production effortMax previousScore cutoffSkill rewardIncrement
  have hold := sourceEffortAtScore_spec hmax hg hg_mono.monotoneOn hscore
  have holdcost : 0 ≤ cost old := by
    simpa only [hcost_zero] using hcost_mono.monotoneOn ⟨le_rfl, hmax⟩ hold.1 hold.1.1
  have he := effortIntervalInverse_spec hmax hcost
    (show sourceCostAtScore cost production effortMax (previousScore / cutoffSkill) + rewardIncrement ∈
        Icc (cost 0) (cost effortMax) by
      rw [hcost_zero, hcost_max]
      exact ⟨by change 0 ≤ cost old + rewardIncrement; linarith, hbudget⟩)
  have holt : old < e := by
    apply (hcost_mono.lt_iff_lt hold.1 he.1).mp
    change cost old < cost e
    have hce : cost e = cost old + rewardIncrement := he.2
    linarith
  have hglt := hg_mono hold.1 he.1 holt
  have hgt : max previousScore (production 0 * cutoffSkill) < production e * cutoffSkill := by
    have hmul := mul_lt_mul_of_pos_right hglt hskill
    rw [hold.2, max_mul_of_nonneg _ _ hskill.le, div_mul_cancel₀ _ hskill.ne'] at hmul
    exact hmul
  have htop : production e * cutoffSkill ≤ production effortMax * cutoffSkill :=
    mul_le_mul_of_nonneg_right (hg_mono.monotoneOn he.1 ⟨hmax, le_rfl⟩ he.1.2) hskill.le
  refine ⟨he.1, he.2, hgt, htop, ?_⟩
  change cost (sourceEffortAtScore production effortMax (production e * cutoffSkill / cutoffSkill)) = cost e
  rw [mul_div_cancel_right₀ _ hskill.ne', sourceEffortAtScore_at_production (e := e) hg_mono he.1]

/-- The source's recursive finite-band threshold scores. The zero score at
the first band encodes baseline effort through the clipped inverse. -/
noncomputable def sourceRecursiveBandScore (cost production : ℝ → ℝ)
    (effortMax : ℝ) (cutoffSkill reward : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => sourceBoundaryStepScore cost production effortMax
      (sourceRecursiveBandScore cost production effortMax cutoffSkill reward k)
      (cutoffSkill (k + 1)) (reward (k + 1) - reward k)

/-- The recursively defined scores satisfy the source adjacent indifference
equations, strict band separation, and a cost bound by the cumulative reward
gain. Feasibility is proved by induction; no boundary efforts or score
equalities are supplied. The first cutoff skill may be zero. -/
theorem sourceRecursiveBandScore_properties
    {cost production : ℝ → ℝ} {effortMax : ℝ} {n : ℕ} {cutoffSkill reward : ℕ → ℝ}
    (hmax : 0 ≤ effortMax) (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : 0 ≤ production 0)
    (hskill : ∀ k ∈ Icc (1 : ℕ) n, 0 < cutoffSkill k)
    (hskill_mono : MonotoneOn cutoffSkill (Icc (1 : ℕ) n))
    (hreward : StrictMonoOn reward (Icc (0 : ℕ) n))
    (hreward_zero : 0 ≤ reward 0) (hreward_top : reward n ≤ 1) :
    ∀ k, k < n →
      let T := sourceRecursiveBandScore cost production effortMax cutoffSkill reward
      max (T k) (production 0 * cutoffSkill (k + 1)) < T (k + 1) ∧
      T (k + 1) ≤ production effortMax * cutoffSkill (k + 1) ∧
      sourceCostAtScore cost production effortMax (T (k + 1) / cutoffSkill (k + 1)) =
        sourceCostAtScore cost production effortMax (T k / cutoffSkill (k + 1)) +
          (reward (k + 1) - reward k) ∧
      sourceCostAtScore cost production effortMax (T (k + 1) / cutoffSkill (k + 1)) ≤
        reward (k + 1) - reward 0 := by
  let T := sourceRecursiveBandScore cost production effortMax cutoffSkill reward
  let C := sourceCostAtScore cost production effortMax
  have hgmax : 0 ≤ production effortMax :=
    hg_zero.trans (hg_mono.monotoneOn ⟨le_rfl, hmax⟩ ⟨hmax, le_rfl⟩ hmax)
  have hCmono := sourceCostAtScore_monotoneOn hmax hcost_mono.monotoneOn hg hg_mono
  have hCzero : C 0 = 0 := sourceCostAtScore_zero hmax hcost_zero hg_mono hg_zero
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have hsnext := hskill (k + 1) ⟨by omega, by omega⟩
    have hprevious : T k / cutoffSkill (k + 1) ≤ production effortMax ∧
        C (T k / cutoffSkill (k + 1)) ≤ reward k - reward 0 := by
      cases k with
      | zero =>
        change (0 : ℝ) / cutoffSkill 1 ≤ production effortMax ∧
          C (0 / cutoffSkill 1) ≤ reward 0 - reward 0
        simpa only [zero_div, hCzero, sub_self, le_refl, and_true] using hgmax
      | succ j =>
        have hp := ih j (by omega) (by omega)
        have hs := hskill (j + 1) ⟨by omega, by omega⟩
        have hsorder := hskill_mono ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
          (show j + 1 ≤ j + 1 + 1 by omega)
        have hTpos : 0 < T (j + 1) :=
          (mul_nonneg hg_zero hs.le).trans_lt ((le_max_right _ _).trans_lt hp.1)
        have hinput : T (j + 1) / cutoffSkill (j + 1 + 1) ≤ production effortMax :=
          (div_le_iff₀ hsnext).mpr (hp.2.1.trans (mul_le_mul_of_nonneg_left hsorder hgmax))
        have hown : T (j + 1) / cutoffSkill (j + 1) ≤ production effortMax :=
          (div_le_iff₀ hs).mpr hp.2.1
        have hratio : T (j + 1) / cutoffSkill (j + 1 + 1) ≤ T (j + 1) / cutoffSkill (j + 1) :=
          (div_le_div_iff₀ hsnext hs).mpr (mul_le_mul_of_nonneg_left hsorder hTpos.le)
        exact ⟨hinput, (hCmono hinput hown hratio).trans hp.2.2.2⟩
    have hgap : 0 < reward (k + 1) - reward k :=
      sub_pos.mpr (hreward ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega))
    have hrnext : reward (k + 1) ≤ 1 :=
      (hreward.monotoneOn ⟨by omega, by omega⟩ ⟨by omega, le_rfl⟩ (by omega)).trans hreward_top
    have hbudget : C (T k / cutoffSkill (k + 1)) + (reward (k + 1) - reward k) ≤ 1 := by
      linarith [hprevious.2]
    have hstep := sourceBoundaryStep_properties hmax hcost hcost_mono hcost_zero hcost_max
      hg hg_mono hsnext hgap hprevious.1 hbudget
    have hid : C (T (k + 1) / cutoffSkill (k + 1)) =
        C (T k / cutoffSkill (k + 1)) + (reward (k + 1) - reward k) :=
      hstep.2.2.2.2.trans hstep.2.1
    refine ⟨hstep.2.2.1, hstep.2.2.2.1, hid, ?_⟩
    change C (T (k + 1) / cutoffSkill (k + 1)) ≤ reward (k + 1) - reward 0
    rw [hid]
    linarith [hprevious.2]

/-- The constructed score menu satisfies all finite-band incentive
comparisons. An applicant between two cutoff skills weakly prefers the
assigned reward band to every attainable alternative. Adjacent comparisons
follow from the source cost/production single-crossing property and then
telescope; no deviation score equalities or optimizer premises are assumed. -/
theorem sourceRecursiveBandScore_menu_optimal
    {cost production : ℝ → ℝ} {effortMax skill : ℝ} {n i j : ℕ} {cutoffSkill reward : ℕ → ℝ}
    (hmax : 0 ≤ effortMax) (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hcost_convex : ConvexOn ℝ (Icc 0 effortMax) cost)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : 0 ≤ production 0)
    (hg_conc : ConcaveOn ℝ (Icc 0 effortMax) production)
    (hskill : ∀ k ∈ Icc (1 : ℕ) n, 0 < cutoffSkill k)
    (hskill_mono : MonotoneOn cutoffSkill (Icc (1 : ℕ) n))
    (hreward : StrictMonoOn reward (Icc (0 : ℕ) n))
    (hreward_zero : 0 ≤ reward 0) (hreward_top : reward n ≤ 1)
    (hi : i ≤ n) (hj : j ≤ n) (hpositive : 0 < skill)
    (hlower : 0 < i → cutoffSkill i ≤ skill)
    (hupper : i < n → skill ≤ cutoffSkill (i + 1))
    (hattainable : sourceRecursiveBandScore cost production effortMax cutoffSkill reward j / skill ≤
      production effortMax) :
    reward j - sourceCostAtScore cost production effortMax
        (sourceRecursiveBandScore cost production effortMax cutoffSkill reward j / skill) ≤
      reward i - sourceCostAtScore cost production effortMax
        (sourceRecursiveBandScore cost production effortMax cutoffSkill reward i / skill) := by
  let T := sourceRecursiveBandScore cost production effortMax cutoffSkill reward
  let C := sourceCostAtScore cost production effortMax
  let U := fun k => reward k - C (T k / skill)
  have hstep := sourceRecursiveBandScore_properties hmax hcost hcost_mono hcost_zero hcost_max
    hg hg_mono hg_zero hskill hskill_mono hreward hreward_zero hreward_top
  have hTmono : MonotoneOn T (Icc (0 : ℕ) n) := by
    exact (strictMonoOn_Iic_of_lt_succ (fun k hk =>
      (le_max_left _ _).trans_lt (hstep k hk).1)).monotoneOn.mono Icc_subset_Iic_self
  have hTnonneg (k : ℕ) (hk : k ≤ n) : 0 ≤ T k :=
    hTmono ⟨Nat.zero_le _, Nat.zero_le _⟩ ⟨Nat.zero_le _, hk⟩ (Nat.zero_le _)
  have hskill_above (k : ℕ) (hik : i < k) (hk : k ≤ n) : skill ≤ cutoffSkill k :=
    (hupper (by omega)).trans (hskill_mono ⟨by omega, by omega⟩ ⟨by omega, hk⟩ (by omega))
  have hskill_below (k : ℕ) (hk : 0 < k) (hki : k ≤ i) : cutoffSkill k ≤ skill :=
    (hskill_mono ⟨hk, hki.trans hi⟩ ⟨by omega, hi⟩ hki).trans (hlower (by omega))
  rcases le_total i j with hij | hji
  · have hadj (k : ℕ) (hik : i ≤ k) (hkj : k < j) : U (k + 1) ≤ U k := by
      have hk : k < n := hkj.trans_le hj
      have hp := hstep k hk
      have hfeas : T (k + 1) / skill ≤ production effortMax :=
        (div_le_div_of_nonneg_right
          (hTmono ⟨by omega, by omega⟩ ⟨Nat.zero_le _, hj⟩ (by omega)) hpositive.le).trans hattainable
      have hgap := sourceCostAtScore_gap_antitone_skill hmax hcost_mono.monotoneOn hcost_convex
        hg hg_mono hg_conc (hTnonneg k hk.le)
        (hTmono ⟨Nat.zero_le _, hk.le⟩ ⟨by omega, by omega⟩ (by omega))
        hpositive (hskill_above (k + 1) (by omega) (by omega)) hfeas
      have hid : C (T (k + 1) / cutoffSkill (k + 1)) =
          C (T k / cutoffSkill (k + 1)) + (reward (k + 1) - reward k) := hp.2.2.1
      change C (T (k + 1) / cutoffSkill (k + 1)) - C (T k / cutoffSkill (k + 1)) ≤
        C (T (k + 1) / skill) - C (T k / skill) at hgap
      dsimp [U]
      linarith
    have h := secondPrice_nat_chain_no_profit_of_adjacent_from U i (j - i) (by
      intro k hik hk
      exact hadj k hik (by omega))
    simpa only [Nat.add_sub_of_le hij] using h
  · have hadj (k : ℕ) (hjk : j ≤ k) (hki : k < i) : U k ≤ U (k + 1) := by
      have hk : k < n := hki.trans_le hi
      have hp := hstep k hk
      have hs := hskill (k + 1) ⟨by omega, by omega⟩
      have hfeas : T (k + 1) / cutoffSkill (k + 1) ≤ production effortMax :=
        (div_le_iff₀ hs).mpr hp.2.1
      have hgap := sourceCostAtScore_gap_antitone_skill hmax hcost_mono.monotoneOn hcost_convex
        hg hg_mono hg_conc (hTnonneg k hk.le)
        (hTmono ⟨Nat.zero_le _, hk.le⟩ ⟨by omega, by omega⟩ (by omega))
        hs (hskill_below (k + 1) (by omega) (by omega)) hfeas
      have hid : C (T (k + 1) / cutoffSkill (k + 1)) =
          C (T k / cutoffSkill (k + 1)) + (reward (k + 1) - reward k) := hp.2.2.1
      change C (T (k + 1) / skill) - C (T k / skill) ≤
        C (T (k + 1) / cutoffSkill (k + 1)) - C (T k / cutoffSkill (k + 1)) at hgap
      dsimp [U]
      linarith
    have h := secondPrice_nat_reverse_chain_no_profit_of_adjacent_from U j (i - j) (by
      intro k hjk hk
      exact hadj k hjk (by omega))
    simpa only [Nat.add_sub_of_le hji] using h

/-- The assigned-band effort is feasible, costs at most its cumulative reward
gain over the bottom band, and produces exactly the clipped source score.
These facts are derived from the recursive boundary construction. -/
theorem sourceRecursiveBandScore_assigned_effort
    {cost production : ℝ → ℝ} {effortMax skill : ℝ} {n i : ℕ} {cutoffSkill reward : ℕ → ℝ}
    (hmax : 0 ≤ effortMax) (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : 0 ≤ production 0)
    (hskill : ∀ k ∈ Icc (1 : ℕ) n, 0 < cutoffSkill k)
    (hskill_mono : MonotoneOn cutoffSkill (Icc (1 : ℕ) n))
    (hreward : StrictMonoOn reward (Icc (0 : ℕ) n))
    (hreward_zero : 0 ≤ reward 0) (hreward_top : reward n ≤ 1)
    (hi : i ≤ n) (hpositive : 0 < skill) (hlower : 0 < i → cutoffSkill i ≤ skill) :
    let T := sourceRecursiveBandScore cost production effortMax cutoffSkill reward
    let e := sourceEffortAtScore production effortMax (T i / skill)
    e ∈ Icc (0 : ℝ) effortMax ∧ cost e ≤ reward i - reward 0 ∧
      production e * skill = max (T i) (production 0 * skill) := by
  let T := sourceRecursiveBandScore cost production effortMax cutoffSkill reward
  let C := sourceCostAtScore cost production effortMax
  have hgmax : 0 ≤ production effortMax :=
    hg_zero.trans (hg_mono.monotoneOn ⟨le_rfl, hmax⟩ ⟨hmax, le_rfl⟩ hmax)
  have hstep := sourceRecursiveBandScore_properties hmax hcost hcost_mono hcost_zero hcost_max
    hg hg_mono hg_zero hskill hskill_mono hreward hreward_zero hreward_top
  have hinput : T i / skill ≤ production effortMax ∧ C (T i / skill) ≤ reward i - reward 0 := by
    cases i with
    | zero =>
      have hCzero : C 0 = 0 := sourceCostAtScore_zero hmax hcost_zero hg_mono hg_zero
      change (0 : ℝ) / skill ≤ production effortMax ∧ C (0 / skill) ≤ reward 0 - reward 0
      simpa only [zero_div, hCzero, sub_self, le_refl, and_true] using hgmax
    | succ k =>
      have hp := hstep k (by omega)
      have hs := hskill (k + 1) ⟨by omega, hi⟩
      have hsorder := hlower (by omega)
      have hTnonneg : 0 ≤ T (k + 1) :=
        ((mul_nonneg hg_zero hs.le).trans_lt ((le_max_right _ _).trans_lt hp.1)).le
      have hown : T (k + 1) / cutoffSkill (k + 1) ≤ production effortMax :=
        (div_le_iff₀ hs).mpr hp.2.1
      have hratio : T (k + 1) / skill ≤ T (k + 1) / cutoffSkill (k + 1) :=
        (div_le_div_iff₀ hpositive hs).mpr (mul_le_mul_of_nonneg_left hsorder hTnonneg)
      have hfeas := hratio.trans hown
      exact ⟨hfeas,
        ((sourceCostAtScore_monotoneOn hmax hcost_mono.monotoneOn hg hg_mono)
          hfeas hown hratio).trans hp.2.2.2⟩
  have he := sourceEffortAtScore_spec hmax hg hg_mono.monotoneOn hinput.1
  refine ⟨he.1, hinput.2, ?_⟩
  rw [he.2, max_mul_of_nonneg _ _ hpositive.le, div_mul_cancel₀ _ hpositive.ne']

/-- The constructed effort is a best response to the finite score-threshold
menu over every nonnegative effort, not merely over boundary efforts. Its
own classifier band is proved to be the assigned band. Efforts beyond the
unit-cost cap cannot improve payoff because rewards are at most one. The
separate CDF-rank bridge must identify this menu with ranking rewards. -/
theorem sourceRecursiveBandScore_bestResponse_to_scoreClassifier
    {cost production : ℝ → ℝ} {effortMax skill : ℝ} {n i : ℕ} {cutoffSkill reward : ℕ → ℝ}
    (hmax : 0 ≤ effortMax) (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Ici 0))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hcost_convex : ConvexOn ℝ (Icc 0 effortMax) cost)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : 0 ≤ production 0)
    (hg_conc : ConcaveOn ℝ (Icc 0 effortMax) production)
    (hskill : ∀ k ∈ Icc (1 : ℕ) n, 0 < cutoffSkill k)
    (hskill_mono : MonotoneOn cutoffSkill (Icc (1 : ℕ) n))
    (hreward : StrictMonoOn reward (Icc (0 : ℕ) n))
    (hreward_zero : 0 ≤ reward 0) (hreward_top : reward n ≤ 1)
    (hi : i ≤ n) (hpositive : 0 < skill)
    (hlower : 0 < i → cutoffSkill i ≤ skill)
    (hupper : i < n → skill ≤ cutoffSkill (i + 1)) :
    let T := sourceRecursiveBandScore cost production effortMax cutoffSkill reward
    let e := sourceEffortAtScore production effortMax (T i / skill)
    let band := fun d => finiteScoreBand (fun k : Fin (n + 1) => T k) (production d * skill)
    e ∈ Icc (0 : ℝ) effortMax ∧ (band e).val = i ∧
      ∀ d : ℝ, 0 ≤ d → reward (band d).val - cost d ≤ reward (band e).val - cost e := by
  let T := sourceRecursiveBandScore cost production effortMax cutoffSkill reward
  let e := sourceEffortAtScore production effortMax (T i / skill)
  let band := fun d => finiteScoreBand (fun k : Fin (n + 1) => T k) (production d * skill)
  have hpmono : StrictMonoOn cost (Icc 0 effortMax) := hcost_mono.mono Icc_subset_Ici_self
  have he := sourceRecursiveBandScore_assigned_effort hmax hcost hpmono hcost_zero hcost_max
    hg hg_mono hg_zero hskill hskill_mono hreward hreward_zero hreward_top hi hpositive hlower
  have hstep := sourceRecursiveBandScore_properties hmax hcost hpmono hcost_zero hcost_max
    hg hg_mono hg_zero hskill hskill_mono hreward hreward_zero hreward_top
  have hTstrict : StrictMonoOn T (Iic n) := strictMonoOn_Iic_of_lt_succ
    (fun k hk => (le_max_left _ _).trans_lt (hstep k hk).1)
  have hband : (band e).val = i := by
    have hfirst : T i ≤ production e * skill := by
      change T i ≤ production e * skill
      have heq : production e * skill = max (T i) (production 0 * skill) := he.2.2
      rw [heq]
      exact le_max_left _ _
    have hb : band e = (⟨i, by omega⟩ : Fin (n + 1)) := by
      apply finiteScoreBand_eq_of_target_interval hfirst
      intro j hij
      have hijn : i < j.val := hij
      have hin : i < n := by omega
      have hj : j.val ≤ n := by omega
      have hbaseline : production 0 * skill < T (i + 1) :=
        (mul_le_mul_of_nonneg_left (hupper hin) hg_zero).trans_lt
          ((le_max_right _ _).trans_lt (hstep i hin).1)
      have htarg : T i < T j.val := hTstrict hi hj hijn
      have heq : production e * skill = max (T i) (production 0 * skill) := he.2.2
      change production e * skill < T j.val
      rw [heq]
      exact max_lt htarg (hbaseline.trans_le
        (hTstrict.monotoneOn (Nat.succ_le_of_lt hin) hj (Nat.succ_le_of_lt hijn)))
    exact congrArg Fin.val hb
  refine ⟨he.1, hband, ?_⟩
  intro d hd
  change reward (band d).val - cost d ≤ reward (band e).val - cost e
  rw [hband]
  have hj : (band d).val ≤ n := Nat.le_of_lt_succ (band d).isLt
  by_cases hdE : d ≤ effortMax
  · have hg0 : 0 ≤ production d := hg_zero.trans (hg_mono.monotoneOn ⟨le_rfl, hmax⟩ ⟨hd, hdE⟩ hd)
    have hreach : T (band d).val ≤ production d * skill :=
      finiteScoreBand_target_le_of_bottom (target := fun k : Fin (n + 1) => T k.val)
        (show T 0 ≤ production d * skill from mul_nonneg hg0 hpositive.le)
    have hinput : T (band d).val / skill ≤ production d := (div_le_iff₀ hpositive).mpr hreach
    have hfeas := hinput.trans (hg_mono.monotoneOn ⟨hd, hdE⟩ ⟨hmax, le_rfl⟩ hdE)
    have hmin := sourceEffortAtScore_spec hmax hg hg_mono.monotoneOn hfeas
    have hmin_le : sourceEffortAtScore production effortMax (T (band d).val / skill) ≤ d := by
      apply (hg_mono.le_iff_le hmin.1 ⟨hd, hdE⟩).mp
      rw [hmin.2]
      exact max_le hinput (hg_mono.monotoneOn ⟨le_rfl, hmax⟩ ⟨hd, hdE⟩ hd)
    have hcostle := hpmono.monotoneOn hmin.1 ⟨hd, hdE⟩ hmin_le
    have hopt := sourceRecursiveBandScore_menu_optimal hmax hcost hpmono hcost_zero hcost_max
      hcost_convex hg hg_mono hg_zero hg_conc hskill hskill_mono hreward hreward_zero hreward_top
      hi hj hpositive hlower hupper hfeas
    exact (sub_le_sub_left hcostle (reward (band d).val)).trans hopt
  · have hcostgt : 1 < cost d := by
      simpa only [hcost_max] using hcost_mono hmax hd (lt_of_not_ge hdE)
    have hrle : reward (band d).val ≤ 1 :=
      (hreward.monotoneOn ⟨Nat.zero_le _, hj⟩ ⟨Nat.zero_le _, le_rfl⟩ hj).trans hreward_top
    have hown : cost e ≤ reward i - reward 0 := he.2.1
    linarith

end LBG22StrategicRanking
