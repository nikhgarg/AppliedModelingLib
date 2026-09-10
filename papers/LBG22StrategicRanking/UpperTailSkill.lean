import LBG22StrategicRanking.PrimitiveRepairs
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Upper-tail skill curvature

Concavity of log skill in negative log tail mass is sufficient for shrinking
proportional skill advantages inside the admitted population. This condition
permits log-convex skill quantiles, unlike concavity of log skill in rank.
-/

namespace LBG22StrategicRanking

open Set

/-- Rank expressed in negative log upper-tail population mass. -/
noncomputable def upperTailRank (x : ℝ) : ℝ := 1 - Real.exp (-x)

theorem upperTailRank_mem_Ioo {x : ℝ} (hx : 0 < x) :
    upperTailRank x ∈ Ioo (0 : ℝ) 1 := by
  have hexp : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos := Real.exp_pos (-x)
  constructor <;> dsimp [upperTailRank] <;> linarith

theorem upperTailRank_neg_log {c : ℝ} (hc : c < 1) :
    upperTailRank (-Real.log (1 - c)) = c := by
  simp only [upperTailRank, neg_neg, Real.exp_log (sub_pos.mpr hc)]
  ring

theorem upperTailRank_strictMono : StrictMono upperTailRank := by
  intro x y hxy
  have he := Real.exp_lt_exp.mpr (neg_lt_neg hxy)
  dsimp [upperTailRank]
  linarith

theorem upperTailRank_hasDerivAt (x : ℝ) :
    HasDerivAt upperTailRank (1 - upperTailRank x) x := by
  convert ((hasDerivAt_id x).neg.exp).const_sub 1 using 1
  dsimp [upperTailRank]
  ring

/-- The admitted-tail affine transformation becomes translation in negative
log tail mass. -/
theorem admittedTailRank_upperTailRank (x y : ℝ) :
    admittedTailRank (upperTailRank x) (upperTailRank y) = upperTailRank (x + y) := by
  simp only [admittedTailRank, upperTailRank, neg_add, Real.exp_add]
  ring

/-- Concavity in negative log tail mass implies monotonicity of within-tail
skill ratios. The top-rank and whole-tail endpoints use only monotone skill. -/
theorem admittedTail_skill_ratio_monotone_of_upperTailConcavity {f : ℝ → ℝ}
    (hf_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < f t)
    (hf_mono : MonotoneOn f (Ioc (0 : ℝ) 1))
    (hf_tail : ConcaveOn ℝ (Ioi (0 : ℝ))
      (fun x => Real.log (f (upperTailRank x))))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    MonotoneOn (fun c => f c / f (admittedTailRank c s)) (Ioc (0 : ℝ) 1) := by
  intro a ha b hb hab
  change f a / f (admittedTailRank a s) ≤ f b / f (admittedTailRank b s)
  have hta := admittedTailRank_mem_Icc ⟨ha.1.le, ha.2⟩ hs
  have htb := admittedTailRank_mem_Icc ⟨hb.1.le, hb.2⟩ hs
  have hta' : admittedTailRank a s ∈ Ioc (0 : ℝ) 1 := ⟨ha.1.trans_le hta.1, hta.2⟩
  have htb' : admittedTailRank b s ∈ Ioc (0 : ℝ) 1 := ⟨hb.1.trans_le htb.1, htb.2⟩
  by_cases hb1 : b = 1
  · subst b
    have htail1 : admittedTailRank 1 s = 1 := by simp [admittedTailRank]
    rw [htail1, div_self (hf_pos 1 ⟨by norm_num, le_rfl⟩).ne']
    exact (div_le_one (hf_pos _ hta')).mpr (hf_mono ha hta' hta.1)
  by_cases hs1 : s = 1
  · subst s
    have htail1 (c : ℝ) : admittedTailRank c 1 = 1 := by simp [admittedTailRank]
    simp only [htail1]
    exact div_le_div_of_nonneg_right (hf_mono ha hb hab)
      (hf_pos 1 ⟨by norm_num, le_rfl⟩).le
  have hb_lt : b < 1 := lt_of_le_of_ne hb.2 hb1
  have ha_lt : a < 1 := hab.trans_lt hb_lt
  have hs_lt : s < 1 := lt_of_le_of_ne hs.2 hs1
  have ha_log : 0 < -Real.log (1 - a) := by
    have := Real.log_neg (sub_pos.mpr ha_lt) (by linarith [ha.1] : 1 - a < 1)
    linarith
  have hb_log : 0 < -Real.log (1 - b) := by
    have := Real.log_neg (sub_pos.mpr hb_lt) (by linarith [hb.1] : 1 - b < 1)
    linarith
  have hs_log : 0 ≤ -Real.log (1 - s) := by
    have := Real.log_nonpos (sub_pos.mpr hs_lt).le (by linarith [hs.1] : 1 - s ≤ 1)
    linarith
  have hab_log : -Real.log (1 - a) ≤ -Real.log (1 - b) := by
    have := Real.log_le_log (sub_pos.mpr hb_lt) (by linarith : 1 - b ≤ 1 - a)
    linarith
  have htail (c : ℝ) (hc : c < 1) :
      upperTailRank (-Real.log (1 - c) + -Real.log (1 - s)) =
        admittedTailRank c s := by
    rw [← admittedTailRank_upperTailRank, upperTailRank_neg_log hc,
      upperTailRank_neg_log hs_lt]
  have hinc := concave_increment_le hf_tail
    (a := -Real.log (1 - a)) (b := -Real.log (1 - b)) (h := -Real.log (1 - s))
    ha_log (by change 0 < -Real.log (1 - b) + -Real.log (1 - s); linarith) hab_log hs_log
  simp only [htail a ha_lt, htail b hb_lt, upperTailRank_neg_log ha_lt,
    upperTailRank_neg_log hb_lt] at hinc
  apply (Real.log_le_log_iff (div_pos (hf_pos _ ha) (hf_pos _ hta'))
    (div_pos (hf_pos _ hb) (hf_pos _ htb'))).mp
  rw [Real.log_div (hf_pos _ ha).ne' (hf_pos _ hta').ne',
    Real.log_div (hf_pos _ hb).ne' (hf_pos _ htb').ne']
  linarith

/-- The map from negative log tail mass to rank is concave. -/
theorem concaveOn_upperTailRank : ConcaveOn ℝ (Ioi (0 : ℝ)) upperTailRank := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy a b ha hb hab
  have he := convexOn_exp.2 (mem_univ (-x)) (mem_univ (-y)) ha hb hab
  simp only [smul_eq_mul] at he ⊢
  have hneg : a * -x + b * -y = -(a * x + b * y) := by ring
  rw [hneg] at he
  dsimp [upperTailRank]
  nlinarith

/-- Ordinary increasing log-concave skill satisfies the weaker upper-tail
curvature condition. No smoothness or strict monotonicity is required. -/
theorem upperTail_logSkill_concaveOn_of_logConcave {f : ℝ → ℝ}
    (hf_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < f t)
    (hf_mono : MonotoneOn f (Ioc (0 : ℝ) 1))
    (hf_log : ConcaveOn ℝ (Ioc (0 : ℝ) 1) (fun t => Real.log (f t))) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x => Real.log (f (upperTailRank x))) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : upperTailRank x ∈ Ioc (0 : ℝ) 1 :=
    ⟨(upperTailRank_mem_Ioo hx).1, (upperTailRank_mem_Ioo hx).2.le⟩
  have hy' : upperTailRank y ∈ Ioc (0 : ℝ) 1 :=
    ⟨(upperTailRank_mem_Ioo hy).1, (upperTailRank_mem_Ioo hy).2.le⟩
  have hz := (convex_Ioc (0 : ℝ) 1) hx' hy' ha hb hab
  have hw := (convex_Ioi (0 : ℝ)) hx hy ha hb hab
  have hw' : upperTailRank (a • x + b • y) ∈ Ioc (0 : ℝ) 1 :=
    ⟨(upperTailRank_mem_Ioo hw).1, (upperTailRank_mem_Ioo hw).2.le⟩
  exact (hf_log.2 hx' hy' ha hb hab).trans
    (Real.log_le_log (hf_pos _ hz) (hf_mono hz hw'
      (concaveOn_upperTailRank.2 hx hy ha hb hab)))

/-- The derivative of log skill with respect to negative log tail mass is
the rank logarithmic derivative multiplied by the remaining population mass. -/
theorem upperTail_logSkill_hasDerivAt {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f (upperTailRank x))
    (hf_pos : 0 < f (upperTailRank x)) :
    HasDerivAt (fun y => Real.log (f (upperTailRank y)))
      ((1 - upperTailRank x) * deriv f (upperTailRank x) / f (upperTailRank x)) x := by
  convert (hf.hasDerivAt.comp x (upperTailRank_hasDerivAt x)).log hf_pos.ne' using 1
  simp only [Function.comp_apply]
  ring

/-- A nonincreasing tail-weighted logarithmic derivative of the skill quantile
implies upper-tail log concavity. Only first differentiability on the interior
is needed; no regularity of the derivative is assumed. -/
theorem upperTail_logSkill_concaveOn_of_tailSlope_antitone {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Ioo (0 : ℝ) 1))
    (hf_pos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < f t)
    (hsl : AntitoneOn (fun t => (1 - t) * deriv f t / f t) (Ioo (0 : ℝ) 1)) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x => Real.log (f (upperTailRank x))) := by
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun y => Real.log (f (upperTailRank y)))
        ((1 - upperTailRank x) * deriv f (upperTailRank x) / f (upperTailRank x)) x :=
    upperTail_logSkill_hasDerivAt
      (hf.differentiableAt (isOpen_Ioo.mem_nhds (upperTailRank_mem_Ioo hx)))
      (hf_pos _ (upperTailRank_mem_Ioo hx))
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioi _)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt)
  intro x hx y hy hxy
  rw [(hd x (interior_subset hx)).deriv, (hd y (interior_subset hy)).deriv]
  exact hsl (upperTailRank_mem_Ioo (interior_subset hx))
    (upperTailRank_mem_Ioo (interior_subset hy)) (upperTailRank_strictMono.monotone hxy)

/-- Under first differentiability, the upper-tail curvature condition is
equivalent to a nonincreasing tail-weighted logarithmic derivative. -/
theorem upperTail_logSkill_concaveOn_iff_tailSlope_antitone {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Ioo (0 : ℝ) 1))
    (hf_pos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < f t) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x => Real.log (f (upperTailRank x))) ↔
      AntitoneOn (fun t => (1 - t) * deriv f t / f t) (Ioo (0 : ℝ) 1) := by
  refine ⟨?_, upperTail_logSkill_concaveOn_of_tailSlope_antitone hf hf_pos⟩
  intro hconc
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun y => Real.log (f (upperTailRank y)))
        ((1 - upperTailRank x) * deriv f (upperTailRank x) / f (upperTailRank x)) x :=
    upperTail_logSkill_hasDerivAt
      (hf.differentiableAt (isOpen_Ioo.mem_nhds (upperTailRank_mem_Ioo hx)))
      (hf_pos _ (upperTailRank_mem_Ioo hx))
  have hanti := hconc.antitoneOn_deriv (fun x hx => (hd x hx).differentiableAt)
  intro a ha b hb hab
  have hapos : 0 < -Real.log (1 - a) := by
    have := Real.log_neg (sub_pos.mpr ha.2) (by linarith [ha.1] : 1 - a < 1)
    linarith
  have hbpos : 0 < -Real.log (1 - b) := by
    have := Real.log_neg (sub_pos.mpr hb.2) (by linarith [hb.1] : 1 - b < 1)
    linarith
  have hlogab : -Real.log (1 - a) ≤ -Real.log (1 - b) := by
    have := Real.log_le_log (sub_pos.mpr hb.2) (by linarith : 1 - b ≤ 1 - a)
    linarith
  have h := hanti hapos hbpos hlogab
  rw [(hd _ hapos).deriv, (hd _ hbpos).deriv] at h
  simpa only [upperTailRank_neg_log ha.2, upperTailRank_neg_log hb.2] using h

/-- The reciprocal-affine skill quantile satisfies upper-tail concavity even
though its logarithm is convex in rank. -/
theorem reciprocalAffineSkill_upperTail_log_concaveOn :
    ConcaveOn ℝ (Ioi (0 : ℝ))
      (fun x => Real.log (1 / (2 - upperTailRank x))) := by
  have heq : (fun x : ℝ => Real.log (1 / (2 - upperTailRank x))) =
      (fun x => -Real.log (1 + Real.exp (-x))) := by
    funext x
    have hden : 2 - upperTailRank x = 1 + Real.exp (-x) := by
      dsimp [upperTailRank]
      ring
    rw [hden, one_div, Real.log_inv]
  rw [heq]
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => -Real.log (1 + Real.exp (-y)))
      (Real.exp (-x) / (1 + Real.exp (-x))) x := by
    convert ((((hasDerivAt_id x).neg.exp).const_add 1).log
      (by positivity : 1 + Real.exp (-x) ≠ 0)).neg using 1
    simp
    ring
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioi _)
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
  intro x hx y hy hxy
  rw [(hd x).deriv, (hd y).deriv]
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + Real.exp (-y))
    (by positivity : 0 < 1 + Real.exp (-x))).mpr
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hxy)
  nlinarith

/-- A concrete failure of ordinary log-concavity, witnessed entirely inside
the rank interval. -/
theorem reciprocalAffineSkill_log_not_concaveOn :
    ¬ ConcaveOn ℝ (Ioc (0 : ℝ) 1) (fun t => Real.log (1 / (2 - t))) := by
  intro h
  have hmid := h.2 (show (1 / 4 : ℝ) ∈ Ioc (0 : ℝ) 1 by norm_num)
    (show (3 / 4 : ℝ) ∈ Ioc (0 : ℝ) 1 by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num)
  norm_num only [smul_eq_mul] at hmid
  have hgap := Real.log_lt_log (by norm_num : 0 < (2 / 3 : ℝ) ^ 2)
    (by norm_num : (2 / 3 : ℝ) ^ 2 < (4 / 7 : ℝ) * (4 / 5 : ℝ))
  rw [Real.log_pow, Real.log_mul (by norm_num : (4 / 7 : ℝ) ≠ 0)
    (by norm_num : (4 / 5 : ℝ) ≠ 0)] at hgap
  norm_num only [Nat.cast_ofNat] at hgap
  linarith

/-- The upper-tail curvature assumption strictly extends ordinary increasing
log-concave skill; this witness is positive, continuous, and strictly increasing
on the complete rank interval. -/
theorem reciprocalAffineSkill_strict_broadening :
    (∀ t ∈ Icc (0 : ℝ) 1, 0 < 1 / (2 - t)) ∧
    ContinuousOn (fun t : ℝ => 1 / (2 - t)) (Icc (0 : ℝ) 1) ∧
    StrictMonoOn (fun t : ℝ => 1 / (2 - t)) (Icc (0 : ℝ) 1) ∧
    ConcaveOn ℝ (Ioi (0 : ℝ))
      (fun x => Real.log (1 / (2 - upperTailRank x))) ∧
    ¬ ConcaveOn ℝ (Ioc (0 : ℝ) 1) (fun t => Real.log (1 / (2 - t))) := by
  refine ⟨?_, ?_, ?_, reciprocalAffineSkill_upperTail_log_concaveOn,
    reciprocalAffineSkill_log_not_concaveOn⟩
  · intro t ht
    exact one_div_pos.mpr (by linarith [ht.2])
  · exact continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      (fun t ht => by linarith [ht.2])
  · intro x hx y hy hxy
    exact one_div_lt_one_div_of_lt (by linarith [hy.2]) (by linarith)

end LBG22StrategicRanking
