import LBG22StrategicRanking.IndependentSkillUtility

/-!
# Affine measurable-skill quantiles

For `f(t)=b+k*t`, normalizing scores by `b+k` gives the lower-skill fraction
`tau=b/(b+k)`. The capacity equation then uses effective capacity
`(1-tau)*rho`, while the feasible production interval still starts at the
effort cost `rho`. Its positive lower output must be retained in the inverse
construction and in all shape conditions.
-/

namespace LBG22StrategicRanking

open Set Filter MeasureTheory
open scoped Topology

/-- Normalized measurable output for an affine skill quantile. -/
theorem affineSkillOutput_eq_convex_combination (C : ℝ → ℝ) (rho tau a : ℝ) :
    uniformSkillOutput C ((1 - tau) * rho) a =
      tau * a + (1 - tau) * uniformSkillOutput C rho a := by
  unfold uniformSkillOutput
  ring

theorem affineSkillOutput_strictMonoOn {C : ℝ → ℝ} {rho tau lo hi : ℝ}
    (hrho : 0 < rho) (htau : 0 ≤ tau) (htau_one : tau < 1)
    (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hmono : StrictMonoOn C (Icc lo hi)) (hClo : C lo = rho) :
    StrictMonoOn (uniformSkillOutput C ((1 - tau) * rho)) (Icc lo hi) := by
  have hF := uniformSkillOutput_strictMonoOn hrho hlo hlohi hmono hClo
  intro a ha b hb hab
  rw [affineSkillOutput_eq_convex_combination, affineSkillOutput_eq_convex_combination]
  exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hab.le htau)
    (mul_lt_mul_of_pos_left (hF ha hb hab) (sub_pos.mpr htau_one))

theorem affineSkillOutput_continuousOn {C : ℝ → ℝ} {rho tau lo hi : ℝ}
    (hrho : 0 < rho) (hlohi : lo ≤ hi)
    (hcont : ContinuousOn C (Icc lo hi)) (hmono : MonotoneOn C (Icc lo hi))
    (hClo : C lo = rho) :
    ContinuousOn (uniformSkillOutput C ((1 - tau) * rho)) (Icc lo hi) := by
  have h : ContinuousOn (fun a => tau * a + (1 - tau) * uniformSkillOutput C rho a)
      (Icc lo hi) := (continuousOn_const.mul continuousOn_id).add
    (continuousOn_const.mul (uniformSkillOutput_continuousOn hrho hlohi hcont hmono hClo))
  exact h.congr (fun a _ => affineSkillOutput_eq_convex_combination C rho tau a)

theorem affineSkillOutput_lower_endpoint {C : ℝ → ℝ} {rho tau lo : ℝ}
    (hrho : 0 < rho) (hClo : C lo = rho) :
    uniformSkillOutput C ((1 - tau) * rho) lo = tau * lo := by
  rw [uniformSkillOutput, hClo]
  field_simp
  ring

/-- The actual inverse on the original feasible production interval covers
exactly the affine-skill output interval, including its nonzero lower end. -/
theorem affineSkillOutputInverse_spec
    {C : ℝ → ℝ} {rho tau lo hi x : ℝ}
    (hrho : 0 < rho) (hlohi : lo ≤ hi)
    (hcont : ContinuousOn C (Icc lo hi)) (hmono : MonotoneOn C (Icc lo hi))
    (hClo : C lo = rho)
    (hx : x ∈ Icc (tau * lo) (uniformSkillOutput C ((1 - tau) * rho) hi)) :
    uniformSkillOutputInverse C ((1 - tau) * rho) lo hi x ∈ Icc lo hi ∧
      uniformSkillOutput C ((1 - tau) * rho)
        (uniformSkillOutputInverse C ((1 - tau) * rho) lo hi x) = x := by
  have himage : x ∈ uniformSkillOutput C ((1 - tau) * rho) '' Icc lo hi :=
    intermediate_value_Icc hlohi (affineSkillOutput_continuousOn hrho hlohi hcont hmono hClo)
      (by simpa only [affineSkillOutput_lower_endpoint hrho hClo] using hx)
  exact Function.invFunOn_pos himage

private noncomputable def affineSkillOutputOrderIso
    {C : ℝ → ℝ} {rho tau lo hi : ℝ}
    (hrho : 0 < rho) (htau : 0 ≤ tau) (htau_one : tau < 1)
    (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hcont : ContinuousOn C (Icc lo hi)) (hmono : StrictMonoOn C (Icc lo hi))
    (hClo : C lo = rho) :
    Icc lo hi ≃o Icc (tau * lo) (uniformSkillOutput C ((1 - tau) * rho) hi) where
  toFun a := ⟨uniformSkillOutput C ((1 - tau) * rho) a, by
    have h := (affineSkillOutput_strictMonoOn hrho htau htau_one hlo hlohi hmono hClo).monotoneOn
    constructor
    · simpa only [affineSkillOutput_lower_endpoint hrho hClo] using
        h ⟨le_rfl, hlohi⟩ a.property a.property.1
    · exact h a.property ⟨hlohi, le_rfl⟩ a.property.2⟩
  invFun x := ⟨uniformSkillOutputInverse C ((1 - tau) * rho) lo hi x,
    (affineSkillOutputInverse_spec hrho hlohi hcont hmono.monotoneOn hClo x.property).1⟩
  left_inv a := by
    apply Subtype.ext
    exact (affineSkillOutput_strictMonoOn hrho htau htau_one hlo hlohi hmono hClo).injOn.leftInvOn_invFunOn
      a.property
  right_inv x := by
    apply Subtype.ext
    exact (affineSkillOutputInverse_spec hrho hlohi hcont hmono.monotoneOn hClo x.property).2
  map_rel_iff' := by
    intro a b
    exact (affineSkillOutput_strictMonoOn hrho htau htau_one hlo hlohi hmono hClo).le_iff_le
      a.property b.property

theorem affineSkillOutputInverse_continuousOn
    {C : ℝ → ℝ} {rho tau lo hi : ℝ}
    (hrho : 0 < rho) (htau : 0 ≤ tau) (htau_one : tau < 1)
    (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hcont : ContinuousOn C (Icc lo hi)) (hmono : StrictMonoOn C (Icc lo hi))
    (hClo : C lo = rho) :
    ContinuousOn (uniformSkillOutputInverse C ((1 - tau) * rho) lo hi)
      (Icc (tau * lo) (uniformSkillOutput C ((1 - tau) * rho) hi)) := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_subtype_val.comp
    (affineSkillOutputOrderIso hrho htau htau_one hlo hlohi hcont hmono hClo).symm.continuous

theorem affineSkillOutputInverse_mem_Ioo
    {C : ℝ → ℝ} {rho tau lo hi x : ℝ}
    (hrho : 0 < rho) (htau : 0 ≤ tau) (htau_one : tau < 1)
    (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hcont : ContinuousOn C (Icc lo hi)) (hmono : StrictMonoOn C (Icc lo hi))
    (hClo : C lo = rho)
    (hx : x ∈ Ioo (tau * lo) (uniformSkillOutput C ((1 - tau) * rho) hi)) :
    uniformSkillOutputInverse C ((1 - tau) * rho) lo hi x ∈ Ioo lo hi ∧
      x < uniformSkillOutputInverse C ((1 - tau) * rho) lo hi x := by
  let A := uniformSkillOutputInverse C ((1 - tau) * rho) lo hi x
  have hs := affineSkillOutputInverse_spec hrho hlohi hcont hmono.monotoneOn hClo ⟨hx.1.le, hx.2.le⟩
  have hF := affineSkillOutput_strictMonoOn hrho htau htau_one hlo hlohi hmono hClo
  have hlow : lo < A := by
    apply (hF.lt_iff_lt ⟨le_rfl, hlohi⟩ hs.1).mp
    simpa only [affineSkillOutput_lower_endpoint hrho hClo, hs.2] using hx.1
  have hhigh : A < hi := by
    apply (hF.lt_iff_lt hs.1 ⟨hlohi, le_rfl⟩).mp
    simpa only [hs.2] using hx.2
  have hCpos : 0 < C A := by
    have h := hmono.monotoneOn ⟨le_rfl, hlohi⟩ hs.1 hs.1.1
    rw [hClo] at h
    exact hrho.trans_le h
  have hquot := div_pos (mul_pos (sub_pos.mpr htau_one) hrho) hCpos
  have heq : A * (1 - (1 - tau) * rho / C A) = x := hs.2
  exact ⟨⟨hlow, hhigh⟩, by nlinarith [mul_pos (hlo.trans hlow) hquot]⟩

theorem affineSkillOutputSlope_pos
    {C C' : ℝ → ℝ} {rho tau lo hi a : ℝ}
    (hrho : 0 < rho) (htau : 0 ≤ tau) (htau_one : tau < 1)
    (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hmono : StrictMonoOn C (Icc lo hi)) (hClo : C lo = rho)
    (ha : a ∈ Ioo lo hi) (hC' : HasDerivAt C (C' a) a) :
    0 < uniformSkillOutputSlope C C' ((1 - tau) * rho) a := by
  have h := uniformSkillOutputSlope_pos hrho hlo hlohi hmono hClo ha hC'
  have heq : uniformSkillOutputSlope C C' ((1 - tau) * rho) a =
      tau + (1 - tau) * uniformSkillOutputSlope C C' rho a := by
    unfold uniformSkillOutputSlope
    ring
  rw [heq]
  exact add_pos_of_nonneg_of_pos htau (mul_pos (sub_pos.mpr htau_one) h)

/-- The affine-skill inverse is convex on its actual output range, without
extending any cost condition below the least feasible cutoff production. -/
theorem affineSkillOutputInverse_convexOn
    {C : ℝ → ℝ} {rho tau lo hi : ℝ}
    (hrho : 0 < rho) (htau : 0 ≤ tau) (htau_one : tau < 1)
    (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hcont : ContinuousOn C (Icc lo hi)) (hmono : StrictMonoOn C (Icc lo hi))
    (hClo : C lo = rho) (hcostRatio : ConvexOn ℝ (Icc lo hi) (fun a => a / C a)) :
    ConvexOn ℝ (Icc (tau * lo) (uniformSkillOutput C ((1 - tau) * rho) hi))
      (uniformSkillOutputInverse C ((1 - tau) * rho) lo hi) := by
  have hs := fun x hx => affineSkillOutputInverse_spec (tau := tau) hrho hlohi hcont hmono.monotoneOn hClo
    (x := x) hx
  exact AppliedModelingLib.rightInverseOn_convexOn_of_strictMonoOn_concaveOn
    (convex_Icc _ _) (convex_Icc _ _)
    (uniformSkillOutput_concaveOn (mul_nonneg (sub_pos.mpr htau_one).le hrho.le)
      (convex_Icc _ _) hcostRatio)
    (affineSkillOutput_strictMonoOn hrho htau htau_one hlo hlohi hmono hClo)
    (fun x hx => (hs x hx).1) (fun x hx => (hs x hx).2)

/-- First and second derivatives of the constructed affine-skill inverse,
including their signs, follow from primitive cost derivatives and shape. -/
theorem affineSkillOutputInverse_derivatives
    {C C' C'' : ℝ → ℝ} {rho tau lo hi x : ℝ}
    (hrho : 0 < rho) (htau : 0 ≤ tau) (htau_one : tau < 1)
    (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hcont : ContinuousOn C (Icc lo hi)) (hmono : StrictMonoOn C (Icc lo hi))
    (hClo : C lo = rho)
    (hC' : ∀ a ∈ Ioo lo hi, HasDerivAt C (C' a) a)
    (hC'' : ∀ a ∈ Ioo lo hi, HasDerivAt C' (C'' a) a)
    (hcostRatio : ConvexOn ℝ (Icc lo hi) (fun a => a / C a))
    (hx : x ∈ Ioo (tau * lo) (uniformSkillOutput C ((1 - tau) * rho) hi)) :
    let r := (1 - tau) * rho
    HasDerivAt (uniformSkillOutputInverse C r lo hi)
        (uniformSkillOutputInverseSlope C C' r lo hi x) x ∧
      HasDerivAt (uniformSkillOutputInverseSlope C C' r lo hi)
        (uniformSkillOutputInverseCurvature C C' C'' r lo hi x) x ∧
      0 < uniformSkillOutputInverseSlope C C' r lo hi x ∧
      0 ≤ uniformSkillOutputInverseCurvature C C' C'' r lo hi x := by
  let r := (1 - tau) * rho
  let A := uniformSkillOutputInverse C r lo hi
  have hr : 0 < r := mul_pos (sub_pos.mpr htau_one) hrho
  have hA := (affineSkillOutputInverse_mem_Ioo hrho htau htau_one hlo hlohi hcont hmono hClo hx).1
  have hCpos (a : ℝ) (ha : a ∈ Icc lo hi) : 0 < C a := by
    have h := hmono.monotoneOn ⟨le_rfl, hlohi⟩ ha ha.1
    rw [hClo] at h
    exact hrho.trans_le h
  have hF' (a : ℝ) (ha : a ∈ Ioo lo hi) :=
    uniformSkillOutput_hasDerivAt (rho := r) (hC' a ha) (hCpos a ⟨ha.1.le, ha.2.le⟩).ne'
  have hFpos := affineSkillOutputSlope_pos hrho htau htau_one hlo hlohi hmono hClo hA (hC' _ hA)
  have hAcont : ContinuousAt A x :=
    (affineSkillOutputInverse_continuousOn hrho htau htau_one hlo hlohi hcont hmono hClo).continuousAt
      (Icc_mem_nhds hx.1 hx.2)
  have hright : ∀ᶠ y in 𝓝 x, uniformSkillOutput C r (A y) = y := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (affineSkillOutputInverse_spec hrho hlohi hcont hmono.monotoneOn hClo
      ⟨hy.1.le, hy.2.le⟩).2
  have hfirst := HasDerivAt.of_local_left_inverse hAcont (hF' (A x) hA) hFpos.ne' hright
  have hsecondF := uniformSkillOutputSlope_hasDerivAt (rho := r) (hC' (A x) hA)
    (hC'' (A x) hA) (hCpos (A x) ⟨hA.1.le, hA.2.le⟩).ne'
  have hsecond : HasDerivAt (uniformSkillOutputInverseSlope C C' r lo hi)
      (uniformSkillOutputInverseCurvature C C' C'' r lo hi x) x := by
    convert (hsecondF.comp x hfirst).inv hFpos.ne' using 1
    dsimp [uniformSkillOutputInverseCurvature, A]
    field_simp
  have hconc := (uniformSkillOutput_concaveOn hr.le (convex_Icc lo hi) hcostRatio).subset
    Ioo_subset_Icc_self (convex_Ioo lo hi)
  have hanti : AntitoneOn (uniformSkillOutputSlope C C' r) (Ioo lo hi) := by
    intro a ha b hb hab
    have h := hconc.antitoneOn_deriv (fun t ht => (hF' t ht).differentiableAt) ha hb hab
    simpa only [(hF' a ha).deriv, (hF' b hb).deriv] using h
  have hnonpos := hanti.derivWithin_nonpos (x := A x)
  rw [hsecondF.hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffWithinAt hA)] at hnonpos
  exact ⟨hfirst, hsecond, inv_pos.mpr hFpos,
    div_nonneg (neg_nonneg.mpr hnonpos) (pow_nonneg hFpos.le 3)⟩

/-- The affine skill quantile normalized to maximal skill one. -/
def affineSkillQuantile (tau t : ℝ) : ℝ := tau + (1 - tau) * t

theorem affineSkillQuantile_pos {tau t : ℝ}
    (htau : 0 ≤ tau) (htau_one : tau < 1) (ht : 0 < t) : 0 < affineSkillQuantile tau t :=
  add_pos_of_nonneg_of_pos htau (mul_pos (sub_pos.mpr htau_one) ht)

theorem affineSkillQuantile_strictMono {tau : ℝ} (htau : tau < 1) :
    StrictMono (affineSkillQuantile tau) := by
  intro s t hst
  dsimp [affineSkillQuantile]
  linarith [mul_lt_mul_of_pos_left hst (sub_pos.mpr htau)]

/-- Affine quantiles preserve the admitted score integral after normalization
by their interval width. Both the Jacobian and admission mass are explicit. -/
theorem affineSkillTailMean_eq_normalizedTailMean
    (R : ℝ → ℝ) {tau c : ℝ} (htau : tau < 1) (hc : c < 1) :
    (∫ t in c..1, R (affineSkillQuantile tau t)) / (1 - c) =
      (∫ s in (affineSkillQuantile tau c)..1, R s) / (1 - affineSkillQuantile tau c) := by
  have hk : 1 - tau ≠ 0 := (sub_pos.mpr htau).ne'
  have hn : 1 - c ≠ 0 := (sub_pos.mpr hc).ne'
  unfold affineSkillQuantile
  rw [intervalIntegral.integral_comp_add_mul R hk tau]
  have htop : tau + (1 - tau) * 1 = 1 := by ring
  have hmass : 1 - (tau + (1 - tau) * c) = (1 - tau) * (1 - c) := by ring
  rw [htop, hmass]
  simp only [smul_eq_mul]
  field_simp

/-- Positive ordered skill makes the source nonnegative-effort clamps
inactive at admitted types when baseline production is zero. -/
theorem sourceTwoLevelEffort_eq_inverse_of_positiveSkill
    {cost production f : ℝ → ℝ} {effortMax rho c t : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_zero : production 0 = 0)
    (ha : sourceScoreScale cost production effortMax rho c ∈ Ioc (0 : ℝ) (production effortMax))
    (hfc : 0 < f c) (hft : 0 < f t) (hct : f c ≤ f t) :
    sourceTwoLevelEffort cost production f effortMax rho c t =
      effortIntervalInverse production effortMax
        (sourceScoreScale cost production effortMax rho c * f c / f t) := by
  let z := sourceScoreScale cost production effortMax rho c * f c / f t
  have hz0 : 0 ≤ z := (div_pos (mul_pos ha.1 hfc) hft).le
  have hz : z ≤ production effortMax :=
    ((div_le_iff₀ hft).mpr (mul_le_mul_of_nonneg_left hct ha.1.le)).trans ha.2
  have hi := effortIntervalInverse_spec hmax hg
    (show z ∈ Icc (production 0) (production effortMax) by simpa only [hg_zero] using And.intro hz0 hz)
  unfold sourceTwoLevelEffort
  simp only [← mul_div_assoc, hg_zero]
  change max (effortIntervalInverse production effortMax (max z 0)) 0 =
    effortIntervalInverse production effortMax z
  rw [max_eq_left hz0, max_eq_left hi.1.1]

/-- Actual conditional residual production for affine measurable skill. -/
noncomputable def sourceAffineResidualUtility (cost production : ℝ → ℝ)
    (budget effortMax rho tau c : ℝ) : ℝ :=
  (∫ t in c..1, production (budget -
    sourceTwoLevelEffort cost production (affineSkillQuantile tau) effortMax rho c t)) / (1 - c)

/-- Affine skill produces exactly the same normalized admitted-score average
as the uniform integral, at the appropriately shifted score cutoff. -/
theorem sourceAffineResidualUtility_eq_uniformTailMean
    {cost production : ℝ → ℝ} {budget effortMax rho tau c : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_zero : production 0 = 0)
    (ha : sourceScoreScale cost production effortMax rho c ∈ Ioc (0 : ℝ) (production effortMax))
    (htau : 0 ≤ tau) (htau_one : tau < 1) (hc : c ∈ Ioo (0 : ℝ) 1) :
    sourceAffineResidualUtility cost production budget effortMax rho tau c =
      uniformSkillResidualMean production budget effortMax
        (sourceScoreScale cost production effortMax rho c * affineSkillQuantile tau c)
        (sourceScoreScale cost production effortMax rho c) := by
  let a := sourceScoreScale cost production effortMax rho c
  let x := a * affineSkillQuantile tau c
  let R := fun s => production (budget - effortIntervalInverse production effortMax (x / s))
  have hI : (∫ t in c..1, production (budget -
      sourceTwoLevelEffort cost production (affineSkillQuantile tau) effortMax rho c t)) =
      ∫ t in c..1, R (affineSkillQuantile tau t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc c 1 := by simpa only [uIcc_of_le hc.2.le] using ht
    dsimp only
    rw [sourceTwoLevelEffort_eq_inverse_of_positiveSkill hmax hg hg_zero ha
      (affineSkillQuantile_pos htau htau_one hc.1)
      (affineSkillQuantile_pos htau htau_one (hc.1.trans_le ht'.1))
      ((affineSkillQuantile_strictMono htau_one).monotone ht'.1)]
  unfold sourceAffineResidualUtility
  rw [hI, affineSkillTailMean_eq_normalizedTailMean R htau_one hc.2]
  have hcutoff : x / a = affineSkillQuantile tau c := by
    dsimp [x]
    rw [mul_comm, mul_div_assoc, div_self ha.1.ne', mul_one]
  change _ = (∫ t in (x / a)..1, R t) / (1 - x / a)
  rw [hcutoff]

/-- Actual conditional measurable output for an affine measurable-skill
quantile, defined from the source effort profile. -/
noncomputable def sourceAffineMeasurableUtility (cost production : ℝ → ℝ)
    (effortMax rho tau c : ℝ) : ℝ :=
  (∫ t in c..1,
    production (sourceTwoLevelEffort cost production (affineSkillQuantile tau) effortMax rho c t) *
      affineSkillQuantile tau t) / (1 - c)

theorem sourceAffineMeasurableUtility_eq_cutoffScore
    {cost production : ℝ → ℝ} {effortMax rho tau c : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_zero : production 0 = 0)
    (ha : sourceScoreScale cost production effortMax rho c ∈ Ioc (0 : ℝ) (production effortMax))
    (htau : 0 ≤ tau) (htau_one : tau < 1) (hc : c ∈ Ioo (0 : ℝ) 1) :
    sourceAffineMeasurableUtility cost production effortMax rho tau c =
      sourceScoreScale cost production effortMax rho c * affineSkillQuantile tau c := by
  let a := sourceScoreScale cost production effortMax rho c
  let f := affineSkillQuantile tau
  have hvalue (t : ℝ) (ht : t ∈ Icc c 1) :
      production (sourceTwoLevelEffort cost production f effortMax rho c t) * f t = a * f c := by
    have hfc := affineSkillQuantile_pos htau htau_one hc.1
    have hft := affineSkillQuantile_pos htau htau_one (hc.1.trans_le ht.1)
    have hct := (affineSkillQuantile_strictMono htau_one).monotone ht.1
    have hz : a * f c / f t ∈ Icc (production 0) (production effortMax) := by
      rw [hg_zero]
      exact ⟨(div_pos (mul_pos ha.1 hfc) hft).le,
        ((div_le_iff₀ hft).mpr (mul_le_mul_of_nonneg_left hct ha.1.le)).trans ha.2⟩
    rw [sourceTwoLevelEffort_eq_inverse_of_positiveSkill hmax hg hg_zero ha hfc hft hct]
    change production (effortIntervalInverse production effortMax (a * f c / f t)) * f t = a * f c
    rw [(effortIntervalInverse_spec hmax hg hz).2, div_mul_cancel₀ _ hft.ne']
  have hI : (∫ t in c..1,
      production (sourceTwoLevelEffort cost production f effortMax rho c t) * f t) =
      ∫ _t in c..1, a * f c := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hvalue t (by simpa only [uIcc_of_le hc.2.le] using ht)
  unfold sourceAffineMeasurableUtility
  rw [hI, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  rw [mul_comm, mul_div_assoc, div_self (sub_pos.mpr hc.2).ne', mul_one]

/-- Aggregate loss along the constructed affine-skill output curve is convex,
continuous through deterministic admission, and has a strictly positive
interior derivative. The hypotheses concern cost and production geometry. -/
theorem affineSkillLossCurve_properties
    {C C' C'' production productionDeriv productionSecondDeriv : ℝ → ℝ}
    {rho tau lo budget effortMax : ℝ}
    (hrho : 0 < rho) (htau : 0 ≤ tau) (htau_one : tau < 1)
    (hlo : 0 < lo) (hlohi : lo ≤ production effortMax)
    (hcont : ContinuousOn C (Icc lo (production effortMax)))
    (hmono : StrictMonoOn C (Icc lo (production effortMax))) (hClo : C lo = rho)
    (hC' : ∀ a ∈ Ioo lo (production effortMax), HasDerivAt C (C' a) a)
    (hC'' : ∀ a ∈ Ioo lo (production effortMax), HasDerivAt C' (C'' a) a)
    (hcostRatio : ConvexOn ℝ (Icc lo (production effortMax)) (fun a => a / C a))
    (hmax : 0 < effortMax) (hbudget : effortMax ≤ budget)
    (hg : ContinuousOn production (Icc 0 budget))
    (hg_mono : StrictMonoOn production (Icc 0 budget)) (hg_zero : production 0 = 0)
    (hg_conc : ConcaveOn ℝ (Ioo 0 budget) production)
    (hg_sq : ConcaveOn ℝ (Ioo 0 budget) (fun e => production e ^ 2))
    (hg' : ∀ e ∈ Ioo (0 : ℝ) budget, HasDerivAt production (productionDeriv e) e)
    (hg'' : ∀ e ∈ Ioo (0 : ℝ) budget,
      HasDerivAt productionDeriv (productionSecondDeriv e) e)
    (hg''_cont : ContinuousOn productionSecondDeriv (Ioo 0 budget)) :
    let r := (1 - tau) * rho
    let upper := uniformSkillOutput C r (production effortMax)
    let A := uniformSkillOutputInverse C r lo (production effortMax)
    let D := fun x => admittedLoss (productionLoss production budget effortMax) x (A x)
    ConvexOn ℝ (Ioo (tau * lo) upper) D ∧ ContinuousOn D (Ioc (tau * lo) upper) ∧
      ∀ x ∈ Ioo (tau * lo) upper, ∃ d, HasDerivAt D d x ∧ 0 < d := by
  let r := (1 - tau) * rho
  let hi := production effortMax
  let upper := uniformSkillOutput C r hi
  let A := uniformSkillOutputInverse C r lo hi
  let A₁ := uniformSkillOutputInverseSlope C C' r lo hi
  let L := productionLoss production budget effortMax
  let L₁ := productionLossSlope production productionDeriv budget effortMax
  let L₂ := productionLossCurvature production productionDeriv productionSecondDeriv budget effortMax
  have hlower : 0 ≤ tau * lo := mul_nonneg htau hlo.le
  have hA (x : ℝ) (hx : x ∈ Ioo (tau * lo) upper) :=
    affineSkillOutputInverse_derivatives hrho htau htau_one hlo hlohi hcont hmono hClo hC' hC'' hcostRatio hx
  have hfeas (x : ℝ) (hx : x ∈ Ioo (tau * lo) upper) : 0 < x ∧ x < A x ∧ A x < hi := by
    have h := affineSkillOutputInverse_mem_Ioo hrho htau htau_one hlo hlohi hcont hmono hClo hx
    exact ⟨hlower.trans_lt hx.1, h.2, h.1.2⟩
  have hL (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) hi) :=
    productionLoss_derivatives_and_curvature_of_squaredConcavity hmax hbudget hg hg_mono
      hg_zero hg_conc hg_sq hg' hg'' hz
  have hL₂ : ContinuousOn L₂ (Ioo 0 hi) := productionLossCurvature_continuousOn
    hmax.le hbudget hg hg_mono hg_zero hg_conc hg' hg'' hg''_cont
  have hconv : ConvexOn ℝ (Ioo (tau * lo) upper) (fun x => admittedLoss L x (A x)) :=
    admittedLoss_convexOn_curve (convex_Ioo _ _)
      (fun z hz => (hL z hz).1) (fun z hz => (hL z hz).2.1) hL₂
      (fun z hz => (hL z hz).2.2.1.le) (fun z hz => (hL z hz).2.2.2) hfeas
      (fun x hx => (hA x hx).1) (fun x hx => (hA x hx).2.1)
      (fun x hx => (hA x hx).2.2.1.le) (fun x hx => (hA x hx).2.2.2)
  have hfeasClosed (x : ℝ) (hx : x ∈ Ioc (tau * lo) upper) : x < A x ∧ A x ≤ hi := by
    have hs := affineSkillOutputInverse_spec hrho hlohi hcont hmono.monotoneOn hClo ⟨hx.1.le, hx.2⟩
    have hCpos : 0 < C (A x) := by
      have h := hmono.monotoneOn ⟨le_rfl, hlohi⟩ hs.1 hs.1.1
      rw [hClo] at h
      exact hrho.trans_le h
    have hquot := div_pos (mul_pos (sub_pos.mpr htau_one) hrho) hCpos
    have heq : A x * (1 - r / C (A x)) = x := hs.2
    exact ⟨by nlinarith [mul_pos (hlo.trans_le hs.1.1) hquot], hs.1.2⟩
  have hmonoE := hg_mono.mono (show Icc (0 : ℝ) effortMax ⊆ Icc 0 budget from
    fun _ he => ⟨he.1, he.2.trans hbudget⟩)
  have hLcont := productionLoss_continuousOn hmax.le hbudget hg hmonoE hg_zero
  have hDcont := admittedLoss_continuousOn_curve hLcont
    ((affineSkillOutputInverse_continuousOn hrho htau htau_one hlo hlohi hcont hmono hClo).mono
      Ioc_subset_Icc_self) hfeasClosed hlower
  refine ⟨hconv, hDcont, ?_⟩
  intro x hx
  have hL₁cont : ContinuousOn L₁ (Ioo 0 hi) :=
    fun z hz => (hL z hz).2.1.continuousAt.continuousWithinAt
  have hd := admittedLoss_hasDerivAt_curve (fun z hz => (hL z hz).1) hL₁cont
    (hfeas x hx).1 (hfeas x hx).2.1 (hfeas x hx).2.2 (hA x hx).1
  have hspan : Icc x (A x) ⊆ Ioo 0 hi := fun z hz =>
    ⟨(hfeas x hx).1.trans_le hz.1, hz.2.trans_lt (hfeas x hx).2.2⟩
  have hkcont : ContinuousOn (lossSlope L₁) (Icc x (A x)) :=
    (hL₁cont.mono hspan).div continuousOn_id (fun z hz => (hspan hz).1.ne')
  exact ⟨admittedLossCurveSlope (lossSlope L₁) A A₁ x, hd,
    admittedLossCurveSlope_pos (hfeas x hx).1 (hfeas x hx).2.1 hkcont
      (fun z hz => div_pos (hL z (hspan hz)).2.2.1 (hspan hz).1) (hA x hx).2.2.1.le⟩

/-- Effort cost and technology determine the feasible capacity-production
interval and the exact endpoint costs. -/
theorem primitiveScoreCost_capacity_interval
    {cost production : ℝ → ℝ} {effortMax rho : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1) (hmax : 0 < effortMax)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : production 0 = 0) :
    let C := costInScore cost (effortIntervalInverse production effortMax)
    let lo := production (effortIntervalInverse cost effortMax rho)
    0 < lo ∧ lo < production effortMax ∧
      ContinuousOn C (Icc 0 (production effortMax)) ∧
      StrictMonoOn C (Icc 0 (production effortMax)) ∧ C lo = rho ∧ C (production effortMax) = 1 := by
  have hq := effortIntervalInverse_mem_Ioo hmax.le hcost hcost_mono
    (show rho ∈ Ioo (cost 0) (cost effortMax) by
      simpa only [hcost_zero, hcost_max] using And.intro hrho hrho_one)
  have hlo : 0 < production (effortIntervalInverse cost effortMax rho) := by
    simpa only [hg_zero] using hg_mono ⟨le_rfl, hmax.le⟩ ⟨hq.1.le, hq.2.le⟩ hq.1
  have hC := primitiveScoreCost_properties hmax.le hcost hcost_mono hcost_zero hcost_max
    hg hg_mono hg_zero
  refine ⟨hlo, hg_mono ⟨hq.1.le, hq.2.le⟩ ⟨hmax.le, le_rfl⟩ hq.2,
    hC.1, hC.2.1, ?_, hC.2.2.2⟩
  have hleft : effortIntervalInverse production effortMax
      (production (effortIntervalInverse cost effortMax rho)) = effortIntervalInverse cost effortMax rho :=
    hg_mono.injOn.leftInvOn_invFunOn ⟨hq.1.le, hq.2.le⟩
  unfold costInScore
  rw [hleft]
  exact (effortIntervalInverse_spec hmax.le hcost
    (show rho ∈ Icc (cost 0) (cost effortMax) by
      simpa only [hcost_zero, hcost_max] using And.intro hrho.le hrho_one.le)).2

/-- Interior cost-in-score derivatives come from the actual cost and
technology derivatives; strict positivity of marginal technology is derived. -/
theorem primitiveScoreCost_derivatives_of_effortPrimitives
    {cost costDeriv costSecondDeriv production productionDeriv productionSecondDeriv : ℝ → ℝ}
    {budget effortMax : ℝ}
    (hmax : 0 < effortMax) (hbudget : effortMax ≤ budget)
    (hp' : ∀ e ∈ Ioo (0 : ℝ) effortMax, HasDerivAt cost (costDeriv e) e)
    (hp'' : ∀ e ∈ Ioo (0 : ℝ) effortMax, HasDerivAt costDeriv (costSecondDeriv e) e)
    (hg : ContinuousOn production (Icc 0 budget))
    (hg_mono : StrictMonoOn production (Icc 0 budget)) (hg_zero : production 0 = 0)
    (hg_conc : ConcaveOn ℝ (Ioo 0 budget) production)
    (hg' : ∀ e ∈ Ioo (0 : ℝ) budget, HasDerivAt production (productionDeriv e) e)
    (hg'' : ∀ e ∈ Ioo (0 : ℝ) budget,
      HasDerivAt productionDeriv (productionSecondDeriv e) e) :
    ∀ a ∈ Ioo (0 : ℝ) (production effortMax),
      HasDerivAt (costInScore cost (effortIntervalInverse production effortMax))
        (primitiveScoreCostSlope costDeriv production productionDeriv effortMax a) a ∧
      HasDerivAt (primitiveScoreCostSlope costDeriv production productionDeriv effortMax)
        (primitiveScoreCostCurvature costDeriv costSecondDeriv production productionDeriv
          productionSecondDeriv effortMax a) a := by
  have hsub : Icc (0 : ℝ) effortMax ⊆ Icc 0 budget := fun _ he => ⟨he.1, he.2.trans hbudget⟩
  have hgE := hg.mono hsub
  have hmonoE := hg_mono.mono hsub
  intro a ha
  have ha' : a ∈ Ioo (production 0) (production effortMax) := by simpa only [hg_zero] using ha
  have he := effortIntervalInverse_mem_Ioo hmax.le hgE hmonoE ha'
  have heB : effortIntervalInverse production effortMax a ∈ Ioo (0 : ℝ) budget :=
    ⟨he.1, he.2.trans_le hbudget⟩
  have hgp := (productionDeriv_pos_of_strictMono_concave hg_mono hg_conc heB (hg' _ heB)).ne'
  exact ⟨primitiveScoreCost_hasDerivAt hmax.le hgE hmonoE ha' (hp' _ he) (hg' _ heB) hgp,
    primitiveScoreCostSlope_hasDerivAt hmax.le hgE hmonoE ha' (hp'' _ he) (hg' _ heB) (hg'' _ heB) hgp⟩

/-- Every source affine-skill policy is represented by the constructed inverse
on its exact feasible output range. Interior cutoffs give interior outputs. -/
theorem affineSkillOutputInverse_at_sourceCutoff
    {cost production : ℝ → ℝ} {effortMax rho tau c : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1) (htau : 0 ≤ tau) (htau_one : tau < 1)
    (hmax : 0 < effortMax)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : production 0 = 0)
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
    let a := sourceScoreScale cost production effortMax rho c
    let C := costInScore cost (effortIntervalInverse production effortMax)
    let lo := production (effortIntervalInverse cost effortMax rho)
    let r := (1 - tau) * rho
    let x := a * affineSkillQuantile tau c
    a ∈ Ioc (0 : ℝ) (production effortMax) ∧
      x ∈ Ioc (tau * lo) (uniformSkillOutput C r (production effortMax)) ∧
      uniformSkillOutputInverse C r lo (production effortMax) x = a ∧
      (c < 1 - rho → x < uniformSkillOutput C r (production effortMax)) := by
  let a := sourceScoreScale cost production effortMax rho c
  let C := costInScore cost (effortIntervalInverse production effortMax)
  let lo := production (effortIntervalInverse cost effortMax rho)
  let r := (1 - tau) * rho
  let x := a * affineSkillQuantile tau c
  obtain ⟨hlo, hlohi, hCcont, hCmono, hClo, hChi⟩ := primitiveScoreCost_capacity_interval
    hrho hrho_one hmax hcost hcost_mono hcost_zero hcost_max hg hg_mono hg_zero
  change C lo = rho at hClo
  change C (production effortMax) = 1 at hChi
  have ha := (uniformSkillOutputInverse_at_sourceCutoff hrho hrho_one hmax hcost hcost_mono
    hcost_zero hcost_max hg hg_mono hg_zero hc).1
  have hden : 0 < 1 - c := by linarith [hc.2]
  have he := effortIntervalInverse_spec hmax.le hcost
    (show rho / (1 - c) ∈ Icc (cost 0) (cost effortMax) by
      rw [hcost_zero, hcost_max]
      exact ⟨(div_pos hrho hden).le, (div_le_one hden).mpr (by linarith [hc.2])⟩)
  have hCa : C a = rho / (1 - c) := by
    have hleft : effortIntervalInverse production effortMax
        (production (effortIntervalInverse cost effortMax (rho / (1 - c)))) =
          effortIntervalInverse cost effortMax (rho / (1 - c)) :=
      hg_mono.injOn.leftInvOn_invFunOn he.1
    change cost (effortIntervalInverse production effortMax
      (production (effortIntervalInverse cost effortMax (rho / (1 - c))))) = _
    rw [hleft]
    exact he.2
  have hloa : lo ≤ a := by
    apply (hCmono.le_iff_le ⟨hlo.le, hlohi.le⟩ ⟨ha.1.le, ha.2⟩).mp
    change C lo ≤ C a
    rw [hClo, hCa]
    apply (le_div_iff₀ hden).mpr
    nlinarith [hc.1]
  have hsub : Icc lo (production effortMax) ⊆ Icc 0 (production effortMax) :=
    fun _ hy => ⟨hlo.le.trans hy.1, hy.2⟩
  have hF := affineSkillOutput_strictMonoOn hrho htau htau_one hlo hlohi.le (hCmono.mono hsub) hClo
  have hFx : uniformSkillOutput C r a = x := by
    dsimp [r, x, uniformSkillOutput]
    rw [hCa]
    unfold affineSkillQuantile
    field_simp
    ring
  have hleft : uniformSkillOutputInverse C r lo (production effortMax)
      (uniformSkillOutput C r a) = a := hF.injOn.leftInvOn_invFunOn ⟨hloa, ha.2⟩
  rw [hFx] at hleft
  have hxlow : tau * lo < x := by
    have h1 := mul_le_mul_of_nonneg_left hloa htau
    have h2 := mul_pos (mul_pos ha.1 (sub_pos.mpr htau_one)) hc.1
    dsimp [x, affineSkillQuantile]
    nlinarith
  have hxhigh : x ≤ uniformSkillOutput C r (production effortMax) := by
    rw [← hFx]
    exact hF.monotoneOn ⟨hloa, ha.2⟩ ⟨hlohi.le, le_rfl⟩ ha.2
  refine ⟨ha, ⟨hxlow, hxhigh⟩, hleft, ?_⟩
  intro hcstrict
  have hahigh : a < production effortMax := by
    apply (hCmono.lt_iff_lt ⟨ha.1.le, ha.2⟩ ⟨hlo.le.trans hlohi.le, le_rfl⟩).mp
    change C a < C (production effortMax)
    rw [hCa, hChi]
    exact (div_lt_one hden).mpr (by linarith)
  change x < uniformSkillOutput C r (production effortMax)
  rw [← hFx]
  exact hF ⟨hloa, ha.2⟩ ⟨hlohi.le, le_rfl⟩ hahigh

/-- Every interior cutoff is globally supported for a nondegenerate affine
measurable-skill quantile. The primitive production and cost conditions are
imposed only on the original feasible range, and all compared utilities are
the actual conditional integrals of the source effort profile. -/
theorem sourceAffineWeightedUtility_exists_optimal_weight_of_effortPrimitives
    {cost costDeriv costSecondDeriv production productionDeriv productionSecondDeriv : ℝ → ℝ}
    {budget effortMax rho tau mean c : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1) (htau : 0 ≤ tau) (htau_one : tau < 1)
    (hmax : 0 < effortMax) (hbudget : effortMax ≤ budget)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hp' : ∀ e ∈ Ioo (0 : ℝ) effortMax, HasDerivAt cost (costDeriv e) e)
    (hp'' : ∀ e ∈ Ioo (0 : ℝ) effortMax, HasDerivAt costDeriv (costSecondDeriv e) e)
    (hg : ContinuousOn production (Icc 0 budget))
    (hg_mono : StrictMonoOn production (Icc 0 budget)) (hg_zero : production 0 = 0)
    (hg_conc : ConcaveOn ℝ (Ioo 0 budget) production)
    (hg_sq : ConcaveOn ℝ (Ioo 0 budget) (fun e => production e ^ 2))
    (hg' : ∀ e ∈ Ioo (0 : ℝ) budget, HasDerivAt production (productionDeriv e) e)
    (hg'' : ∀ e ∈ Ioo (0 : ℝ) budget,
      HasDerivAt productionDeriv (productionSecondDeriv e) e)
    (hg''_cont : ContinuousOn productionSecondDeriv (Ioo 0 budget))
    (hcostRatio : ConvexOn ℝ
      (Icc (production (effortIntervalInverse cost effortMax rho)) (production effortMax))
      (fun a => a / cost (effortIntervalInverse production effortMax a)))
    (hmean : 0 < mean) (hc : c ∈ Ioo (0 : ℝ) (1 - rho)) :
    ∃ beta ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioc (0 : ℝ) (1 - rho),
      weightedPrivateUtility beta (sourceAffineMeasurableUtility cost production effortMax rho tau)
        (fun t => mean * sourceAffineResidualUtility cost production budget effortMax rho tau t) d ≤
      weightedPrivateUtility beta (sourceAffineMeasurableUtility cost production effortMax rho tau)
        (fun t => mean * sourceAffineResidualUtility cost production budget effortMax rho tau t) c := by
  have hsubset : Icc (0 : ℝ) effortMax ⊆ Icc 0 budget :=
    fun _ he => ⟨he.1, he.2.trans hbudget⟩
  have hgE := hg.mono hsubset
  have hmonoE := hg_mono.mono hsubset
  let C := costInScore cost (effortIntervalInverse production effortMax)
  let C₁ := primitiveScoreCostSlope costDeriv production productionDeriv effortMax
  let C₂ := primitiveScoreCostCurvature costDeriv costSecondDeriv production productionDeriv
    productionSecondDeriv effortMax
  let lo := production (effortIntervalInverse cost effortMax rho)
  let r := (1 - tau) * rho
  let A := uniformSkillOutputInverse C r lo (production effortMax)
  let upper := uniformSkillOutput C r (production effortMax)
  let L := productionLoss production budget effortMax
  let U := fun x => production budget - admittedLoss L x (A x)
  let a := sourceScoreScale cost production effortMax rho
  let x := fun d => a d * affineSkillQuantile tau d
  obtain ⟨hlo, hlohi, hCcont, hCmono, hClo, _⟩ := primitiveScoreCost_capacity_interval
    hrho hrho_one hmax hcost hcost_mono hcost_zero hcost_max hgE hmonoE hg_zero
  have hCsub : Icc lo (production effortMax) ⊆ Icc 0 (production effortMax) :=
    fun _ ha => ⟨hlo.le.trans ha.1, ha.2⟩
  have hCderiv := primitiveScoreCost_derivatives_of_effortPrimitives hmax hbudget hp' hp''
    hg hg_mono hg_zero hg_conc hg' hg''
  have hCfirst (z : ℝ) (hz : z ∈ Ioo lo (production effortMax)) : HasDerivAt C (C₁ z) z :=
    (hCderiv z ⟨hlo.trans hz.1, hz.2⟩).1
  have hCsecond (z : ℝ) (hz : z ∈ Ioo lo (production effortMax)) : HasDerivAt C₁ (C₂ z) z :=
    (hCderiv z ⟨hlo.trans hz.1, hz.2⟩).2
  have hshape := affineSkillLossCurve_properties hrho htau htau_one hlo hlohi.le
    (hCcont.mono hCsub) (hCmono.mono hCsub) hClo hCfirst hCsecond hcostRatio
    hmax hbudget hg hg_mono hg_zero hg_conc hg_sq hg' hg'' hg''_cont
  have hUconc : ConcaveOn ℝ (Ioo (tau * lo) upper) U :=
    (concaveOn_const _ (convex_Ioo _ _)).sub hshape.1
  have hUcont : ContinuousOn U (Ioc (tau * lo) upper) := continuousOn_const.sub hshape.2.1
  have hpolicy (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1 - rho)) :=
    affineSkillOutputInverse_at_sourceCutoff hrho hrho_one htau htau_one hmax
      hcost hcost_mono hcost_zero hcost_max hgE hmonoE hg_zero hd
  have hc' : c ∈ Ioc (0 : ℝ) (1 - rho) := ⟨hc.1, hc.2.le⟩
  have htarget : x c ∈ Ioo (tau * lo) upper :=
    ⟨(hpolicy c hc').2.1.1, (hpolicy c hc').2.2.2 hc.2⟩
  obtain ⟨d, hd, hdpos⟩ := hshape.2.2 (x c) htarget
  obtain ⟨beta, hbeta, hopt⟩ := exists_supporting_weight_of_concave_residual
    (show (0 : ℝ) < 1 by norm_num) hmean htarget hUconc hUcont
    (hd.const_sub (production budget)) (neg_neg_of_pos hdpos)
  have hM (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1 - rho)) :=
    sourceAffineMeasurableUtility_eq_cutoffScore hmax.le hgE hg_zero (hpolicy d hd).1
      htau htau_one (show d ∈ Ioo (0 : ℝ) 1 from ⟨hd.1, by linarith [hd.2]⟩)
  have hR (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1 - rho)) :
      sourceAffineResidualUtility cost production budget effortMax rho tau d = U (x d) := by
    have hd1 : d < 1 := by linarith [hd.2]
    have hxpos : 0 < x d := (mul_nonneg htau hlo.le).trans_lt (hpolicy d hd).2.1.1
    have hf1 : affineSkillQuantile tau 1 = 1 := by unfold affineSkillQuantile; ring
    have hf : affineSkillQuantile tau d < 1 := by
      rw [← hf1]
      exact affineSkillQuantile_strictMono htau_one hd1
    have hxa : x d < a d := by
      have h := mul_lt_mul_of_pos_left hf (hpolicy d hd).1.1
      simpa only [mul_one] using h
    rw [sourceAffineResidualUtility_eq_uniformTailMean hmax.le hgE hg_zero (hpolicy d hd).1
      htau htau_one ⟨hd.1, hd1⟩,
      uniformSkillResidualMean_eq_sub_admittedLoss hmax.le hbudget hg hmonoE hg_zero
        hxpos hxa (hpolicy d hd).1.2]
    change production budget - admittedLoss L (x d) (a d) =
      production budget - admittedLoss L (x d) (A (x d))
    have hA : A (x d) = a d := (hpolicy d hd).2.2.1
    rw [hA]
  refine ⟨beta, hbeta, ?_⟩
  intro d hd
  have h := hopt (x d) (hpolicy d hd).2.1
  simp only [weightedPrivateUtility, one_mul] at h ⊢
  rw [hM d hd, hM c hc', hR d hd, hR c hc']
  exact h

/-- Multiplying all measurable skills by the same nonzero unit conversion
does not change the source effort profile, which depends only on skill ratios. -/
theorem sourceTwoLevelEffort_skill_scale (cost production f : ℝ → ℝ)
    (effortMax rho c t : ℝ) {scale : ℝ} (hscale : scale ≠ 0) :
    sourceTwoLevelEffort cost production (fun u => scale * f u) effortMax rho c t =
      sourceTwoLevelEffort cost production f effortMax rho c t := by
  unfold sourceTwoLevelEffort
  rw [mul_div_mul_left _ _ hscale]

/-- Continuity and boundedness of the actual effort profile on the admitted
tail follow from positive continuous increasing skill and the compact inverse. -/
theorem sourceTwoLevelEffort_continuousOn_and_mem_of_positiveSkill
    {cost production f : ℝ → ℝ} {effortMax rho c : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : production 0 = 0)
    (ha : sourceScoreScale cost production effortMax rho c ∈ Ioc (0 : ℝ) (production effortMax))
    (hc : c ≤ 1) (hf : ContinuousOn f (Icc c 1)) (hf_mono : MonotoneOn f (Icc c 1))
    (hfc : 0 < f c) :
    ContinuousOn (sourceTwoLevelEffort cost production f effortMax rho c) (Icc c 1) ∧
      ∀ t ∈ Icc c 1, sourceTwoLevelEffort cost production f effortMax rho c t ∈ Icc 0 effortMax := by
  let a := sourceScoreScale cost production effortMax rho c
  have hct (t : ℝ) (ht : t ∈ Icc c 1) : f c ≤ f t := hf_mono ⟨le_rfl, hc⟩ ht ht.1
  have hft (t : ℝ) (ht : t ∈ Icc c 1) : 0 < f t := hfc.trans_le (hct t ht)
  have hs (t : ℝ) (ht : t ∈ Icc c 1) : a * f c / f t ∈ Icc (production 0) (production effortMax) := by
    rw [hg_zero]
    exact ⟨(div_pos (mul_pos ha.1 hfc) (hft t ht)).le,
      ((div_le_iff₀ (hft t ht)).mpr (mul_le_mul_of_nonneg_left (hct t ht) ha.1.le)).trans ha.2⟩
  have hscont : ContinuousOn (fun t => a * f c / f t) (Icc c 1) :=
    continuousOn_const.div hf (fun t ht => (hft t ht).ne')
  have hi := (effortIntervalInverse_continuousOn hmax hg hg_mono).comp hscont hs
  have heq (t : ℝ) (ht : t ∈ Icc c 1) :=
    sourceTwoLevelEffort_eq_inverse_of_positiveSkill hmax hg hg_zero ha hfc (hft t ht) (hct t ht)
  refine ⟨hi.congr heq, ?_⟩
  intro t ht
  rw [heq t ht]
  exact (effortIntervalInverse_spec hmax hg (hs t ht)).1

/-- Conditional school utility for an arbitrary measurable-skill quantile,
under the fixed independent rank, lottery, and unmeasurable-skill population. -/
noncomputable def sourceSkillConditionalSchoolUtility
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (skill : α → ℝ)
    (cost production f : ℝ → ℝ) (budget effortMax rho beta c : ℝ) : ℝ :=
  ∫ z : (ℝ × ℝ) × α,
    beta * (production (sourceTwoLevelEffort cost production f effortMax rho c z.1.1) * f z.1.1) +
    (1 - beta) * (production (budget -
      sourceTwoLevelEffort cost production f effortMax rho c z.1.1) * skill z.2)
    ∂ProbabilityTheory.cond (independentSkillPopulation μ) (twoLevelAdmissionEvent rho c)

/-- For a scaled affine skill quantile, the genuine population expectation is
the scaled measurable component plus the independent-skill residual component.
The scale cancels in effort, but is retained in measurable production. -/
theorem sourceSkillConditionalSchoolUtility_eq_scaled_affine
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {skill : α → ℝ} (hskill : Integrable skill μ)
    {cost production : ℝ → ℝ} {budget effortMax rho tau scale beta c : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1) (htau : 0 ≤ tau) (htau_one : tau < 1)
    (hscale : 0 < scale) (hmax : 0 < effortMax) (hbudget : effortMax ≤ budget)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 budget))
    (hg_mono : StrictMonoOn production (Icc 0 budget)) (hg_zero : production 0 = 0)
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
    sourceSkillConditionalSchoolUtility μ skill cost production
      (fun t => scale * affineSkillQuantile tau t) budget effortMax rho beta c =
      weightedPrivateUtility beta
        (fun t => scale * sourceAffineMeasurableUtility cost production effortMax rho tau t)
        (fun t => (∫ u, skill u ∂μ) *
          sourceAffineResidualUtility cost production budget effortMax rho tau t) c := by
  have hc1 : c < 1 := by linarith [hc.2]
  have hsubset : Icc (0 : ℝ) effortMax ⊆ Icc 0 budget :=
    fun _ he => ⟨he.1, he.2.trans hbudget⟩
  have hgE := hg.mono hsubset
  have hmonoE := hg_mono.mono hsubset
  have ha := (affineSkillOutputInverse_at_sourceCutoff hrho hrho_one htau htau_one hmax
    hcost hcost_mono hcost_zero hcost_max hgE hmonoE hg_zero hc).1
  have hf : ContinuousOn (affineSkillQuantile tau) (Icc c 1) :=
    continuousOn_const.add (continuousOn_const.mul continuousOn_id)
  have he := sourceTwoLevelEffort_continuousOn_and_mem_of_positiveSkill hmax.le hgE hmonoE
    hg_zero ha hc1.le hf ((affineSkillQuantile_strictMono htau_one).monotone.monotoneOn _)
    (affineSkillQuantile_pos htau htau_one hc.1)
  let M := fun t => production
    (sourceTwoLevelEffort cost production (affineSkillQuantile tau) effortMax rho c t) *
      affineSkillQuantile tau t
  let R := fun t => production (budget -
    sourceTwoLevelEffort cost production (affineSkillQuantile tau) effortMax rho c t)
  have hMcont : ContinuousOn M (Icc c 1) := (hgE.comp he.1 he.2).mul hf
  have hRcont : ContinuousOn R (Icc c 1) := by
    apply hg.comp (continuousOn_const.sub he.1)
    intro t ht
    exact ⟨by linarith [(he.2 t ht).2], by linarith [(he.2 t ht).1]⟩
  have hM := independentSkillPopulation_conditional_utility μ hrho hc
    (hMcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (integrable_const (1 : ℝ) : Integrable (fun _ : α => (1 : ℝ)) μ)
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul, one_mul] at hM
  have hR := independentSkillPopulation_conditional_utility μ hrho hc
    (hRcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self) hskill
  have heq : (fun z : (ℝ × ℝ) × α =>
      beta * (production (sourceTwoLevelEffort cost production
        (fun t => scale * affineSkillQuantile tau t) effortMax rho c z.1.1) *
          (scale * affineSkillQuantile tau z.1.1)) +
      (1 - beta) * (production (budget - sourceTwoLevelEffort cost production
        (fun t => scale * affineSkillQuantile tau t) effortMax rho c z.1.1) * skill z.2)) =
      (fun z : (ℝ × ℝ) × α => (beta * scale) * M z.1.1 + (1 - beta) * (R z.1.1 * skill z.2)) := by
    funext z
    rw [sourceTwoLevelEffort_skill_scale cost production _ _ _ _ _ hscale.ne']
    dsimp [M, R]
    ring
  unfold sourceSkillConditionalSchoolUtility
  rw [heq, integral_add (hM.1.const_mul (beta * scale)) (hR.1.const_mul (1 - beta)),
    integral_const_mul, integral_const_mul, hM.2, hR.2]
  change _ = beta * (scale * ((∫ t in c..1, M t) / (1 - c))) +
    (1 - beta) * ((∫ u, skill u ∂μ) * ((∫ t in c..1, R t) / (1 - c)))
  ring

/-- Every interior two-level cutoff is optimal for some interior school
weight when measurable skill is uniform on any nondegenerate nonnegative
interval. The population law is fixed across policies, each conditioned on
its actual admission event. Skill normalization changes neither effort nor the primitive cost
and production conditions, and no bound on skill dispersion is imposed. -/
theorem sourceSkillConditionalSchoolUtility_exists_optimal_weight_of_affineSkill
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {skill : α → ℝ} (hskill : Integrable skill μ) (hmean : 0 < ∫ u, skill u ∂μ)
    {cost costDeriv costSecondDeriv production productionDeriv productionSecondDeriv : ℝ → ℝ}
    {budget effortMax rho lowerSkill skillWidth c : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1)
    (hlower : 0 ≤ lowerSkill) (hwidth : 0 < skillWidth)
    (hmax : 0 < effortMax) (hbudget : effortMax ≤ budget)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hp' : ∀ e ∈ Ioo (0 : ℝ) effortMax, HasDerivAt cost (costDeriv e) e)
    (hp'' : ∀ e ∈ Ioo (0 : ℝ) effortMax, HasDerivAt costDeriv (costSecondDeriv e) e)
    (hg : ContinuousOn production (Icc 0 budget))
    (hg_mono : StrictMonoOn production (Icc 0 budget)) (hg_zero : production 0 = 0)
    (hg_conc : ConcaveOn ℝ (Ioo 0 budget) production)
    (hg_sq : ConcaveOn ℝ (Ioo 0 budget) (fun e => production e ^ 2))
    (hg' : ∀ e ∈ Ioo (0 : ℝ) budget, HasDerivAt production (productionDeriv e) e)
    (hg'' : ∀ e ∈ Ioo (0 : ℝ) budget,
      HasDerivAt productionDeriv (productionSecondDeriv e) e)
    (hg''_cont : ContinuousOn productionSecondDeriv (Ioo 0 budget))
    (hcostRatio : ConvexOn ℝ
      (Icc (production (effortIntervalInverse cost effortMax rho)) (production effortMax))
      (fun a => a / cost (effortIntervalInverse production effortMax a)))
    (hc : c ∈ Ioo (0 : ℝ) (1 - rho)) :
    ∃ beta ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioc (0 : ℝ) (1 - rho),
      sourceSkillConditionalSchoolUtility μ skill cost production
        (fun t => lowerSkill + skillWidth * t) budget effortMax rho beta d ≤
      sourceSkillConditionalSchoolUtility μ skill cost production
        (fun t => lowerSkill + skillWidth * t) budget effortMax rho beta c := by
  let scale := lowerSkill + skillWidth
  let tau := lowerSkill / scale
  have hscale : 0 < scale := by dsimp [scale]; linarith
  have htau : 0 ≤ tau := div_nonneg hlower hscale.le
  have htau_one : tau < 1 := (div_lt_one hscale).mpr (by dsimp [scale]; linarith)
  have hnorm : (fun t => scale * affineSkillQuantile tau t) =
      (fun t => lowerSkill + skillWidth * t) := by
    funext t
    dsimp [affineSkillQuantile, tau]
    field_simp
    dsimp [scale]
    ring
  obtain ⟨beta, hbeta, hopt⟩ := sourceAffineWeightedUtility_exists_optimal_weight_of_effortPrimitives
    hrho hrho_one htau htau_one hmax hbudget hcost hcost_mono hcost_zero hcost_max hp' hp''
    hg hg_mono hg_zero hg_conc hg_sq hg' hg'' hg''_cont hcostRatio (div_pos hmean hscale) hc
  have hbridge (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1 - rho)) :
      sourceSkillConditionalSchoolUtility μ skill cost production
        (fun t => lowerSkill + skillWidth * t) budget effortMax rho beta d =
      scale * weightedPrivateUtility beta (sourceAffineMeasurableUtility cost production effortMax rho tau)
        (fun t => ((∫ u, skill u ∂μ) / scale) *
          sourceAffineResidualUtility cost production budget effortMax rho tau t) d := by
    rw [← hnorm, sourceSkillConditionalSchoolUtility_eq_scaled_affine μ hskill hrho hrho_one
      htau htau_one hscale hmax hbudget hcost hcost_mono hcost_zero hcost_max hg hg_mono hg_zero hd]
    unfold weightedPrivateUtility
    field_simp
  refine ⟨beta, hbeta, ?_⟩
  intro d hd
  rw [hbridge d hd, hbridge c ⟨hc.1, hc.2.le⟩]
  exact mul_le_mul_of_nonneg_left (hopt d hd) hscale.le

/-- Every increasing affine skill quantile with nonnegative lower skill is
positive and log-concave on positive ranks; zero skill at rank zero is allowed. -/
theorem affineSkill_logConcave {lowerSkill skillWidth : ℝ}
    (hlower : 0 ≤ lowerSkill) (hwidth : 0 < skillWidth) :
    ConcaveOn ℝ (Ioc (0 : ℝ) 1) (fun t => Real.log (lowerSkill + skillWidth * t)) := by
  have hpos (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : 0 < lowerSkill + skillWidth * t :=
    add_pos_of_nonneg_of_pos hlower (mul_pos hwidth ht.1)
  refine ⟨convex_Ioc _ _, ?_⟩
  intro a ha b hb u v hu hv huv
  have h := strictConcaveOn_log_Ioi.concaveOn.2 (hpos a ha) (hpos b hb) hu hv huv
  have hlin : lowerSkill + skillWidth * (u * a + v * b) =
      u * (lowerSkill + skillWidth * a) + v * (lowerSkill + skillWidth * b) := by
    nlinarith only [congrArg (fun t => t * lowerSkill) huv]
  simpa only [smul_eq_mul, hlin] using h

/-- One sufficient primitive package repairs both the two-level applicant-
welfare monotonicity claim and the every-interior-cutoff school-optimality
claim. Measurable skill is uniform on a nondegenerate nonnegative interval;
geometric concavity of cost in produced-score units supplies both cost-shape
requirements. This common condition is sufficient, not asserted necessary. -/
theorem sourceAffine_welfare_and_weighted_optimality_of_geometricCost
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {skill : α → ℝ} (hskill : Integrable skill μ) (hmean : 0 < ∫ u, skill u ∂μ)
    {cost costDeriv costSecondDeriv production productionDeriv productionSecondDeriv : ℝ → ℝ}
    {budget effortMax rho lowerSkill skillWidth : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1)
    (hlower : 0 ≤ lowerSkill) (hwidth : 0 < skillWidth)
    (hmax : 0 < effortMax) (hbudget : effortMax ≤ budget)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hcost_convex : ConvexOn ℝ (Icc 0 effortMax) cost)
    (hp' : ∀ e ∈ Ioo (0 : ℝ) effortMax, HasDerivAt cost (costDeriv e) e)
    (hp'' : ∀ e ∈ Ioo (0 : ℝ) effortMax, HasDerivAt costDeriv (costSecondDeriv e) e)
    (hg : ContinuousOn production (Icc 0 budget))
    (hg_mono : StrictMonoOn production (Icc 0 budget)) (hg_zero : production 0 = 0)
    (hg_conc : ConcaveOn ℝ (Icc 0 budget) production)
    (hg_sq : ConcaveOn ℝ (Ioo 0 budget) (fun e => production e ^ 2))
    (hg' : ∀ e ∈ Ioo (0 : ℝ) budget, HasDerivAt production (productionDeriv e) e)
    (hg'' : ∀ e ∈ Ioo (0 : ℝ) budget,
      HasDerivAt productionDeriv (productionSecondDeriv e) e)
    (hg''_cont : ContinuousOn productionSecondDeriv (Ioo 0 budget))
    (hgeo : ConcaveOn ℝ {z | 0 < Real.exp z ∧ Real.exp z ≤ production effortMax}
      (fun z => Real.log (cost (effortIntervalInverse production effortMax (Real.exp z))))) :
    AntitoneOn (sourceTwoLevelApplicantWelfare cost production
      (fun t => lowerSkill + skillWidth * t) effortMax rho) (Ioc (0 : ℝ) (1 - rho)) ∧
    ∀ c ∈ Ioo (0 : ℝ) (1 - rho), ∃ beta ∈ Ioo (0 : ℝ) 1, ∀ d ∈ Ioc (0 : ℝ) (1 - rho),
      sourceSkillConditionalSchoolUtility μ skill cost production
        (fun t => lowerSkill + skillWidth * t) budget effortMax rho beta d ≤
      sourceSkillConditionalSchoolUtility μ skill cost production
        (fun t => lowerSkill + skillWidth * t) budget effortMax rho beta c := by
  have hsubset : Icc (0 : ℝ) effortMax ⊆ Icc 0 budget :=
    fun _ he => ⟨he.1, he.2.trans hbudget⟩
  have hgE := hg.mono hsubset
  have hmonoE := hg_mono.mono hsubset
  have hf : ContinuousOn (fun t => lowerSkill + skillWidth * t) (Ioc (0 : ℝ) 1) :=
    continuousOn_const.add (continuousOn_const.mul continuousOn_id)
  have hfpos (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : 0 < lowerSkill + skillWidth * t :=
    add_pos_of_nonneg_of_pos hlower (mul_pos hwidth ht.1)
  have hfmono : MonotoneOn (fun t => lowerSkill + skillWidth * t) (Ioc (0 : ℝ) 1) := by
    intro a _ b _ hab
    dsimp only
    linarith [mul_le_mul_of_nonneg_left hab hwidth.le]
  have hwelfare := sourceTwoLevelApplicantWelfare_antitone hrho hmax hcost hcost_mono
    hcost_zero hcost_max hgE hmonoE (by rw [hg_zero]) hf hfpos hfmono
    (affineSkill_logConcave hlower hwidth) (by simpa only [hg_zero] using hgeo)
  have hratio := primitiveScoreCost_ratio_convexOn_of_geometricConcavity hmax
    hcost_mono hcost_zero hcost_convex hgE hmonoE hg_zero
    (hg_conc.subset hsubset (convex_Icc _ _)) hgeo
  have hlo := (primitiveScoreCost_capacity_interval hrho hrho_one hmax hcost hcost_mono
    hcost_zero hcost_max hgE hmonoE hg_zero).1
  have hratio' := hratio.subset
    (show Icc (production (effortIntervalInverse cost effortMax rho)) (production effortMax) ⊆
      Ioc (0 : ℝ) (production effortMax) from fun _ ha => ⟨hlo.trans_le ha.1, ha.2⟩)
    (convex_Icc _ _)
  refine ⟨hwelfare, ?_⟩
  intro c hc
  exact sourceSkillConditionalSchoolUtility_exists_optimal_weight_of_affineSkill
    μ hskill hmean hrho hrho_one hlower hwidth hmax hbudget hcost hcost_mono hcost_zero hcost_max
    hp' hp'' hg hg_mono hg_zero (hg_conc.subset Ioo_subset_Icc_self (convex_Ioo _ _))
    hg_sq hg' hg'' hg''_cont hratio' hc

end LBG22StrategicRanking
