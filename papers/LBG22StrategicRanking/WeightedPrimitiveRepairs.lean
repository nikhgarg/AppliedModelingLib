import LBG22StrategicRanking.PrimitiveRepairs
import LBG22StrategicRanking.AdmittedLoss
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Primitive output and production-loss geometry

For uniform measurable skill, the school's measurable output is the product
of the admission cutoff and the cutoff applicant's production. Parameterizing
by cutoff production separates the cost primitive from the admitted-population
loss. The inverse output path is constructed from the primitive cost schedule.
-/

namespace LBG22StrategicRanking

open Set Filter
open scoped Topology

/-- Measurable output in units of the uniform skill scale, parameterized by
cutoff production. The capacity equation determines the cutoff. -/
noncomputable def uniformSkillOutput (scoreCost : ℝ → ℝ) (rho a : ℝ) : ℝ :=
  a * (1 - rho / scoreCost a)

theorem uniformSkillOutput_eq_sub (scoreCost : ℝ → ℝ) (rho a : ℝ) :
    uniformSkillOutput scoreCost rho a = a - rho * (a / scoreCost a) := by
  unfold uniformSkillOutput
  ring

/-- Marginal measurable output as cutoff production increases. -/
noncomputable def uniformSkillOutputSlope (C C' : ℝ → ℝ) (rho a : ℝ) : ℝ :=
  1 - rho / C a + a * rho * C' a / (C a) ^ 2

/-- Curvature of measurable output in cutoff-production coordinates. -/
noncomputable def uniformSkillOutputCurvature (C C' C'' : ℝ → ℝ) (rho a : ℝ) : ℝ :=
  rho * (2 * C' a + a * C'' a) / (C a) ^ 2 -
    2 * rho * a * (C' a) ^ 2 / (C a) ^ 3

theorem uniformSkillOutput_hasDerivAt {C C' : ℝ → ℝ} {rho a : ℝ}
    (hC : HasDerivAt C (C' a) a) (hCa : C a ≠ 0) :
    HasDerivAt (uniformSkillOutput C rho) (uniformSkillOutputSlope C C' rho a) a := by
  have hd := (hasDerivAt_id a).mul (((hasDerivAt_const a rho).div hC hCa).const_sub 1)
  convert hd using 1
  dsimp [uniformSkillOutputSlope]
  field_simp
  ring

theorem uniformSkillOutputSlope_hasDerivAt {C C' C'' : ℝ → ℝ} {rho a : ℝ}
    (hC : HasDerivAt C (C' a) a) (hC' : HasDerivAt C' (C'' a) a) (hCa : C a ≠ 0) :
    HasDerivAt (uniformSkillOutputSlope C C' rho)
      (uniformSkillOutputCurvature C C' C'' rho a) a := by
  have hbase := ((hasDerivAt_const a rho).div hC hCa).const_sub 1
  have hterm := (((hasDerivAt_id a).mul_const rho).mul hC').div (hC.pow 2) (pow_ne_zero 2 hCa)
  convert hbase.add hterm using 1
  dsimp [uniformSkillOutputCurvature]
  norm_num
  field_simp
  ring

/-- Increasing effort cost makes the measurable output path strictly increasing
on the feasible cutoff-production interval. -/
theorem uniformSkillOutput_strictMonoOn {scoreCost : ℝ → ℝ} {rho lo hi : ℝ}
    (hrho : 0 < rho) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hcost : StrictMonoOn scoreCost (Icc lo hi)) (hcost_lo : scoreCost lo = rho) :
    StrictMonoOn (uniformSkillOutput scoreCost rho) (Icc lo hi) := by
  intro a ha b hb hab
  have hca : rho ≤ scoreCost a := by
    simpa only [hcost_lo] using hcost.monotoneOn ⟨le_rfl, hlohi⟩ ha ha.1
  have hcpos : 0 < scoreCost a := hrho.trans_le hca
  have hbracket : 0 ≤ 1 - rho / scoreCost a :=
    sub_nonneg.mpr ((div_le_one hcpos).mpr hca)
  have hratio := div_lt_div_of_pos_left hrho hcpos (hcost ha hb hab)
  have hbpos : 0 < b := hlo.trans_le hb.1
  unfold uniformSkillOutput
  calc
    a * (1 - rho / scoreCost a) ≤ b * (1 - rho / scoreCost a) :=
      mul_le_mul_of_nonneg_right hab.le hbracket
    _ < b * (1 - rho / scoreCost b) := mul_lt_mul_of_pos_left (by linarith) hbpos

/-- Convexity of production divided by its effort cost is a primitive sufficient
condition for concavity of the measurable-output path. -/
theorem uniformSkillOutput_concaveOn {scoreCost : ℝ → ℝ} {rho : ℝ} {D : Set ℝ}
    (hrho : 0 ≤ rho) (hD : Convex ℝ D)
    (hcostRatio : ConvexOn ℝ D (fun a => a / scoreCost a)) :
    ConcaveOn ℝ D (uniformSkillOutput scoreCost rho) := by
  have hlin : ConcaveOn ℝ D (fun a : ℝ => a) := concaveOn_id hD
  have hscaled : ConvexOn ℝ D (fun a => rho * (a / scoreCost a)) := hcostRatio.smul hrho
  exact (hlin.sub hscaled).congr (fun a _ => (uniformSkillOutput_eq_sub scoreCost rho a).symm)

theorem uniformSkillOutput_continuousOn {scoreCost : ℝ → ℝ} {rho lo hi : ℝ}
    (hrho : 0 < rho) (hlohi : lo ≤ hi)
    (hcost : ContinuousOn scoreCost (Icc lo hi))
    (hcost_mono : MonotoneOn scoreCost (Icc lo hi)) (hcost_lo : scoreCost lo = rho) :
    ContinuousOn (uniformSkillOutput scoreCost rho) (Icc lo hi) := by
  apply continuousOn_id.mul
  apply continuousOn_const.sub
  apply continuousOn_const.div hcost
  intro a ha
  have hca := hcost_mono ⟨le_rfl, hlohi⟩ ha ha.1
  rw [hcost_lo] at hca
  exact (hrho.trans_le hca).ne'

/-- Interior marginal output is positive even when the cost derivative is zero:
the strictly positive admission cutoff supplies the first term. -/
theorem uniformSkillOutputSlope_pos {C C' : ℝ → ℝ} {rho lo hi a : ℝ}
    (hrho : 0 < rho) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hmono : StrictMonoOn C (Icc lo hi)) (hClo : C lo = rho)
    (ha : a ∈ Ioo lo hi) (hC' : HasDerivAt C (C' a) a) :
    0 < uniformSkillOutputSlope C C' rho a := by
  have hCa : rho < C a := by
    simpa only [hClo] using hmono ⟨le_rfl, hlohi⟩ ⟨ha.1.le, ha.2.le⟩ ha.1
  have hCpos := hrho.trans hCa
  have hderiv : 0 ≤ C' a := by
    have h := (hmono.monotoneOn.mono Ioo_subset_Icc_self).derivWithin_nonneg (x := a)
    rwa [hC'.hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffWithinAt ha)] at h
  have hbracket : 0 < 1 - rho / C a := sub_pos.mpr ((div_lt_one hCpos).mpr hCa)
  have hterm : 0 ≤ a * rho * C' a / C a ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    exact mul_nonneg (mul_nonneg (hlo.trans ha.1).le hrho.le) hderiv
  exact add_pos_of_pos_of_nonneg hbracket hterm

/-- The cutoff production corresponding to a prescribed measurable output,
chosen from the actual feasible production interval. -/
noncomputable def uniformSkillOutputInverse (scoreCost : ℝ → ℝ) (rho lo hi : ℝ) : ℝ → ℝ :=
  Function.invFunOn (uniformSkillOutput scoreCost rho) (Icc lo hi)

/-- The derivative of cutoff production with respect to measurable output. -/
noncomputable def uniformSkillOutputInverseSlope (C C' : ℝ → ℝ) (rho lo hi x : ℝ) : ℝ :=
  (uniformSkillOutputSlope C C' rho (uniformSkillOutputInverse C rho lo hi x))⁻¹

/-- The inverse-output curvature expressed through primitive cost derivatives. -/
noncomputable def uniformSkillOutputInverseCurvature (C C' C'' : ℝ → ℝ)
    (rho lo hi x : ℝ) : ℝ :=
  -(uniformSkillOutputCurvature C C' C'' rho (uniformSkillOutputInverse C rho lo hi x)) /
    (uniformSkillOutputSlope C C' rho (uniformSkillOutputInverse C rho lo hi x)) ^ 3

private theorem uniformSkillOutput_zero {scoreCost : ℝ → ℝ} {rho lo : ℝ}
    (hrho : 0 < rho) (hcost_lo : scoreCost lo = rho) :
    uniformSkillOutput scoreCost rho lo = 0 := by
  simp only [uniformSkillOutput, hcost_lo, div_self hrho.ne', sub_self, mul_zero]

/-- The inverse output path is a genuine solution of the capacity/output
equations on its full feasible range. -/
theorem uniformSkillOutputInverse_spec {scoreCost : ℝ → ℝ} {rho lo hi x : ℝ}
    (hrho : 0 < rho) (hlohi : lo ≤ hi)
    (hcost : ContinuousOn scoreCost (Icc lo hi))
    (hcost_mono : MonotoneOn scoreCost (Icc lo hi)) (hcost_lo : scoreCost lo = rho)
    (hx : x ∈ Icc (0 : ℝ) (uniformSkillOutput scoreCost rho hi)) :
    uniformSkillOutputInverse scoreCost rho lo hi x ∈ Icc lo hi ∧
      uniformSkillOutput scoreCost rho (uniformSkillOutputInverse scoreCost rho lo hi x) = x := by
  have himage : x ∈ uniformSkillOutput scoreCost rho '' Icc lo hi :=
    intermediate_value_Icc hlohi
      (uniformSkillOutput_continuousOn hrho hlohi hcost hcost_mono hcost_lo)
      (by simpa only [uniformSkillOutput_zero hrho hcost_lo] using hx)
  exact Function.invFunOn_pos himage

private noncomputable def uniformSkillOutputOrderIso
    {scoreCost : ℝ → ℝ} {rho lo hi : ℝ}
    (hrho : 0 < rho) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hcost : ContinuousOn scoreCost (Icc lo hi))
    (hcost_mono : StrictMonoOn scoreCost (Icc lo hi)) (hcost_lo : scoreCost lo = rho) :
    Icc lo hi ≃o Icc (0 : ℝ) (uniformSkillOutput scoreCost rho hi) where
  toFun a := ⟨uniformSkillOutput scoreCost rho a, by
    have hmono := (uniformSkillOutput_strictMonoOn hrho hlo hlohi hcost_mono hcost_lo).monotoneOn
    constructor
    · simpa only [uniformSkillOutput_zero hrho hcost_lo] using
        hmono ⟨le_rfl, hlohi⟩ a.property a.property.1
    · exact hmono a.property ⟨hlohi, le_rfl⟩ a.property.2⟩
  invFun x := ⟨uniformSkillOutputInverse scoreCost rho lo hi x,
    (uniformSkillOutputInverse_spec hrho hlohi hcost hcost_mono.monotoneOn hcost_lo x.property).1⟩
  left_inv a := by
    apply Subtype.ext
    exact (uniformSkillOutput_strictMonoOn hrho hlo hlohi hcost_mono hcost_lo).injOn.leftInvOn_invFunOn
      a.property
  right_inv x := by
    apply Subtype.ext
    exact (uniformSkillOutputInverse_spec hrho hlohi hcost hcost_mono.monotoneOn hcost_lo x.property).2
  map_rel_iff' := by
    intro a b
    exact (uniformSkillOutput_strictMonoOn hrho hlo hlohi hcost_mono hcost_lo).le_iff_le
      a.property b.property

theorem uniformSkillOutputInverse_continuousOn
    {scoreCost : ℝ → ℝ} {rho lo hi : ℝ}
    (hrho : 0 < rho) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hcost : ContinuousOn scoreCost (Icc lo hi))
    (hcost_mono : StrictMonoOn scoreCost (Icc lo hi)) (hcost_lo : scoreCost lo = rho) :
    ContinuousOn (uniformSkillOutputInverse scoreCost rho lo hi)
      (Icc (0 : ℝ) (uniformSkillOutput scoreCost rho hi)) := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_subtype_val.comp
    (uniformSkillOutputOrderIso hrho hlo hlohi hcost hcost_mono hcost_lo).symm.continuous

/-- An interior measurable output corresponds to an interior cutoff production
strictly above the lowest admitted output. -/
theorem uniformSkillOutputInverse_mem_Ioo
    {scoreCost : ℝ → ℝ} {rho lo hi x : ℝ}
    (hrho : 0 < rho) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hcost : ContinuousOn scoreCost (Icc lo hi))
    (hcost_mono : StrictMonoOn scoreCost (Icc lo hi)) (hcost_lo : scoreCost lo = rho)
    (hx : x ∈ Ioo (0 : ℝ) (uniformSkillOutput scoreCost rho hi)) :
    uniformSkillOutputInverse scoreCost rho lo hi x ∈ Ioo lo hi ∧
      x < uniformSkillOutputInverse scoreCost rho lo hi x := by
  let A := uniformSkillOutputInverse scoreCost rho lo hi x
  have hs := uniformSkillOutputInverse_spec hrho hlohi hcost hcost_mono.monotoneOn hcost_lo
    ⟨hx.1.le, hx.2.le⟩
  have hmono := uniformSkillOutput_strictMonoOn hrho hlo hlohi hcost_mono hcost_lo
  have hAlow : lo < A := by
    apply (hmono.lt_iff_lt ⟨le_rfl, hlohi⟩ hs.1).mp
    simpa only [uniformSkillOutput_zero hrho hcost_lo, hs.2] using hx.1
  have hAhigh : A < hi := by
    apply (hmono.lt_iff_lt hs.1 ⟨hlohi, le_rfl⟩).mp
    simpa only [hs.2] using hx.2
  have hCa : rho ≤ scoreCost A := by
    simpa only [hcost_lo] using hcost_mono.monotoneOn ⟨le_rfl, hlohi⟩ hs.1 hs.1.1
  have hquot : 0 < rho / scoreCost A := div_pos hrho (hrho.trans_le hCa)
  have hApos := hlo.trans hAlow
  refine ⟨⟨hAlow, hAhigh⟩, ?_⟩
  have heq : A * (1 - rho / scoreCost A) = x := hs.2
  nlinarith [mul_pos hApos hquot]

/-- Convexity of the inverse measurable-output path is derived from the actual
cost schedule, without assuming an auxiliary inverse or its shape. -/
theorem uniformSkillOutputInverse_convexOn_and_monotoneOn
    {scoreCost : ℝ → ℝ} {rho lo hi : ℝ}
    (hrho : 0 < rho) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hcost : ContinuousOn scoreCost (Icc lo hi))
    (hcost_mono : StrictMonoOn scoreCost (Icc lo hi)) (hcost_lo : scoreCost lo = rho)
    (hcostRatio : ConvexOn ℝ (Icc lo hi) (fun a => a / scoreCost a)) :
    ConvexOn ℝ (Icc (0 : ℝ) (uniformSkillOutput scoreCost rho hi))
        (uniformSkillOutputInverse scoreCost rho lo hi) ∧
      MonotoneOn (uniformSkillOutputInverse scoreCost rho lo hi)
        (Icc (0 : ℝ) (uniformSkillOutput scoreCost rho hi)) := by
  have hspec := fun x hx => uniformSkillOutputInverse_spec hrho hlohi hcost
    hcost_mono.monotoneOn hcost_lo (x := x) hx
  have hmono := uniformSkillOutput_strictMonoOn hrho hlo hlohi hcost_mono hcost_lo
  exact ⟨AppliedModelingLib.rightInverseOn_convexOn_of_strictMonoOn_concaveOn
      (convex_Icc lo hi) (convex_Icc _ _)
      (uniformSkillOutput_concaveOn hrho.le (convex_Icc lo hi) hcostRatio) hmono
      (fun x hx => (hspec x hx).1) (fun x hx => (hspec x hx).2),
    AppliedModelingLib.rightInverseOn_monotoneOn_of_strictMonoOn hmono
      (fun x hx => (hspec x hx).1) (fun x hx => (hspec x hx).2)⟩

/-- Cost in produced-score units inherits its range, continuity, and order
properties from effort cost and technology. -/
theorem primitiveScoreCost_properties
    {cost production : ℝ → ℝ} {effortMax : ℝ}
    (hmax : 0 ≤ effortMax)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : production 0 = 0) :
    let C := costInScore cost (effortIntervalInverse production effortMax)
    ContinuousOn C (Icc 0 (production effortMax)) ∧
      StrictMonoOn C (Icc 0 (production effortMax)) ∧ C 0 = 0 ∧ C (production effortMax) = 1 := by
  let C := costInScore cost (effortIntervalInverse production effortMax)
  have hspec (y : ℝ) (hy : y ∈ Icc 0 (production effortMax)) :=
    effortIntervalInverse_spec hmax hg (show y ∈ Icc (production 0) (production effortMax) by
      simpa only [hg_zero] using hy)
  have hcontInv : ContinuousOn (effortIntervalInverse production effortMax)
      (Icc 0 (production effortMax)) := by
    simpa only [hg_zero] using effortIntervalInverse_continuousOn hmax hg hg_mono
  have hmonoInv : StrictMonoOn (effortIntervalInverse production effortMax)
      (Icc 0 (production effortMax)) := by
    simpa only [hg_zero] using effortIntervalInverse_strictMonoOn hmax hg hg_mono
  have hleft (e : ℝ) (he : e ∈ Icc 0 effortMax) :
      effortIntervalInverse production effortMax (production e) = e :=
    hg_mono.injOn.leftInvOn_invFunOn he
  have hzero := hleft 0 ⟨le_rfl, hmax⟩
  rw [hg_zero] at hzero
  refine ⟨hcost.comp hcontInv (fun y hy => (hspec y hy).1),
    hcost_mono.comp hmonoInv (fun y hy => (hspec y hy).1), ?_, ?_⟩
  · change cost (effortIntervalInverse production effortMax 0) = 0
    rw [hzero, hcost_zero]
  · change cost (effortIntervalInverse production effortMax (production effortMax)) = 1
    rw [hleft effortMax ⟨hmax, le_rfl⟩, hcost_max]

/-- Convex effort cost and concave production make cost in produced-score
units convex. If that cost is also geometrically concave, production divided
by cost is convex on the entire positive feasible interval. Thus the welfare
repair's cost condition implies the aggregate-optimality cost condition.

The proof is derivative-free: convexity gives decreasing `a/C(a)`, geometric
concavity makes its logarithm convex in log score, and composition with the
concave logarithm and then the increasing convex exponential gives convexity. -/
theorem primitiveScoreCost_ratio_convexOn_of_geometricConcavity
    {cost production : ℝ → ℝ} {effortMax : ℝ}
    (hmax : 0 < effortMax)
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax)) (hcost_zero : cost 0 = 0)
    (hcost_convex : ConvexOn ℝ (Icc 0 effortMax) cost)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : production 0 = 0)
    (hg_conc : ConcaveOn ℝ (Icc 0 effortMax) production)
    (hgeo : ConcaveOn ℝ {z | 0 < Real.exp z ∧ Real.exp z ≤ production effortMax}
      (fun z => Real.log (cost (effortIntervalInverse production effortMax (Real.exp z))))) :
    ConvexOn ℝ (Ioc (0 : ℝ) (production effortMax))
      (fun a => a / cost (effortIntervalInverse production effortMax a)) := by
  let C := costInScore cost (effortIntervalInverse production effortMax)
  let D := Ioc (0 : ℝ) (production effortMax)
  have hgmax : 0 < production effortMax := by
    simpa only [hg_zero] using hg_mono ⟨le_rfl, hmax.le⟩ ⟨hmax.le, le_rfl⟩ hmax
  have hi (a : ℝ) (ha : a ∈ Icc (0 : ℝ) (production effortMax)) :
      effortIntervalInverse production effortMax a ∈ Icc (0 : ℝ) effortMax ∧
        production (effortIntervalInverse production effortMax a) = a :=
    effortIntervalInverse_spec hmax.le hg (by simpa only [hg_zero] using ha)
  have hi0 : effortIntervalInverse production effortMax 0 = 0 := by
    have h := hg_mono.injOn.leftInvOn_invFunOn (show (0 : ℝ) ∈ Icc 0 effortMax from ⟨le_rfl, hmax.le⟩)
    simpa only [hg_zero] using h
  have hCzero : C 0 = 0 := by dsimp [C, costInScore]; rw [hi0, hcost_zero]
  have hCpos (a : ℝ) (ha : a ∈ D) : 0 < C a := by
    have hepos : 0 < effortIntervalInverse production effortMax a := by
      apply (hg_mono.lt_iff_lt ⟨le_rfl, hmax.le⟩ (hi a ⟨ha.1.le, ha.2⟩).1).mp
      rw [hg_zero, (hi a ⟨ha.1.le, ha.2⟩).2]
      exact ha.1
    simpa only [hcost_zero] using
      hcost_mono ⟨le_rfl, hmax.le⟩ (hi a ⟨ha.1.le, ha.2⟩).1 hepos
  have hiConv : ConvexOn ℝ (Icc (0 : ℝ) (production effortMax))
      (effortIntervalInverse production effortMax) :=
    AppliedModelingLib.rightInverseOn_convexOn_of_strictMonoOn_concaveOn
      (convex_Icc _ _) (convex_Icc _ _) hg_conc hg_mono
      (fun a ha => (hi a ha).1) (fun a ha => (hi a ha).2)
  have hCconv : ConvexOn ℝ (Icc (0 : ℝ) (production effortMax)) C := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro a ha b hb u v hu hv huv
    exact (hcost_mono.monotoneOn (hi _ ((convex_Icc _ _) ha hb hu hv huv)).1
      ((convex_Icc _ _) (hi a ha).1 (hi b hb).1 hu hv huv)
      (hiConv.2 ha hb hu hv huv)).trans (hcost_convex.2 (hi a ha).1 (hi b hb).1 hu hv huv)
  have hratio : AntitoneOn (fun a => a / C a) D := by
    intro a ha b hb hab
    have hs := hCconv.monotoneOn_slope_gt ⟨le_rfl, hgmax.le⟩
      ⟨⟨ha.1.le, ha.2⟩, ha.1⟩ ⟨⟨hb.1.le, hb.2⟩, hb.1⟩ hab
    have hs' : C a / a ≤ C b / b := by simpa only [slope_def_field, hCzero, sub_zero] using hs
    have hm := (div_le_div_iff₀ ha.1 hb.1).mp hs'
    exact (div_le_div_iff₀ (hCpos b hb) (hCpos a ha)).mpr (by nlinarith only [hm])
  let H := fun z => z - Real.log (C (Real.exp z))
  have hdomain : Real.log '' D = Iic (Real.log (production effortMax)) := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Real.log_le_log ha.1 ha.2
    · intro hz
      refine ⟨Real.exp z, ⟨Real.exp_pos z, ?_⟩, Real.log_exp z⟩
      exact (Real.exp_le_exp.mpr hz).trans_eq (Real.exp_log hgmax)
  have hHconv : ConvexOn ℝ (Iic (Real.log (production effortMax))) H :=
    (convexOn_id (convex_Iic _)).sub
      (hgeo.subset (fun z hz => ⟨Real.exp_pos z,
        (Real.exp_le_exp.mpr hz).trans_eq (Real.exp_log hgmax)⟩) (convex_Iic _))
  have hHlog (z : ℝ) (hz : z ≤ Real.log (production effortMax)) :
      H z = Real.log (Real.exp z / C (Real.exp z)) := by
    have ha : Real.exp z ∈ D := ⟨Real.exp_pos z,
      (Real.exp_le_exp.mpr hz).trans_eq (Real.exp_log hgmax)⟩
    rw [Real.log_div (Real.exp_pos z).ne' (hCpos _ ha).ne', Real.log_exp]
  have hHanti : AntitoneOn H (Iic (Real.log (production effortMax))) := by
    intro z hz w hw hzw
    have hzD : Real.exp z ∈ D := ⟨Real.exp_pos z,
      (Real.exp_le_exp.mpr hz).trans_eq (Real.exp_log hgmax)⟩
    have hwD : Real.exp w ∈ D := ⟨Real.exp_pos w,
      (Real.exp_le_exp.mpr hw).trans_eq (Real.exp_log hgmax)⟩
    rw [hHlog z hz, hHlog w hw]
    exact Real.log_le_log (div_pos (Real.exp_pos w) (hCpos _ hwD))
      (hratio hzD hwD (Real.exp_le_exp.mpr hzw))
  have hlog : ConvexOn ℝ D (fun a => Real.log (a / C a)) := by
    rw [← hdomain] at hHconv hHanti
    apply (hHconv.comp_concaveOn
      (strictConcaveOn_log_Ioi.concaveOn.subset Ioc_subset_Ioi_self (convex_Ioc _ _)) hHanti).congr
    intro a ha
    dsimp [Function.comp_def, H]
    rw [Real.exp_log ha.1, Real.log_div ha.1.ne' (hCpos a ha).ne']
  refine ⟨convex_Ioc _ _, ?_⟩
  intro a ha b hb u v hu hv huv
  have hab := (convex_Ioc _ _) ha hb hu hv huv
  have h := (Real.exp_le_exp.mpr (hlog.2 ha hb hu hv huv)).trans
    (convexOn_exp.2 (mem_univ _) (mem_univ _) hu hv huv)
  simpa only [Real.exp_log (div_pos hab.1 (hCpos _ hab)),
    Real.exp_log (div_pos ha.1 (hCpos _ ha)), Real.exp_log (div_pos hb.1 (hCpos _ hb))] using h

/-- The source primitives construct the convex cutoff-production path on the
entire feasible measurable-output interval. The only added shape premise here
is convexity of production divided by its effort cost on the feasible range. -/
theorem uniformSkillOutputInverse_of_effortPrimitives
    {cost production : ℝ → ℝ} {effortMax rho : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1) (hmax : 0 < effortMax)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : production 0 = 0)
    (hcostRatio : ConvexOn ℝ
      (Icc (production (effortIntervalInverse cost effortMax rho)) (production effortMax))
      (fun a => a / cost (effortIntervalInverse production effortMax a))) :
    let C := costInScore cost (effortIntervalInverse production effortMax)
    let lo := production (effortIntervalInverse cost effortMax rho)
    let A := uniformSkillOutputInverse C rho lo (production effortMax)
    ContinuousOn A (Icc (0 : ℝ) (production effortMax * (1 - rho))) ∧
      ConvexOn ℝ (Icc (0 : ℝ) (production effortMax * (1 - rho))) A ∧
      MonotoneOn A (Icc (0 : ℝ) (production effortMax * (1 - rho))) ∧
      ∀ x ∈ Icc (0 : ℝ) (production effortMax * (1 - rho)),
        A x ∈ Icc lo (production effortMax) ∧ A x * (1 - rho / C (A x)) = x := by
  let C := costInScore cost (effortIntervalInverse production effortMax)
  let q := effortIntervalInverse cost effortMax rho
  let lo := production q
  have hq := effortIntervalInverse_spec hmax.le hcost
    (show rho ∈ Icc (cost 0) (cost effortMax) by
      simpa only [hcost_zero, hcost_max] using And.intro hrho.le hrho_one.le)
  have hqpos : 0 < q := by
    apply (hcost_mono.lt_iff_lt ⟨le_rfl, hmax.le⟩ hq.1).mp
    simpa only [hcost_zero, hq.2] using hrho
  have hlo : 0 < lo := by
    simpa only [hg_zero] using hg_mono ⟨le_rfl, hmax.le⟩ hq.1 hqpos
  have hlohi : lo ≤ production effortMax :=
    hg_mono.monotoneOn hq.1 ⟨hmax.le, le_rfl⟩ hq.1.2
  have hC := primitiveScoreCost_properties hmax.le hcost hcost_mono hcost_zero hcost_max
    hg hg_mono hg_zero
  have hClo : C lo = rho := by
    change cost (effortIntervalInverse production effortMax (production q)) = rho
    have hleft : effortIntervalInverse production effortMax (production q) = q :=
      hg_mono.injOn.leftInvOn_invFunOn hq.1
    rw [hleft]
    exact hq.2
  have hsubset : Icc lo (production effortMax) ⊆ Icc 0 (production effortMax) :=
    fun _ ha => ⟨hlo.le.trans ha.1, ha.2⟩
  have hcont := hC.1.mono hsubset
  have hmono := hC.2.1.mono hsubset
  have hCmax : C (production effortMax) = 1 := hC.2.2.2
  have htop : uniformSkillOutput C rho (production effortMax) = production effortMax * (1 - rho) := by
    simp only [uniformSkillOutput, hCmax, div_one]
  have hAcont := uniformSkillOutputInverse_continuousOn hrho hlo hlohi hcont hmono hClo
  have hAshape := uniformSkillOutputInverse_convexOn_and_monotoneOn hrho hlo hlohi hcont hmono hClo
    hcostRatio
  have hAspec := fun x hx => uniformSkillOutputInverse_spec hrho hlohi hcont hmono.monotoneOn hClo
    (x := x) hx
  rw [htop] at hAcont hAshape hAspec
  exact ⟨hAcont, hAshape.1, hAshape.2, hAspec⟩

/-- Effort cost expressed per unit of produced measurable score. -/
noncomputable def primitiveScoreCostSlope (costDeriv production productionDeriv : ℝ → ℝ)
    (effortMax z : ℝ) : ℝ :=
  costDeriv (effortIntervalInverse production effortMax z) /
    productionDeriv (effortIntervalInverse production effortMax z)

/-- Curvature of effort cost in produced-score units. -/
noncomputable def primitiveScoreCostCurvature
    (costDeriv costSecondDeriv production productionDeriv productionSecondDeriv : ℝ → ℝ)
    (effortMax z : ℝ) : ℝ :=
  (costSecondDeriv (effortIntervalInverse production effortMax z) *
      productionDeriv (effortIntervalInverse production effortMax z) -
    costDeriv (effortIntervalInverse production effortMax z) *
      productionSecondDeriv (effortIntervalInverse production effortMax z)) /
    productionDeriv (effortIntervalInverse production effortMax z) ^ 3

/-- The local derivative of the constructed technology inverse is obtained
from its proved range and continuity properties. -/
theorem effortIntervalInverse_hasDerivAt
    {production : ℝ → ℝ} {effortMax z gp : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax))
    (hz : z ∈ Ioo (production 0) (production effortMax))
    (hg' : HasDerivAt production gp (effortIntervalInverse production effortMax z))
    (hgp : gp ≠ 0) :
    HasDerivAt (effortIntervalInverse production effortMax) gp⁻¹ z := by
  apply HasDerivAt.of_local_left_inverse
    ((effortIntervalInverse_continuousOn hmax hg hg_mono).continuousAt
      (Icc_mem_nhds hz.1 hz.2)) hg' hgp
  filter_upwards [Ioo_mem_nhds hz.1 hz.2] with y hy
  exact (effortIntervalInverse_spec hmax hg ⟨hy.1.le, hy.2.le⟩).2

theorem primitiveScoreCost_hasDerivAt
    {cost costDeriv production productionDeriv : ℝ → ℝ} {effortMax z : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax))
    (hz : z ∈ Ioo (production 0) (production effortMax))
    (hp' : HasDerivAt cost (costDeriv (effortIntervalInverse production effortMax z))
      (effortIntervalInverse production effortMax z))
    (hg' : HasDerivAt production (productionDeriv (effortIntervalInverse production effortMax z))
      (effortIntervalInverse production effortMax z))
    (hgp : productionDeriv (effortIntervalInverse production effortMax z) ≠ 0) :
    HasDerivAt (costInScore cost (effortIntervalInverse production effortMax))
      (primitiveScoreCostSlope costDeriv production productionDeriv effortMax z) z := by
  have hi := effortIntervalInverse_hasDerivAt hmax hg hg_mono hz hg' hgp
  simpa only [primitiveScoreCostSlope, div_eq_mul_inv] using hp'.comp z hi

theorem primitiveScoreCostSlope_hasDerivAt
    {costDeriv costSecondDeriv production productionDeriv productionSecondDeriv : ℝ → ℝ}
    {effortMax z : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax))
    (hz : z ∈ Ioo (production 0) (production effortMax))
    (hp'' : HasDerivAt costDeriv (costSecondDeriv (effortIntervalInverse production effortMax z))
      (effortIntervalInverse production effortMax z))
    (hg' : HasDerivAt production (productionDeriv (effortIntervalInverse production effortMax z))
      (effortIntervalInverse production effortMax z))
    (hg'' : HasDerivAt productionDeriv
      (productionSecondDeriv (effortIntervalInverse production effortMax z))
      (effortIntervalInverse production effortMax z))
    (hgp : productionDeriv (effortIntervalInverse production effortMax z) ≠ 0) :
    HasDerivAt (primitiveScoreCostSlope costDeriv production productionDeriv effortMax)
      (primitiveScoreCostCurvature costDeriv costSecondDeriv production productionDeriv
        productionSecondDeriv effortMax z) z := by
  have hi := effortIntervalInverse_hasDerivAt hmax hg hg_mono hz hg' hgp
  convert (hp''.comp z hi).div (hg''.comp z hi) hgp using 1
  dsimp [primitiveScoreCostCurvature]
  field_simp

/-- Unmeasurable output lost when producing measurable score `z` under the
hard effort budget. The inverse is constructed from the production primitive. -/
noncomputable def productionLoss (production : ℝ → ℝ) (budget effortMax z : ℝ) : ℝ :=
  production budget - production (budget - effortIntervalInverse production effortMax z)

/-- The marginal loss is the ratio of residual and measurable marginal
production. -/
noncomputable def productionLossSlope (production productionDeriv : ℝ → ℝ)
    (budget effortMax z : ℝ) : ℝ :=
  productionDeriv (budget - effortIntervalInverse production effortMax z) /
    productionDeriv (effortIntervalInverse production effortMax z)

/-- The second derivative of the production loss, expressed in the primitive
production derivatives at measurable and residual effort. -/
noncomputable def productionLossCurvature
    (production productionDeriv productionSecondDeriv : ℝ → ℝ)
    (budget effortMax z : ℝ) : ℝ :=
  -(productionSecondDeriv (budget - effortIntervalInverse production effortMax z)) /
      (productionDeriv (effortIntervalInverse production effortMax z)) ^ 2 -
    productionDeriv (budget - effortIntervalInverse production effortMax z) *
      productionSecondDeriv (effortIntervalInverse production effortMax z) /
      (productionDeriv (effortIntervalInverse production effortMax z)) ^ 3

theorem productionLoss_hasDerivAt
    {production productionDeriv : ℝ → ℝ} {budget effortMax z : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax))
    (hz : z ∈ Ioo (production 0) (production effortMax))
    (hg' : HasDerivAt production (productionDeriv (effortIntervalInverse production effortMax z))
      (effortIntervalInverse production effortMax z))
    (hgr' : HasDerivAt production
      (productionDeriv (budget - effortIntervalInverse production effortMax z))
      (budget - effortIntervalInverse production effortMax z))
    (hgp : productionDeriv (effortIntervalInverse production effortMax z) ≠ 0) :
    HasDerivAt (productionLoss production budget effortMax)
      (productionLossSlope production productionDeriv budget effortMax z) z := by
  have hi := effortIntervalInverse_hasDerivAt hmax hg hg_mono hz hg' hgp
  have h := (hgr'.comp z (hi.const_sub budget)).const_sub (production budget)
  convert h using 1
  simp only [productionLossSlope, div_eq_mul_inv, neg_neg, mul_neg]

/-- The two sources of convexity of production loss: curvature at measurable
effort and curvature at residual effort. -/
theorem productionLossSlope_hasDerivAt
    {production productionDeriv productionSecondDeriv : ℝ → ℝ} {budget effortMax z : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax))
    (hz : z ∈ Ioo (production 0) (production effortMax))
    (hg' : HasDerivAt production (productionDeriv (effortIntervalInverse production effortMax z))
      (effortIntervalInverse production effortMax z))
    (hg'' : HasDerivAt productionDeriv
      (productionSecondDeriv (effortIntervalInverse production effortMax z))
      (effortIntervalInverse production effortMax z))
    (hgr'' : HasDerivAt productionDeriv
      (productionSecondDeriv (budget - effortIntervalInverse production effortMax z))
      (budget - effortIntervalInverse production effortMax z))
    (hgp : productionDeriv (effortIntervalInverse production effortMax z) ≠ 0) :
    HasDerivAt (productionLossSlope production productionDeriv budget effortMax)
      (productionLossCurvature production productionDeriv productionSecondDeriv budget effortMax z)
      z := by
  have hi := effortIntervalInverse_hasDerivAt hmax hg hg_mono hz hg' hgp
  have h := (hgr''.comp z (hi.const_sub budget)).div (hg''.comp z hi) hgp
  convert h using 1
  simp only [productionLossCurvature, Function.comp_apply]
  field_simp

/-- Concavity bounds the second derivative using only local differentiability
on the interior of the source domain. -/
private theorem secondDerivative_nonpos_of_concaveOn
    {f f' : ℝ → ℝ} {lo hi x f'' : ℝ}
    (hconc : ConcaveOn ℝ (Ioo lo hi) f)
    (hfirst : ∀ t ∈ Ioo lo hi, HasDerivAt f (f' t) t)
    (hx : x ∈ Ioo lo hi) (hsecond : HasDerivAt f' f'' x) : f'' ≤ 0 := by
  have hanti : AntitoneOn f' (Ioo lo hi) := by
    intro a ha b hb hab
    have h := hconc.antitoneOn_deriv (fun t ht => (hfirst t ht).differentiableAt) ha hb hab
    simpa only [(hfirst a ha).deriv, (hfirst b hb).deriv] using h
  have h := hanti.derivWithin_nonpos (x := x)
  rwa [hsecond.hasDerivWithinAt.derivWithin (isOpen_Ioo.uniqueDiffWithinAt hx)] at h

/-- Both derivatives and their signs for the constructed inverse output path.
Smoothness is required only at interior cutoff productions. -/
theorem uniformSkillOutputInverse_derivatives
    {C C' C'' : ℝ → ℝ} {rho lo hi x : ℝ}
    (hrho : 0 < rho) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hcont : ContinuousOn C (Icc lo hi))
    (hmono : StrictMonoOn C (Icc lo hi)) (hClo : C lo = rho)
    (hC' : ∀ a ∈ Ioo lo hi, HasDerivAt C (C' a) a)
    (hC'' : ∀ a ∈ Ioo lo hi, HasDerivAt C' (C'' a) a)
    (hcostRatio : ConvexOn ℝ (Icc lo hi) (fun a => a / C a))
    (hx : x ∈ Ioo (0 : ℝ) (uniformSkillOutput C rho hi)) :
    HasDerivAt (uniformSkillOutputInverse C rho lo hi)
        (uniformSkillOutputInverseSlope C C' rho lo hi x) x ∧
      HasDerivAt (uniformSkillOutputInverseSlope C C' rho lo hi)
        (uniformSkillOutputInverseCurvature C C' C'' rho lo hi x) x ∧
      0 < uniformSkillOutputInverseSlope C C' rho lo hi x ∧
      0 ≤ uniformSkillOutputInverseCurvature C C' C'' rho lo hi x := by
  let A := uniformSkillOutputInverse C rho lo hi
  have hA := (uniformSkillOutputInverse_mem_Ioo hrho hlo hlohi hcont hmono hClo hx).1
  have hCpos (a : ℝ) (ha : a ∈ Icc lo hi) : 0 < C a := by
    have h := hmono.monotoneOn ⟨le_rfl, hlohi⟩ ha ha.1
    rw [hClo] at h
    exact hrho.trans_le h
  have hF' (a : ℝ) (ha : a ∈ Ioo lo hi) :=
    uniformSkillOutput_hasDerivAt (rho := rho) (hC' a ha) (hCpos a ⟨ha.1.le, ha.2.le⟩).ne'
  have hFpos := uniformSkillOutputSlope_pos hrho hlo hlohi hmono hClo hA (hC' _ hA)
  have hAcont : ContinuousAt A x :=
    (uniformSkillOutputInverse_continuousOn hrho hlo hlohi hcont hmono hClo).continuousAt
      (Icc_mem_nhds hx.1 hx.2)
  have hright : ∀ᶠ y in 𝓝 x, uniformSkillOutput C rho (A y) = y := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (uniformSkillOutputInverse_spec hrho hlohi hcont hmono.monotoneOn hClo
      ⟨hy.1.le, hy.2.le⟩).2
  have hfirst := HasDerivAt.of_local_left_inverse hAcont (hF' (A x) hA) hFpos.ne' hright
  have hFsecond := uniformSkillOutputSlope_hasDerivAt (rho := rho) (hC' (A x) hA)
    (hC'' (A x) hA) (hCpos (A x) ⟨hA.1.le, hA.2.le⟩).ne'
  have hsecond : HasDerivAt (uniformSkillOutputInverseSlope C C' rho lo hi)
      (uniformSkillOutputInverseCurvature C C' C'' rho lo hi x) x := by
    convert (hFsecond.comp x hfirst).inv hFpos.ne' using 1
    dsimp [uniformSkillOutputInverseCurvature, A]
    field_simp
  have hFconc := (uniformSkillOutput_concaveOn hrho.le (convex_Icc lo hi) hcostRatio).subset
    Ioo_subset_Icc_self (convex_Ioo lo hi)
  have hFnonpos := secondDerivative_nonpos_of_concaveOn hFconc hF' hA hFsecond
  exact ⟨hfirst, hsecond, inv_pos.mpr hFpos,
    div_nonneg (neg_nonneg.mpr hFnonpos) (pow_nonneg hFpos.le 3)⟩

/-- Concavity of squared production supplies the elasticity curvature needed
by the admitted-population loss argument. -/
theorem squaredProduction_curvature_nonpos
    {production productionDeriv : ℝ → ℝ} {lo hi e gpp : ℝ}
    (hconc : ConcaveOn ℝ (Ioo lo hi) (fun t => (production t) ^ 2))
    (hfirst : ∀ t ∈ Ioo lo hi, HasDerivAt production (productionDeriv t) t)
    (he : e ∈ Ioo lo hi) (hsecond : HasDerivAt productionDeriv gpp e) :
    production e * gpp + (productionDeriv e) ^ 2 ≤ 0 := by
  have hfirstSq (t : ℝ) (ht : t ∈ Ioo lo hi) :
      HasDerivAt (fun t => (production t) ^ 2)
        (2 * production t * productionDeriv t) t := by
    convert (hfirst t ht).pow 2 using 1
    norm_num
  have hsecondSq : HasDerivAt (fun t => 2 * production t * productionDeriv t)
      (2 * ((productionDeriv e) ^ 2 + production e * gpp)) e := by
    convert ((hfirst e he).const_mul 2).mul hsecond using 1
    ring
  have h := secondDerivative_nonpos_of_concaveOn hconc hfirstSq he hsecondSq
  linarith

/-- Strictly increasing concave production has strictly positive marginal
production at every interior effort. -/
theorem productionDeriv_pos_of_strictMono_concave
    {production : ℝ → ℝ} {budget e gp : ℝ}
    (hmono : StrictMonoOn production (Icc 0 budget))
    (hconc : ConcaveOn ℝ (Ioo 0 budget) production)
    (he : e ∈ Ioo (0 : ℝ) budget) (hderiv : HasDerivAt production gp e) : 0 < gp := by
  let y := (e + budget) / 2
  have hey : e < y := by dsimp [y]; linarith [he.2]
  have hy : y ∈ Ioo (0 : ℝ) budget := by dsimp [y]; constructor <;> linarith [he.1, he.2]
  have hinc := hmono ⟨he.1.le, he.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hey
  have hslope : 0 < slope production e y := by
    rw [slope_def_field]
    exact div_pos (sub_pos.mpr hinc) (sub_pos.mpr hey)
  exact hslope.trans_le (hconc.slope_le_of_hasDerivAt he hy hey hderiv)

/-- The aggregate-loss curvature condition follows from increasing concave
production with concave square. No bounded derivative at zero is required,
and the hard budget may equal the maximal feasible measurable effort. -/
theorem productionLoss_derivatives_and_curvature_of_squaredConcavity
    {production productionDeriv productionSecondDeriv : ℝ → ℝ}
    {budget effortMax z : ℝ}
    (hmax : 0 < effortMax) (hbudget : effortMax ≤ budget)
    (hg : ContinuousOn production (Icc 0 budget))
    (hg_mono : StrictMonoOn production (Icc 0 budget)) (hg_zero : production 0 = 0)
    (hg_conc : ConcaveOn ℝ (Ioo 0 budget) production)
    (hg_sq : ConcaveOn ℝ (Ioo 0 budget) (fun e => production e ^ 2))
    (hg' : ∀ e ∈ Ioo (0 : ℝ) budget, HasDerivAt production (productionDeriv e) e)
    (hg'' : ∀ e ∈ Ioo (0 : ℝ) budget,
      HasDerivAt productionDeriv (productionSecondDeriv e) e)
    (hz : z ∈ Ioo (0 : ℝ) (production effortMax)) :
    HasDerivAt (productionLoss production budget effortMax)
        (productionLossSlope production productionDeriv budget effortMax z) z ∧
      HasDerivAt (productionLossSlope production productionDeriv budget effortMax)
        (productionLossCurvature production productionDeriv productionSecondDeriv budget effortMax z) z ∧
      0 < productionLossSlope production productionDeriv budget effortMax z ∧
      productionLossSlope production productionDeriv budget effortMax z ≤
        z * productionLossCurvature production productionDeriv productionSecondDeriv budget effortMax z := by
  have hsubset : Icc (0 : ℝ) effortMax ⊆ Icc 0 budget :=
    fun _ he => ⟨he.1, he.2.trans hbudget⟩
  have hgE := hg.mono hsubset
  have hmonoE := hg_mono.mono hsubset
  have hz' : z ∈ Ioo (production 0) (production effortMax) := by
    simpa only [hg_zero] using hz
  let e := effortIntervalInverse production effortMax z
  have hinv := effortIntervalInverse_spec hmax.le hgE ⟨hz'.1.le, hz'.2.le⟩
  have he0 : 0 < e := by
    apply (hmonoE.lt_iff_lt ⟨le_rfl, hmax.le⟩ hinv.1).mp
    simpa only [hinv.2] using hz'.1
  have heMax : e < effortMax := by
    apply (hmonoE.lt_iff_lt hinv.1 ⟨hmax.le, le_rfl⟩).mp
    simpa only [hinv.2] using hz'.2
  have he : e ∈ Ioo (0 : ℝ) budget := ⟨he0, heMax.trans_le hbudget⟩
  have hr : budget - e ∈ Ioo (0 : ℝ) budget := by
    constructor <;> linarith [he.1, he.2]
  have hpe : 0 < productionDeriv e :=
    productionDeriv_pos_of_strictMono_concave hg_mono hg_conc he (hg' e he)
  have hpr : 0 < productionDeriv (budget - e) :=
    productionDeriv_pos_of_strictMono_concave hg_mono hg_conc hr (hg' _ hr)
  have hfirst := productionLoss_hasDerivAt hmax.le hgE hmonoE hz' (hg' e he) (hg' _ hr) hpe.ne'
  have hsecond := productionLossSlope_hasDerivAt hmax.le hgE hmonoE hz'
    (hg' e he) (hg'' e he) (hg'' _ hr) hpe.ne'
  refine ⟨hfirst, hsecond, div_pos hpr hpe, ?_⟩
  have hsq := squaredProduction_curvature_nonpos hg_sq hg' he (hg'' e he)
  have hrsecond := secondDerivative_nonpos_of_concaveOn hg_conc hg' hr (hg'' _ hr)
  change productionDeriv (budget - e) / productionDeriv e ≤
    z * (-(productionSecondDeriv (budget - e)) / productionDeriv e ^ 2 -
      productionDeriv (budget - e) * productionSecondDeriv e / productionDeriv e ^ 3)
  have hze : production e = z := hinv.2
  rw [hze] at hsq
  have hterm : productionDeriv (budget - e) * productionDeriv e ^ 2 ≤
      -(z * productionDeriv (budget - e) * productionSecondDeriv e) := by
    nlinarith [mul_nonneg hpr.le (neg_nonneg.mpr hsq)]
  have htermR : 0 ≤ -(z * productionSecondDeriv (budget - e) * productionDeriv e) :=
    neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hz.1.le hrsecond) hpe.le)
  apply (le_of_mul_le_mul_right (a := productionDeriv e ^ 3) ?_ (pow_pos hpe 3))
  field_simp
  nlinarith only [hterm, htermR]

/-- Continuous second primitive derivatives give continuous production-loss
curvature on the feasible interior; no endpoint derivative is assumed. -/
theorem productionLossCurvature_continuousOn
    {production productionDeriv productionSecondDeriv : ℝ → ℝ} {budget effortMax : ℝ}
    (hmax : 0 ≤ effortMax) (hbudget : effortMax ≤ budget)
    (hg : ContinuousOn production (Icc 0 budget))
    (hg_mono : StrictMonoOn production (Icc 0 budget)) (hg_zero : production 0 = 0)
    (hg_conc : ConcaveOn ℝ (Ioo 0 budget) production)
    (hg' : ∀ e ∈ Ioo (0 : ℝ) budget, HasDerivAt production (productionDeriv e) e)
    (hg'' : ∀ e ∈ Ioo (0 : ℝ) budget,
      HasDerivAt productionDeriv (productionSecondDeriv e) e)
    (hg''_cont : ContinuousOn productionSecondDeriv (Ioo 0 budget)) :
    ContinuousOn (productionLossCurvature production productionDeriv productionSecondDeriv
      budget effortMax) (Ioo 0 (production effortMax)) := by
  have hsubset : Icc (0 : ℝ) effortMax ⊆ Icc 0 budget :=
    fun _ he => ⟨he.1, he.2.trans hbudget⟩
  have hgE := hg.mono hsubset
  have hmonoE := hg_mono.mono hsubset
  have hi : ContinuousOn (effortIntervalInverse production effortMax)
      (Ioo 0 (production effortMax)) := by
    have h := (effortIntervalInverse_continuousOn hmax hgE hmonoE).mono Ioo_subset_Icc_self
    simpa only [hg_zero] using h
  have himem (z : ℝ) (hz : z ∈ Ioo 0 (production effortMax)) :
      effortIntervalInverse production effortMax z ∈ Ioo (0 : ℝ) budget := by
    have h := effortIntervalInverse_mem_Ioo hmax hgE hmonoE
      (show z ∈ Ioo (production 0) (production effortMax) by simpa only [hg_zero] using hz)
    exact ⟨h.1, h.2.trans_le hbudget⟩
  have hrmem (z : ℝ) (hz : z ∈ Ioo 0 (production effortMax)) :
      budget - effortIntervalInverse production effortMax z ∈ Ioo (0 : ℝ) budget := by
    have h := himem z hz
    constructor <;> linarith [h.1, h.2]
  have hg'_cont : ContinuousOn productionDeriv (Ioo 0 budget) :=
    fun e he => (hg'' e he).continuousAt.continuousWithinAt
  have hpi := hg'_cont.comp hi (fun z hz => himem z hz)
  have hppi := hg''_cont.comp hi (fun z hz => himem z hz)
  have hpr := hg'_cont.comp (continuousOn_const.sub hi) (fun z hz => hrmem z hz)
  have hppr := hg''_cont.comp (continuousOn_const.sub hi) (fun z hz => hrmem z hz)
  have hnz (z : ℝ) (hz : z ∈ Ioo 0 (production effortMax)) :
      productionDeriv (effortIntervalInverse production effortMax z) ≠ 0 :=
    (productionDeriv_pos_of_strictMono_concave hg_mono hg_conc (himem z hz)
      (hg' _ (himem z hz))).ne'
  exact (hppr.neg.div (hpi.pow 2) (fun z hz => pow_ne_zero 2 (hnz z hz))).sub
    ((hpr.mul hppi).div (hpi.pow 3) (fun z hz => pow_ne_zero 3 (hnz z hz)))

/-- Production loss is continuous through zero residual effort, including the
case where the hard budget equals the maximal measurable effort. -/
theorem productionLoss_continuousOn
    {production : ℝ → ℝ} {budget effortMax : ℝ}
    (hmax : 0 ≤ effortMax) (hbudget : effortMax ≤ budget)
    (hg : ContinuousOn production (Icc 0 budget))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : production 0 = 0) :
    ContinuousOn (productionLoss production budget effortMax) (Icc 0 (production effortMax)) := by
  have hgE := hg.mono (show Icc (0 : ℝ) effortMax ⊆ Icc 0 budget from
    fun _ he => ⟨he.1, he.2.trans hbudget⟩)
  have hinvcont : ContinuousOn (effortIntervalInverse production effortMax)
      (Icc 0 (production effortMax)) := by
    simpa only [hg_zero] using effortIntervalInverse_continuousOn hmax hgE hg_mono
  apply continuousOn_const.sub
  apply hg.comp (continuousOn_const.sub hinvcont)
  intro z hz
  have hi := effortIntervalInverse_spec hmax hgE
    (show z ∈ Icc (production 0) (production effortMax) by simpa only [hg_zero] using hz)
  exact ⟨by linarith [hi.1.2], by linarith [hi.1.1]⟩

/-- Normalizing the actual admitted population and changing variables from
skill rank to produced score gives the integral used by the aggregate-loss
curvature argument. The Jacobian and the conditional-population mass are both
explicit. -/
theorem uniformTailLoss_eq_scoreIntegral {L : ℝ → ℝ} {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (hL : ContinuousOn L (Icc x a)) :
    (∫ t in (x / a)..1, L (x / t)) / (1 - x / a) =
      x * a / (a - x) * ∫ z in x..a, L z / z ^ 2 := by
  have ha : 0 < a := hx.trans hxa
  have hzpos (z : ℝ) (hz : z ∈ uIcc x a) : 0 < z := by
    rw [uIcc_of_le hxa.le] at hz
    exact hx.trans_le hz.1
  have hd (z : ℝ) (hz : z ∈ uIcc x a) :
      HasDerivAt (fun z : ℝ => x / z) (-x / z ^ 2) z := by
    simpa only [mul_zero, zero_mul, mul_one, zero_sub] using
      (hasDerivAt_const z x).div (hasDerivAt_id z) (hzpos z hz).ne'
  have hdcont : ContinuousOn (fun z : ℝ => -x / z ^ 2) (uIcc x a) :=
    continuousOn_const.div (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (hzpos z hz).ne')
  have himagepos (t : ℝ) (ht : t ∈ (fun z : ℝ => x / z) '' uIcc x a) : 0 < t := by
    rcases ht with ⟨z, hz, rfl⟩
    exact div_pos hx (hzpos z hz)
  have hG : ContinuousOn (fun t : ℝ => L (x / t)) ((fun z : ℝ => x / z) '' uIcc x a) := by
    apply hL.comp (continuousOn_const.div continuousOn_id (fun t ht => (himagepos t ht).ne'))
    intro t ht
    rcases ht with ⟨z, hz, rfl⟩
    change x / (x / z) ∈ Icc x a
    rw [div_div_cancel₀ hx.ne']
    rwa [uIcc_of_le hxa.le] at hz
  have hchange := intervalIntegral.integral_comp_mul_deriv' hd hdcont hG
  simp only [Function.comp_apply, div_div_cancel₀ hx.ne', div_self hx.ne'] at hchange
  have hintegral : (∫ z in x..a, L z * (-x / z ^ 2)) =
      -x * ∫ z in x..a, L z / z ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z _
    ring
  rw [hintegral, intervalIntegral.integral_symm (a := x / a) (b := 1)] at hchange
  have hactual : (∫ t in (x / a)..1, L (x / t)) = x * ∫ z in x..a, L z / z ^ 2 := by
    linarith
  rw [hactual]
  field_simp

/-- Conditional residual output for a uniform admitted skill population. -/
noncomputable def uniformSkillResidualMean (production : ℝ → ℝ)
    (budget effortMax x a : ℝ) : ℝ :=
  (∫ t in (x / a)..1,
    production (budget - effortIntervalInverse production effortMax (x / t))) / (1 - x / a)

/-- The aggregate loss is exactly the source's conditional residual-output
mean subtracted from the all-residual-effort benchmark. -/
theorem uniformSkillResidualMean_eq_sub_admittedLoss
    {production : ℝ → ℝ} {budget effortMax x a : ℝ}
    (hmax : 0 ≤ effortMax) (hbudget : effortMax ≤ budget)
    (hg : ContinuousOn production (Icc 0 budget))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : production 0 = 0)
    (hx : 0 < x) (hxa : x < a) (ha : a ≤ production effortMax) :
    uniformSkillResidualMean production budget effortMax x a =
      production budget - admittedLoss (productionLoss production budget effortMax) x a := by
  let L := productionLoss production budget effortMax
  have hapos : 0 < a := hx.trans hxa
  have hcpos : 0 < x / a := div_pos hx hapos
  have hcone : x / a < 1 := (div_lt_one hapos).mpr hxa
  have hmass : 1 - x / a ≠ 0 := (sub_pos.mpr hcone).ne'
  have hL : ContinuousOn L (Icc x a) :=
    (productionLoss_continuousOn hmax hbudget hg hg_mono hg_zero).mono
      (fun _ hz => ⟨hx.le.trans hz.1, hz.2.trans ha⟩)
  have hcomp : ContinuousOn (fun t => L (x / t)) (Icc (x / a) 1) := by
    apply hL.comp (continuousOn_const.div continuousOn_id
      (fun t ht => (hcpos.trans_le ht.1).ne'))
    intro t ht
    have htpos : 0 < t := hcpos.trans_le ht.1
    constructor
    · apply (le_div_iff₀ htpos).mpr
      exact mul_le_of_le_one_right hx.le ht.2
    · apply (div_le_iff₀ htpos).mpr
      simpa only [mul_comm] using (div_le_iff₀ hapos).mp ht.1
  have hI := hcomp.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hcone.le
  have heq : (fun t => production (budget - effortIntervalInverse production effortMax (x / t))) =
      (fun t => production budget - L (x / t)) := by
    funext t
    dsimp [L, productionLoss]
    ring
  unfold uniformSkillResidualMean
  rw [heq, intervalIntegral.integral_sub intervalIntegrable_const hI,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_div]
  have hcancel : (1 - x / a) * production budget / (1 - x / a) = production budget := by
    rw [mul_comm, mul_div_assoc, div_self hmass, mul_one]
  rw [hcancel, uniformTailLoss_eq_scoreIntegral hx hxa hL]
  rfl

/-- Positive marginal loss at all admitted scores makes the actual aggregate
loss derivative strictly positive; nondecreasing cutoff production suffices. -/
theorem admittedLossCurveSlope_pos {k A A' : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hxa : x < A x)
    (hk : ContinuousOn k (Icc x (A x)))
    (hkpos : ∀ z ∈ Icc x (A x), 0 < k z) (hA' : 0 ≤ A' x) :
    0 < admittedLossCurveSlope k A A' x := by
  have hleftIntegral : 0 < ∫ z in x..A x, (A x - z) * k z := by
    apply intervalIntegral.integral_pos hxa ((continuousOn_const.sub continuousOn_id).mul hk)
    · intro z hz
      exact mul_nonneg (sub_nonneg.mpr hz.2) (hkpos z ⟨hz.1.le, hz.2⟩).le
    · exact ⟨x, ⟨le_rfl, hxa.le⟩,
        mul_pos (sub_pos.mpr hxa) (hkpos x ⟨le_rfl, hxa.le⟩)⟩
  have hrightIntegral : 0 ≤ ∫ z in x..A x, (z - x) * k z :=
    intervalIntegral.integral_nonneg hxa.le (fun z hz =>
      mul_nonneg (sub_nonneg.mpr hz.1) (hkpos z hz).le)
  have hleft : 0 < admittedLossLeft k x (A x) :=
    mul_pos (div_pos (hx.trans hxa) (sq_pos_of_pos (sub_pos.mpr hxa))) hleftIntegral
  have hright : 0 ≤ admittedLossRight k x (A x) :=
    mul_nonneg (div_nonneg hx.le (sq_nonneg _)) hrightIntegral
  exact add_pos_of_pos_of_nonneg hleft (mul_nonneg hA' hright)

/-- Conditional residual output, parameterized by measurable output, with the
cutoff production constructed from effort cost and production. -/
noncomputable def uniformSkillResidualUtility (cost production : ℝ → ℝ)
    (budget effortMax rho x : ℝ) : ℝ :=
  uniformSkillResidualMean production budget effortMax x
    (uniformSkillOutputInverse
      (costInScore cost (effortIntervalInverse production effortMax)) rho
      (production (effortIntervalInverse cost effortMax rho)) (production effortMax) x)

/-- With uniform measurable skill and zero baseline production, concavity of
squared production and convexity of production divided by its effort cost
make the actual conditional residual-output frontier concave and strictly
decreasing. All inverse maps and population integrals are constructed from
the primitives. Differentiability is required only at interior efforts. -/
theorem uniformSkillResidualUtility_concaveOn_of_effortPrimitives
    {cost costDeriv costSecondDeriv production productionDeriv productionSecondDeriv : ℝ → ℝ}
    {budget effortMax rho : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1)
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
      (fun a => a / cost (effortIntervalInverse production effortMax a))) :
    let U := uniformSkillResidualUtility cost production budget effortMax rho
    let D := Ioo (0 : ℝ) (production effortMax * (1 - rho))
    ConcaveOn ℝ D U ∧ ∀ x ∈ D, ∃ u, HasDerivAt U u x ∧ u < 0 := by
  let C := costInScore cost (effortIntervalInverse production effortMax)
  let C₁ := primitiveScoreCostSlope costDeriv production productionDeriv effortMax
  let C₂ := primitiveScoreCostCurvature costDeriv costSecondDeriv production productionDeriv
    productionSecondDeriv effortMax
  let lo := production (effortIntervalInverse cost effortMax rho)
  let hi := production effortMax
  let A := uniformSkillOutputInverse C rho lo hi
  let A₁ := uniformSkillOutputInverseSlope C C₁ rho lo hi
  let A₂ := uniformSkillOutputInverseCurvature C C₁ C₂ rho lo hi
  let L := productionLoss production budget effortMax
  let L₁ := productionLossSlope production productionDeriv budget effortMax
  let L₂ := productionLossCurvature production productionDeriv productionSecondDeriv budget effortMax
  let D := Ioo (0 : ℝ) (hi * (1 - rho))
  have hsubset : Icc (0 : ℝ) effortMax ⊆ Icc 0 budget :=
    fun _ he => ⟨he.1, he.2.trans hbudget⟩
  have hgE := hg.mono hsubset
  have hmonoE := hg_mono.mono hsubset
  have hC := primitiveScoreCost_properties hmax.le hcost hcost_mono hcost_zero hcost_max
    hgE hmonoE hg_zero
  have hq := effortIntervalInverse_mem_Ioo hmax.le hcost hcost_mono
    (show rho ∈ Ioo (cost 0) (cost effortMax) by
      simpa only [hcost_zero, hcost_max] using And.intro hrho hrho_one)
  have hlo : 0 < lo := by
    simpa only [hg_zero] using hmonoE ⟨le_rfl, hmax.le⟩ ⟨hq.1.le, hq.2.le⟩ hq.1
  have hlohi : lo < hi := hmonoE ⟨hq.1.le, hq.2.le⟩ ⟨hmax.le, le_rfl⟩ hq.2
  have hClo : C lo = rho := by
    change cost (effortIntervalInverse production effortMax
      (production (effortIntervalInverse cost effortMax rho))) = rho
    have hleft : effortIntervalInverse production effortMax
        (production (effortIntervalInverse cost effortMax rho)) =
          effortIntervalInverse cost effortMax rho :=
      hmonoE.injOn.leftInvOn_invFunOn ⟨hq.1.le, hq.2.le⟩
    rw [hleft]
    exact (effortIntervalInverse_spec hmax.le hcost
      (show rho ∈ Icc (cost 0) (cost effortMax) by
        simpa only [hcost_zero, hcost_max] using And.intro hrho.le hrho_one.le)).2
  have hCmax : C hi = 1 := hC.2.2.2
  have htop : uniformSkillOutput C rho hi = hi * (1 - rho) := by
    simp only [uniformSkillOutput, hCmax, div_one]
  have hCsubset : Icc lo hi ⊆ Icc 0 hi := fun _ ha => ⟨hlo.le.trans ha.1, ha.2⟩
  have hcont : ContinuousOn C (Icc lo hi) := hC.1.mono hCsubset
  have hmono : StrictMonoOn C (Icc lo hi) := hC.2.1.mono hCsubset
  have hinv (a : ℝ) (ha : a ∈ Ioo lo hi) :
      effortIntervalInverse production effortMax a ∈ Ioo (0 : ℝ) effortMax :=
    effortIntervalInverse_mem_Ioo hmax.le hgE hmonoE
      (by simpa only [hg_zero] using And.intro (hlo.trans ha.1) ha.2)
  have hinvB (a : ℝ) (ha : a ∈ Ioo lo hi) :
      effortIntervalInverse production effortMax a ∈ Ioo (0 : ℝ) budget :=
    ⟨(hinv a ha).1, (hinv a ha).2.trans_le hbudget⟩
  have hC₁ (a : ℝ) (ha : a ∈ Ioo lo hi) : HasDerivAt C (C₁ a) a :=
    primitiveScoreCost_hasDerivAt hmax.le hgE hmonoE
      (by simpa only [hg_zero] using And.intro (hlo.trans ha.1) ha.2)
      (hp' _ (hinv a ha)) (hg' _ (hinvB a ha))
      (productionDeriv_pos_of_strictMono_concave hg_mono hg_conc
        (hinvB a ha) (hg' _ (hinvB a ha))).ne'
  have hC₂ (a : ℝ) (ha : a ∈ Ioo lo hi) : HasDerivAt C₁ (C₂ a) a :=
    primitiveScoreCostSlope_hasDerivAt hmax.le hgE hmonoE
      (by simpa only [hg_zero] using And.intro (hlo.trans ha.1) ha.2)
      (hp'' _ (hinv a ha)) (hg' _ (hinvB a ha)) (hg'' _ (hinvB a ha))
      (productionDeriv_pos_of_strictMono_concave hg_mono hg_conc
        (hinvB a ha) (hg' _ (hinvB a ha))).ne'
  have hA (x : ℝ) (hx : x ∈ D) := uniformSkillOutputInverse_derivatives
    hrho hlo hlohi.le hcont hmono hClo hC₁ hC₂ hcostRatio
    (show x ∈ Ioo (0 : ℝ) (uniformSkillOutput C rho hi) by simpa only [htop] using hx)
  have hfeas (x : ℝ) (hx : x ∈ D) : 0 < x ∧ x < A x ∧ A x < hi := by
    have h := uniformSkillOutputInverse_mem_Ioo hrho hlo hlohi.le hcont hmono hClo
      (show x ∈ Ioo (0 : ℝ) (uniformSkillOutput C rho hi) by simpa only [htop] using hx)
    exact ⟨hx.1, h.2, h.1.2⟩
  have hL (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) hi) :=
    productionLoss_derivatives_and_curvature_of_squaredConcavity hmax hbudget hg hg_mono
      hg_zero hg_conc hg_sq hg' hg'' hz
  have hL₂ : ContinuousOn L₂ (Ioo 0 hi) := productionLossCurvature_continuousOn
    hmax.le hbudget hg hg_mono hg_zero hg_conc hg' hg'' hg''_cont
  have hconv : ConvexOn ℝ D (fun x => admittedLoss L x (A x)) :=
    admittedLoss_convexOn_curve (convex_Ioo _ _)
      (fun z hz => (hL z hz).1) (fun z hz => (hL z hz).2.1) hL₂
      (fun z hz => (hL z hz).2.2.1.le) (fun z hz => (hL z hz).2.2.2) hfeas
      (fun x hx => (hA x hx).1) (fun x hx => (hA x hx).2.1)
      (fun x hx => (hA x hx).2.2.1.le) (fun x hx => (hA x hx).2.2.2)
  have heq (x : ℝ) (hx : x ∈ D) :
      uniformSkillResidualUtility cost production budget effortMax rho x =
        production budget - admittedLoss L x (A x) :=
    uniformSkillResidualMean_eq_sub_admittedLoss hmax.le hbudget hg hmonoE hg_zero
      hx.1 (hfeas x hx).2.1 (hfeas x hx).2.2.le
  have hconc : ConcaveOn ℝ D (fun x => production budget - admittedLoss L x (A x)) :=
    (concaveOn_const _ (convex_Ioo _ _)).sub hconv
  refine ⟨hconc.congr (fun x hx => (heq x hx).symm), ?_⟩
  intro x hx
  have hL₁cont : ContinuousOn L₁ (Ioo 0 hi) :=
    fun z hz => (hL z hz).2.1.continuousAt.continuousWithinAt
  have hd := admittedLoss_hasDerivAt_curve (fun z hz => (hL z hz).1) hL₁cont
    hx.1 (hfeas x hx).2.1 (hfeas x hx).2.2 (hA x hx).1
  have hspan : Icc x (A x) ⊆ Ioo 0 hi := fun z hz =>
    ⟨hx.1.trans_le hz.1, hz.2.trans_lt (hfeas x hx).2.2⟩
  have hkcont : ContinuousOn (lossSlope L₁) (Icc x (A x)) :=
    (hL₁cont.mono hspan).div continuousOn_id (fun z hz => (hspan hz).1.ne')
  have hdpos := admittedLossCurveSlope_pos hx.1 (hfeas x hx).2.1 hkcont
    (fun z hz => div_pos (hL z (hspan hz)).2.2.1 (hspan hz).1) (hA x hx).2.2.1.le
  refine ⟨-(admittedLossCurveSlope (lossSlope L₁) A A₁ x), ?_, neg_neg_of_pos hdpos⟩
  apply (hd.const_sub (production budget)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact heq y hy

/-- The population-loss integral remains continuous when its upper score
reaches the largest feasible production. Only continuity of loss is needed
there; its derivative may be unbounded at zero residual effort. -/
theorem admittedLoss_continuousOn_curve
    {L A : ℝ → ℝ} {lower upper scoreMax : ℝ}
    (hL : ContinuousOn L (Icc 0 scoreMax))
    (hA : ContinuousOn A (Ioc lower upper))
    (hfeas : ∀ x ∈ Ioc lower upper, x < A x ∧ A x ≤ scoreMax)
    (hlower : 0 ≤ lower) :
    ContinuousOn (fun x => admittedLoss L x (A x)) (Ioc lower upper) := by
  intro x hx
  let d := x / 2
  have hd : 0 < d := half_pos (hlower.trans_lt hx.1)
  have hdx : d < x := half_lt_self (hlower.trans_lt hx.1)
  have hds : d ≤ scoreMax := hdx.le.trans ((hfeas x hx).1.le.trans (hfeas x hx).2)
  let k := fun z => L z / z ^ 2
  let P := fun z => ∫ t in d..z, k t
  have hk : ContinuousOn k (Icc d scoreMax) :=
    (hL.mono (fun _ hz => ⟨hd.le.trans hz.1, hz.2⟩)).div
      (continuousOn_id.pow 2) (fun _ hz => pow_ne_zero 2 (hd.trans_le hz.1).ne')
  have hInt := hk.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) hds
  have hP : ContinuousOn P (Icc d scoreMax) := by
    simpa only [uIcc_of_le hds] using
      intervalIntegral.continuousOn_primitive_interval' hInt (left_mem_uIcc (a := d))
  let T := Ioc lower upper ∩ Ioi d
  have hT : T ⊆ Ioc lower upper := fun _ hy => hy.1
  have hlow (y : ℝ) (hy : y ∈ T) : y ∈ Icc d scoreMax :=
    ⟨hy.2.le, (hfeas y (hT hy)).1.le.trans (hfeas y (hT hy)).2⟩
  have hhigh (y : ℝ) (hy : y ∈ T) : A y ∈ Icc d scoreMax :=
    ⟨hy.2.le.trans (hfeas y (hT hy)).1.le, (hfeas y (hT hy)).2⟩
  have hprimitive : ContinuousOn (fun y => P (A y) - P y) T :=
    (hP.comp (hA.mono hT) hhigh).sub (hP.comp continuousOn_id hlow)
  have hactual : ContinuousOn (fun y => ∫ z in y..A y, L z / z ^ 2) T := by
    apply hprimitive.congr
    intro y hy
    have hI (z : ℝ) (hz : z ∈ Icc d scoreMax) :
        IntervalIntegrable k MeasureTheory.volume d z :=
      (hk.mono (fun _ ht => ⟨ht.1, ht.2.trans hz.2⟩)).intervalIntegrable_of_Icc hz.1
    exact (intervalIntegral.integral_interval_sub_left (hI _ (hhigh y hy))
      (hI _ (hlow y hy))).symm
  have hcont : ContinuousOn (fun y => admittedLoss L y (A y)) T :=
    ((continuousOn_id.mul (hA.mono hT)).div
      ((hA.mono hT).sub continuousOn_id)
      (fun y hy => (sub_pos.mpr (hfeas y (hT hy)).1).ne')).mul hactual
  apply (hcont x ⟨hx, hdx⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hdx)] with y hy hdy
  exact ⟨hy, hdy⟩

/-- A concave decreasing residual-output frontier supplies a genuine interior
weight supporting any interior measurable output. Continuity includes the
deterministic endpoint in the global policy comparison. -/
theorem exists_supporting_weight_of_concave_residual
    {U : ℝ → ℝ} {lower upper x scale mean u : ℝ}
    (hscale : 0 < scale) (hmean : 0 < mean)
    (hx : x ∈ Ioo lower upper)
    (hconc : ConcaveOn ℝ (Ioo lower upper) U)
    (hcont : ContinuousOn U (Ioc lower upper))
    (hderiv : HasDerivAt U u x) (hu : u < 0) :
    ∃ beta ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioc lower upper,
      weightedPrivateUtility beta (fun t => scale * t) (fun t => mean * U t) y ≤
        weightedPrivateUtility beta (fun t => scale * t) (fun t => mean * U t) x := by
  obtain ⟨beta, hbpos, hblt, hstat⟩ := exists_beta_weightedPrivateUtility_hasDerivAt_zero
    ((hasDerivAt_id x).const_mul scale) (hderiv.const_mul mean)
    (by simpa using hscale) (mul_neg_of_pos_of_neg hmean hu)
  let W := weightedPrivateUtility beta (fun t => scale * t) (fun t => mean * U t)
  have hWconc : ConcaveOn ℝ (Ioo lower upper) W :=
    ((concaveOn_id (convex_Ioo _ _)).smul hscale.le |>.smul hbpos.le).add
      ((hconc.smul hmean.le).smul (sub_pos.mpr hblt).le)
  have hWcont : ContinuousOn W (Ioc lower upper) :=
    (continuousOn_const.mul (continuousOn_const.mul continuousOn_id)).add
      (continuousOn_const.mul (continuousOn_const.mul hcont))
  have hmax (y : ℝ) (hy : y ∈ Ioo lower upper) : W y ≤ W x := by
    rcases lt_trichotomy y x with hyx | rfl | hxy
    · have hslope := hWconc.le_slope_of_hasDerivAt hy hx hyx hstat
      rw [slope_def_field] at hslope
      have h := (le_div_iff₀ (sub_pos.mpr hyx)).mp hslope
      linarith
    · exact le_rfl
    · have hslope := hWconc.slope_le_of_hasDerivAt hx hy hxy hstat
      rw [slope_def_field] at hslope
      have h := (div_le_iff₀ (sub_pos.mpr hxy)).mp hslope
      linarith
  refine ⟨beta, ⟨hbpos, hblt⟩, ?_⟩
  intro y hy
  apply ContinuousWithinAt.closure_le (s := Ioo lower upper)
    (f := W) (g := fun _ => W x) _
    ((hWcont y hy).mono Ioo_subset_Ioc_self) continuousWithinAt_const hmax
  rw [closure_Ioo (hx.1.trans hx.2).ne]
  exact ⟨hy.1.le, hy.2⟩

/-- Actual conditional residual utility is continuous on the full positive
policy-output range, including the deterministic policy. -/
theorem uniformSkillResidualUtility_continuousOn
    {cost production : ℝ → ℝ} {budget effortMax rho : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1)
    (hmax : 0 < effortMax) (hbudget : effortMax ≤ budget)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 budget))
    (hg_mono : StrictMonoOn production (Icc 0 budget)) (hg_zero : production 0 = 0)
    (hcostRatio : ConvexOn ℝ
      (Icc (production (effortIntervalInverse cost effortMax rho)) (production effortMax))
      (fun a => a / cost (effortIntervalInverse production effortMax a))) :
    ContinuousOn (uniformSkillResidualUtility cost production budget effortMax rho)
      (Ioc 0 (production effortMax * (1 - rho))) := by
  let C := costInScore cost (effortIntervalInverse production effortMax)
  let lo := production (effortIntervalInverse cost effortMax rho)
  let A := uniformSkillOutputInverse C rho lo (production effortMax)
  have hsubset : Icc (0 : ℝ) effortMax ⊆ Icc 0 budget :=
    fun _ he => ⟨he.1, he.2.trans hbudget⟩
  have hgE := hg.mono hsubset
  have hmonoE := hg_mono.mono hsubset
  have hC := primitiveScoreCost_properties hmax.le hcost hcost_mono hcost_zero hcost_max
    hgE hmonoE hg_zero
  have hq := effortIntervalInverse_mem_Ioo hmax.le hcost hcost_mono
    (show rho ∈ Ioo (cost 0) (cost effortMax) by
      simpa only [hcost_zero, hcost_max] using And.intro hrho hrho_one)
  have hlo : 0 < lo := by
    simpa only [hg_zero] using hmonoE ⟨le_rfl, hmax.le⟩ ⟨hq.1.le, hq.2.le⟩ hq.1
  have hA := uniformSkillOutputInverse_of_effortPrimitives hrho hrho_one hmax
    hcost hcost_mono hcost_zero hcost_max hgE hmonoE hg_zero hcostRatio
  have hfeas (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) (production effortMax * (1 - rho))) :
      x < A x ∧ A x ≤ production effortMax := by
    have hs := hA.2.2.2 x ⟨hx.1.le, hx.2⟩
    have hapos : 0 < A x := hlo.trans_le hs.1.1
    have hCpos : 0 < C (A x) := by
      have h := hC.2.1 ⟨le_rfl, hapos.le.trans hs.1.2⟩ ⟨hapos.le, hs.1.2⟩ hapos
      have hzero : C 0 = 0 := hC.2.2.1
      change C 0 < C (A x) at h
      simpa only [hzero] using h
    refine ⟨?_, hs.1.2⟩
    calc
      x = A x * (1 - rho / C (A x)) := hs.2.symm
      _ < A x * 1 := mul_lt_mul_of_pos_left (sub_lt_self _ (div_pos hrho hCpos)) hapos
      _ = A x := mul_one _
  have hL := productionLoss_continuousOn hmax.le hbudget hg hmonoE hg_zero
  have hloss := admittedLoss_continuousOn_curve hL (hA.1.mono Ioc_subset_Icc_self) hfeas (by norm_num)
  have hcont : ContinuousOn (fun x => production budget -
      admittedLoss (productionLoss production budget effortMax) x (A x))
      (Ioc 0 (production effortMax * (1 - rho))) := continuousOn_const.sub hloss
  apply hcont.congr
  intro x hx
  exact uniformSkillResidualMean_eq_sub_admittedLoss hmax.le hbudget hg hmonoE hg_zero
    hx.1 (hfeas x hx).1 (hfeas x hx).2

/-- Primitive sufficient conditions support every interior measurable output
by a weight strictly between zero and one, against the full two-level policy
range including its deterministic endpoint. The objective uses the actual
conditional residual-output integral and positive skill scales. -/
theorem uniformSkillResidualUtility_exists_supporting_weight_of_effortPrimitives
    {cost costDeriv costSecondDeriv production productionDeriv productionSecondDeriv : ℝ → ℝ}
    {budget effortMax rho scale mean x : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1)
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
    (hscale : 0 < scale) (hmean : 0 < mean)
    (hx : x ∈ Ioo (0 : ℝ) (production effortMax * (1 - rho))) :
    ∃ beta ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) (production effortMax * (1 - rho)),
      weightedPrivateUtility beta (fun t => scale * t)
        (fun t => mean * uniformSkillResidualUtility cost production budget effortMax rho t) y ≤
      weightedPrivateUtility beta (fun t => scale * t)
        (fun t => mean * uniformSkillResidualUtility cost production budget effortMax rho t) x := by
  have hshape := uniformSkillResidualUtility_concaveOn_of_effortPrimitives
    hrho hrho_one hmax hbudget hcost hcost_mono hcost_zero hcost_max hp' hp''
    hg hg_mono hg_zero hg_conc hg_sq hg' hg'' hg''_cont hcostRatio
  have hcont := uniformSkillResidualUtility_continuousOn hrho hrho_one hmax hbudget
    hcost hcost_mono hcost_zero hcost_max hg hg_mono hg_zero hcostRatio
  obtain ⟨u, hu, huneg⟩ := hshape.2 x hx
  exact exists_supporting_weight_of_concave_residual hscale hmean hx hshape.1 hcont hu huneg

/-- The source cutoff formula belongs to the feasible output range and is
inverted by the constructed cutoff-production path. This identifies the
output parameterization with the actual two-level policy. -/
theorem uniformSkillOutputInverse_at_sourceCutoff
    {cost production : ℝ → ℝ} {effortMax rho c : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1) (hmax : 0 < effortMax)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : production 0 = 0)
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
    let a := sourceScoreScale cost production effortMax rho c
    let C := costInScore cost (effortIntervalInverse production effortMax)
    let lo := production (effortIntervalInverse cost effortMax rho)
    a ∈ Ioc (0 : ℝ) (production effortMax) ∧
      a * c ∈ Ioc (0 : ℝ) (production effortMax * (1 - rho)) ∧
      uniformSkillOutputInverse C rho lo (production effortMax) (a * c) = a := by
  let a := sourceScoreScale cost production effortMax rho c
  let C := costInScore cost (effortIntervalInverse production effortMax)
  let lo := production (effortIntervalInverse cost effortMax rho)
  have hden : 0 < 1 - c := by linarith [hc.2]
  have hq : rho / (1 - c) ∈ Icc (cost 0) (cost effortMax) := by
    rw [hcost_zero, hcost_max]
    exact ⟨(div_pos hrho hden).le, (div_le_one hden).mpr (by linarith [hc.2])⟩
  have he := effortIntervalInverse_spec hmax.le hcost hq
  have he0 : 0 < effortIntervalInverse cost effortMax (rho / (1 - c)) := by
    apply (hcost_mono.lt_iff_lt ⟨le_rfl, hmax.le⟩ he.1).mp
    rw [hcost_zero, he.2]
    exact div_pos hrho hden
  have ha : a ∈ Ioc (0 : ℝ) (production effortMax) := by
    refine ⟨?_, hg_mono.monotoneOn he.1 ⟨hmax.le, le_rfl⟩ he.1.2⟩
    simpa only [hg_zero] using hg_mono ⟨le_rfl, hmax.le⟩ he.1 he0
  have hbase := effortIntervalInverse_spec hmax.le hcost
    (show rho ∈ Icc (cost 0) (cost effortMax) by
      simpa only [hcost_zero, hcost_max] using And.intro hrho.le hrho_one.le)
  have hbase0 : 0 < effortIntervalInverse cost effortMax rho := by
    apply (hcost_mono.lt_iff_lt ⟨le_rfl, hmax.le⟩ hbase.1).mp
    simpa only [hcost_zero, hbase.2] using hrho
  have hlo : 0 < lo := by
    simpa only [hg_zero] using hg_mono ⟨le_rfl, hmax.le⟩ hbase.1 hbase0
  have hloa : lo ≤ a := by
    apply hg_mono.monotoneOn hbase.1 he.1
    apply (hcost_mono.le_iff_le hbase.1 he.1).mp
    rw [hbase.2, he.2]
    apply (le_div_iff₀ hden).mpr
    nlinarith [hc.1]
  have hC := primitiveScoreCost_properties hmax.le hcost hcost_mono hcost_zero hcost_max
    hg hg_mono hg_zero
  have hClo : C lo = rho := by
    change cost (effortIntervalInverse production effortMax
      (production (effortIntervalInverse cost effortMax rho))) = rho
    have hleft : effortIntervalInverse production effortMax
        (production (effortIntervalInverse cost effortMax rho)) =
          effortIntervalInverse cost effortMax rho :=
      hg_mono.injOn.leftInvOn_invFunOn hbase.1
    rw [hleft]
    exact hbase.2
  have hCa : C a = rho / (1 - c) := by
    change cost (effortIntervalInverse production effortMax
      (production (effortIntervalInverse cost effortMax (rho / (1 - c))))) = _
    have hleft : effortIntervalInverse production effortMax
        (production (effortIntervalInverse cost effortMax (rho / (1 - c)))) =
          effortIntervalInverse cost effortMax (rho / (1 - c)) :=
      hg_mono.injOn.leftInvOn_invFunOn he.1
    rw [hleft]
    exact he.2
  have hF : uniformSkillOutput C rho a = a * c := by
    rw [uniformSkillOutput, hCa, div_div_cancel₀ hrho.ne']
    ring
  have hmono := uniformSkillOutput_strictMonoOn hrho hlo (hloa.trans ha.2)
    (hC.2.1.mono (fun _ hy => ⟨hlo.le.trans hy.1, hy.2⟩)) hClo
  have hleft : uniformSkillOutputInverse C rho lo (production effortMax)
      (uniformSkillOutput C rho a) = a :=
    hmono.injOn.leftInvOn_invFunOn ⟨hloa, ha.2⟩
  rw [hF] at hleft
  exact ⟨ha, ⟨mul_pos ha.1 hc.1,
    mul_le_mul ha.2 hc.2 hc.1.le (ha.1.le.trans ha.2)⟩, hleft⟩

/-- Under zero baseline production, the source effort profile at admitted
ranks is the inverse technology evaluated at the common score divided by
skill. Both nonnegative-effort clamps are inactive on this feasible range. -/
theorem sourceTwoLevelEffort_uniform_eq_inverse
    {cost production : ℝ → ℝ} {effortMax rho c t : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_zero : production 0 = 0)
    (ha : sourceScoreScale cost production effortMax rho c ∈ Ioc (0 : ℝ) (production effortMax))
    (hc : 0 < c) (ht : t ∈ Icc c 1) :
    sourceTwoLevelEffort cost production id effortMax rho c t =
      effortIntervalInverse production effortMax
        (sourceScoreScale cost production effortMax rho c * c / t) := by
  let a := sourceScoreScale cost production effortMax rho c
  have htpos : 0 < t := hc.trans_le ht.1
  have hz : a * c / t ∈ Icc (production 0) (production effortMax) := by
    rw [hg_zero]
    refine ⟨(div_pos (mul_pos ha.1 hc) htpos).le, ?_⟩
    apply le_trans _ ha.2
    apply (div_le_iff₀ htpos).mpr
    exact mul_le_mul_of_nonneg_left ht.1 ha.1.le
  have hi := effortIntervalInverse_spec hmax hg hz
  unfold sourceTwoLevelEffort
  simp only [id_eq, ← mul_div_assoc, hg_zero]
  change max (effortIntervalInverse production effortMax (max (a * c / t) 0)) 0 =
    effortIntervalInverse production effortMax (a * c / t)
  have hz0 : 0 ≤ a * c / t := by simpa only [hg_zero] using hz.1
  rw [max_eq_left hz0, max_eq_left hi.1.1]

/-- Conditional unmeasurable production under the actual two-level effort
profile and a hard effort budget. Independence of unmeasurable skill multiplies
this production mean by that skill's population mean. -/
noncomputable def sourceTwoLevelResidualUtility (cost production : ℝ → ℝ)
    (budget effortMax rho c : ℝ) : ℝ :=
  (∫ t in c..1,
    production (budget - sourceTwoLevelEffort cost production id effortMax rho c t)) / (1 - c)

/-- The output-parameterized residual utility equals the source policy's
conditional residual utility at every positive feasible cutoff. -/
theorem uniformSkillResidualUtility_at_sourceCutoff
    {cost production : ℝ → ℝ} {budget effortMax rho c : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1) (hmax : 0 < effortMax)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : production 0 = 0)
    (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
    uniformSkillResidualUtility cost production budget effortMax rho
        (sourceScoreScale cost production effortMax rho c * c) =
      sourceTwoLevelResidualUtility cost production budget effortMax rho c := by
  have h := uniformSkillOutputInverse_at_sourceCutoff hrho hrho_one hmax
    hcost hcost_mono hcost_zero hcost_max hg hg_mono hg_zero hc
  unfold uniformSkillResidualUtility uniformSkillResidualMean
  rw [h.2.2]
  have hcutoff : sourceScoreScale cost production effortMax rho c * c /
      sourceScoreScale cost production effortMax rho c = c := by
    rw [mul_comm, mul_div_assoc, div_self h.1.1.ne', mul_one]
  rw [hcutoff]
  unfold sourceTwoLevelResidualUtility
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have hc1 : c ≤ 1 := by linarith [hc.2]
  rw [uIcc_of_le hc1] at ht
  dsimp only
  rw [sourceTwoLevelEffort_uniform_eq_inverse hmax.le hg hg_zero h.1 hc.1 ht]

/-- Conditional measurable output for the uniform skill quantile `f(t)=t`,
computed from the actual two-level effort profile. -/
noncomputable def sourceTwoLevelMeasurableUtility (cost production : ℝ → ℝ)
    (effortMax rho c : ℝ) : ℝ :=
  (∫ t in c..1,
    production (sourceTwoLevelEffort cost production id effortMax rho c t) * t) / (1 - c)

/-- Score equalization makes the actual conditional measurable utility equal
to cutoff production times cutoff skill. -/
theorem sourceTwoLevelMeasurableUtility_eq_cutoffScore
    {cost production : ℝ → ℝ} {effortMax rho c : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_zero : production 0 = 0)
    (ha : sourceScoreScale cost production effortMax rho c ∈ Ioc (0 : ℝ) (production effortMax))
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    sourceTwoLevelMeasurableUtility cost production effortMax rho c =
      sourceScoreScale cost production effortMax rho c * c := by
  let a := sourceScoreScale cost production effortMax rho c
  have hvalue (t : ℝ) (ht : t ∈ Icc c 1) :
      production (sourceTwoLevelEffort cost production id effortMax rho c t) * t = a * c := by
    have htpos : 0 < t := hc.1.trans_le ht.1
    have hz : a * c / t ∈ Icc (production 0) (production effortMax) := by
      rw [hg_zero]
      refine ⟨(div_pos (mul_pos ha.1 hc.1) htpos).le, ?_⟩
      apply le_trans _ ha.2
      exact (div_le_iff₀ htpos).mpr (mul_le_mul_of_nonneg_left ht.1 ha.1.le)
    rw [sourceTwoLevelEffort_uniform_eq_inverse hmax hg hg_zero ha hc.1 ht]
    change production (effortIntervalInverse production effortMax (a * c / t)) * t = a * c
    rw [(effortIntervalInverse_spec hmax hg hz).2, div_mul_cancel₀ _ htpos.ne']
  have hI : (∫ t in c..1,
      production (sourceTwoLevelEffort cost production id effortMax rho c t) * t) =
      ∫ _t in c..1, a * c := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hvalue t (by simpa only [uIcc_of_le hc.2.le] using ht)
  unfold sourceTwoLevelMeasurableUtility
  rw [hI, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  rw [mul_comm, mul_div_assoc, div_self (sub_pos.mpr hc.2).ne', mul_one]

/-- For uniform measurable skill and zero baseline production, every interior
two-level cutoff is globally optimal for some strictly interior school weight
under the stated primitive curvature conditions. Both utility components are
the actual conditional population integrals. The comparison includes the
deterministic cutoff, and the hard budget may equal maximal feasible effort. -/
theorem sourceTwoLevelWeightedUtility_exists_optimal_weight_of_effortPrimitives
    {cost costDeriv costSecondDeriv production productionDeriv productionSecondDeriv : ℝ → ℝ}
    {budget effortMax rho mean c : ℝ}
    (hrho : 0 < rho) (hrho_one : rho < 1)
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
      weightedPrivateUtility beta (sourceTwoLevelMeasurableUtility cost production effortMax rho)
        (fun t => mean * sourceTwoLevelResidualUtility cost production budget effortMax rho t) d ≤
      weightedPrivateUtility beta (sourceTwoLevelMeasurableUtility cost production effortMax rho)
        (fun t => mean * sourceTwoLevelResidualUtility cost production budget effortMax rho t) c := by
  have hsubset : Icc (0 : ℝ) effortMax ⊆ Icc 0 budget :=
    fun _ he => ⟨he.1, he.2.trans hbudget⟩
  have hgE := hg.mono hsubset
  have hmonoE := hg_mono.mono hsubset
  let a := sourceScoreScale cost production effortMax rho
  have hpolicy (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1 - rho)) :=
    uniformSkillOutputInverse_at_sourceCutoff hrho hrho_one hmax hcost hcost_mono
      hcost_zero hcost_max hgE hmonoE hg_zero hd
  have hc' : c ∈ Ioc (0 : ℝ) (1 - rho) := ⟨hc.1, hc.2.le⟩
  have htarget : a c * c ∈ Ioo (0 : ℝ) (production effortMax * (1 - rho)) := by
    refine ⟨(hpolicy c hc').2.1.1, ?_⟩
    calc
      a c * c ≤ production effortMax * c := mul_le_mul_of_nonneg_right
        (hpolicy c hc').1.2 hc.1.le
      _ < production effortMax * (1 - rho) := mul_lt_mul_of_pos_left hc.2
        ((hpolicy c hc').1.1.trans_le (hpolicy c hc').1.2)
  obtain ⟨beta, hbeta, hopt⟩ :=
    uniformSkillResidualUtility_exists_supporting_weight_of_effortPrimitives
      hrho hrho_one hmax hbudget hcost hcost_mono hcost_zero hcost_max hp' hp''
      hg hg_mono hg_zero hg_conc hg_sq hg' hg'' hg''_cont hcostRatio
      (show (0 : ℝ) < 1 by norm_num) hmean htarget
  have hM (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1 - rho)) :=
    sourceTwoLevelMeasurableUtility_eq_cutoffScore hmax.le hgE hg_zero (hpolicy d hd).1
      (show d ∈ Ioo (0 : ℝ) 1 from ⟨hd.1, by linarith [hd.2]⟩)
  have hU (d : ℝ) (hd : d ∈ Ioc (0 : ℝ) (1 - rho)) :=
    uniformSkillResidualUtility_at_sourceCutoff (budget := budget) hrho hrho_one hmax
      hcost hcost_mono hcost_zero hcost_max hgE hmonoE hg_zero hd
  refine ⟨beta, hbeta, ?_⟩
  intro d hd
  have h := hopt (a d * d) (hpolicy d hd).2.1
  simp only [weightedPrivateUtility, one_mul] at h ⊢
  rw [hM d hd, hM c hc', ← hU d hd, ← hU c hc']
  exact h

end LBG22StrategicRanking
