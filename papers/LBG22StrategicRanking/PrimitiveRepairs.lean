import LBG22StrategicRanking.MainTheorems
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Primitive conditions for strategic-ranking welfare

The two-level applicant-welfare formula integrates effort costs over a changing
admitted population. Normalizing that population to its own quantile interval
separates the admission mass from relative effort costs. Positive increasing
monotone within-tail skill ratios and geometrically concave cost in produced score imply that
these normalized costs increase with selectivity.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory

/-- The population rank of an applicant at normalized admitted-tail quantile `s`. -/
def admittedTailRank (c s : ℝ) : ℝ := c + (1 - c) * s

theorem admittedTailRank_mem_Icc {c s : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) : admittedTailRank c s ∈ Icc c 1 := by
  dsimp [admittedTailRank]
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hc.2) hs.1,
    mul_nonneg (sub_nonneg.mpr hc.2) (sub_nonneg.mpr hs.2)]

/-- Equal-length increments of a concave function decrease with their base point. -/
theorem concave_increment_le {L : ℝ → ℝ} {D : Set ℝ}
    (hL : ConcaveOn ℝ D L) {a b h : ℝ}
    (ha : a ∈ D) (hbh : b + h ∈ D) (hab : a ≤ b) (hh : 0 ≤ h) :
    L (b + h) - L b ≤ L (a + h) - L a := by
  rcases eq_or_lt_of_le hab with rfl | hab
  · exact le_rfl
  have hd : 0 < b - a + h := by linarith
  have hw : 0 ≤ h / (b - a + h) := div_nonneg hh hd.le
  have hv : 0 ≤ (b - a) / (b - a + h) := div_nonneg (sub_nonneg.mpr hab.le) hd.le
  have hsum : h / (b - a + h) + (b - a) / (b - a + h) = 1 := by
    field_simp
    ring
  have hfirst := hL.2 ha hbh hv hw (by linarith)
  have hsecond := hL.2 ha hbh hw hv hsum
  have hx : (b - a) / (b - a + h) * a + h / (b - a + h) * (b + h) = a + h := by
    field_simp
    ring
  have hy : h / (b - a + h) * a + (b - a) / (b - a + h) * (b + h) = b := by
    field_simp
    ring
  simp only [smul_eq_mul, hx] at hfirst
  simp only [smul_eq_mul, hy] at hsecond
  have hsa := congrArg (fun z => z * L a) hsum
  have hsb := congrArg (fun z => z * L (b + h)) hsum
  nlinarith only [hfirst, hsecond, hsa, hsb]

/-- Log-concavity and increasing skill imply that proportional upper-tail skill
advantages shrink as the admission cutoff rises. No differentiability is required. -/
theorem admittedTail_skill_ratio_monotone {f : ℝ → ℝ}
    (hf_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < f t)
    (hf_mono : MonotoneOn f (Ioc (0 : ℝ) 1))
    (hf_log : ConcaveOn ℝ (Ioc (0 : ℝ) 1) (fun t => Real.log (f t)))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    MonotoneOn (fun c => f c / f (admittedTailRank c s)) (Ioc (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hta := admittedTailRank_mem_Icc ⟨ha.1.le, ha.2⟩ hs
  have htb := admittedTailRank_mem_Icc ⟨hb.1.le, hb.2⟩ hs
  have hta' : admittedTailRank a s ∈ Ioc (0 : ℝ) 1 := ⟨ha.1.trans_le hta.1, hta.2⟩
  have htb' : admittedTailRank b s ∈ Ioc (0 : ℝ) 1 := ⟨hb.1.trans_le htb.1, htb.2⟩
  have hh : 0 ≤ (1 - b) * s := mul_nonneg (sub_nonneg.mpr hb.2) hs.1
  have hx : a + (1 - b) * s ∈ Ioc (0 : ℝ) 1 := by
    constructor
    · linarith [ha.1]
    · dsimp [admittedTailRank] at htb
      linarith [htb.2]
  have horder : a + (1 - b) * s ≤ admittedTailRank a s := by
    dsimp [admittedTailRank]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) hs.1]
  have hinc := concave_increment_le hf_log ha htb' hab hh
  have hlogmono : Real.log (f (a + (1 - b) * s)) ≤
      Real.log (f (admittedTailRank a s)) :=
    Real.log_le_log (hf_pos _ hx) (hf_mono hx hta' horder)
  have hlog : Real.log (f a / f (admittedTailRank a s)) ≤
      Real.log (f b / f (admittedTailRank b s)) := by
    rw [Real.log_div (hf_pos _ ha).ne' (hf_pos _ hta').ne',
      Real.log_div (hf_pos _ hb).ne' (hf_pos _ htb').ne']
    dsimp [admittedTailRank] at *
    linarith
  exact (Real.log_le_log_iff (div_pos (hf_pos _ ha) (hf_pos _ hta'))
    (div_pos (hf_pos _ hb) (hf_pos _ htb'))).mp hlog

/-- Cost in produced-score units, `cost ∘ productionInv`. This is determined by
the effort-cost and technology primitives rather than by a welfare objective. -/
def costInScore (cost productionInv : ℝ → ℝ) (score : ℝ) : ℝ :=
  cost (productionInv score)

/-- A positive geometrically concave score-cost function has increasing
relative cost `phi(r*y)/phi(y)` as the score scale `y` increases, for `0<r≤1`. -/
theorem relativeScoreCost_monotone_of_geometricConcavity {phi : ℝ → ℝ} {scoreMax : ℝ}
    (hphi_pos : ∀ y ∈ Ioc (0 : ℝ) scoreMax, 0 < phi y)
    (hphi_geo : ConcaveOn ℝ (Iic (Real.log scoreMax))
      (fun z => Real.log (phi (Real.exp z))))
    {r : ℝ} (hr : 0 < r) (hr_one : r ≤ 1) :
    MonotoneOn (fun y => phi (r * y) / phi y) (Ioc (0 : ℝ) scoreMax) := by
  intro a ha b hb hab
  have hlogr : Real.log r ≤ 0 := Real.log_nonpos hr.le hr_one
  have hlogab := Real.log_le_log ha.1 hab
  have hla := Real.log_le_log ha.1 ha.2
  have hlb := Real.log_le_log hb.1 hb.2
  have hra : r * a ∈ Ioc (0 : ℝ) scoreMax :=
    ⟨mul_pos hr ha.1, (mul_le_of_le_one_left ha.1.le hr_one).trans ha.2⟩
  have hrb : r * b ∈ Ioc (0 : ℝ) scoreMax :=
    ⟨mul_pos hr hb.1, (mul_le_of_le_one_left hb.1.le hr_one).trans hb.2⟩
  have hinc := concave_increment_le hphi_geo
    (a := Real.log r + Real.log a) (b := Real.log r + Real.log b)
    (h := -Real.log r)
    (show Real.log r + Real.log a ≤ Real.log scoreMax by linarith)
    (show Real.log r + Real.log b + -Real.log r ≤ Real.log scoreMax by linarith)
    (by linarith) (by linarith)
  have hcancel (z : ℝ) : Real.log r + z + -Real.log r = z := by ring
  simp only [hcancel, Real.exp_add, Real.exp_log hr, Real.exp_log ha.1,
    Real.exp_log hb.1] at hinc
  have hlog : Real.log (phi (r * a) / phi a) ≤
      Real.log (phi (r * b) / phi b) := by
    rw [Real.log_div (hphi_pos _ hra).ne' (hphi_pos _ ha).ne',
      Real.log_div (hphi_pos _ hrb).ne' (hphi_pos _ hb).ne']
    linarith
  exact (Real.log_le_log_iff
    (div_pos (hphi_pos _ hra) (hphi_pos _ ha))
    (div_pos (hphi_pos _ hrb) (hphi_pos _ hb))).mp hlog

/-- A zero-cost production floor does not prevent increasing relative costs.
Geometric concavity is needed only above the floor, where costs are positive. -/
theorem relativeScoreCost_monotone_of_geometricConcavity_aboveFloor
    {phi : ℝ → ℝ} {scoreFloor scoreMax : ℝ}
    (hfloor : 0 ≤ scoreFloor)
    (hphi_nonneg : ∀ y ∈ Ioc (0 : ℝ) scoreMax, 0 ≤ phi y)
    (hphi_zero : ∀ y ∈ Ioc (0 : ℝ) scoreMax, y ≤ scoreFloor → phi y = 0)
    (hphi_pos : ∀ y ∈ Ioc scoreFloor scoreMax, 0 < phi y)
    (hphi_geo : ConcaveOn ℝ {z | scoreFloor < Real.exp z ∧ Real.exp z ≤ scoreMax}
      (fun z => Real.log (phi (Real.exp z))))
    {r : ℝ} (hr : 0 < r) (hr_one : r ≤ 1) :
    MonotoneOn (fun y => phi (r * y) / phi y) (Ioc scoreFloor scoreMax) := by
  intro a ha b hb hab
  have ha0 : 0 < a := hfloor.trans_lt ha.1
  have hb0 : 0 < b := hfloor.trans_lt hb.1
  have hra : r * a ∈ Ioc (0 : ℝ) scoreMax :=
    ⟨mul_pos hr ha0, (mul_le_of_le_one_left ha0.le hr_one).trans ha.2⟩
  have hrb : r * b ∈ Ioc (0 : ℝ) scoreMax :=
    ⟨mul_pos hr hb0, (mul_le_of_le_one_left hb0.le hr_one).trans hb.2⟩
  change phi (r * a) / phi a ≤ phi (r * b) / phi b
  by_cases hlow : r * a ≤ scoreFloor
  · rw [hphi_zero _ hra hlow, zero_div]
    exact div_nonneg (hphi_nonneg _ hrb) (hphi_pos _ hb).le
  have hra' : r * a ∈ Ioc scoreFloor scoreMax := ⟨lt_of_not_ge hlow, hra.2⟩
  have hrb' : r * b ∈ Ioc scoreFloor scoreMax :=
    ⟨hra'.1.trans_le (mul_le_mul_of_nonneg_left hab hr.le), hrb.2⟩
  have hlogr : Real.log r ≤ 0 := Real.log_nonpos hr.le hr_one
  have hcancel (z : ℝ) : Real.log r + z + -Real.log r = z := by ring
  have hinc := concave_increment_le hphi_geo
    (a := Real.log r + Real.log a) (b := Real.log r + Real.log b)
    (h := -Real.log r)
    (by simpa only [mem_setOf_eq, Real.exp_add, Real.exp_log hr, Real.exp_log ha0]
      using hra')
    (by simpa only [mem_setOf_eq, hcancel, Real.exp_log hb0] using hb)
    (by linarith [Real.log_le_log ha0 hab]) (by linarith)
  simp only [hcancel, Real.exp_add, Real.exp_log hr, Real.exp_log ha0,
    Real.exp_log hb0] at hinc
  apply (Real.log_le_log_iff (div_pos (hphi_pos _ hra') (hphi_pos _ ha))
    (div_pos (hphi_pos _ hrb') (hphi_pos _ hb))).mp
  rw [Real.log_div (hphi_pos _ hra').ne' (hphi_pos _ ha).ne',
    Real.log_div (hphi_pos _ hrb').ne' (hphi_pos _ hb).ne']
  linarith

/-- Cost relative to the marginal admitted applicant's cost, after normalizing
the admitted population to `[0,1]`. -/
noncomputable def admittedRelativeCost (phi f scale : ℝ → ℝ) (c s : ℝ) : ℝ :=
  phi (scale c * (f c / f (admittedTailRank c s))) / phi (scale c)

/-- Actual population effort cost of the source equal-score two-level profile. -/
noncomputable def twoLevelPopulationCost (phi f scale : ℝ → ℝ) (c : ℝ) : ℝ :=
  ∫ t in c..1, phi (scale c * (f c / f t))

/-- Changing variables to the admitted-tail quantile cancels the population
mass against the cutoff applicant's indifference cost `rho/(1-c)`. -/
theorem twoLevelPopulationCost_eq_normalized {phi f scale : ℝ → ℝ} {rho c : ℝ}
    (hc : c < 1) (hrho : 0 < rho)
    (hthreshold : phi (scale c) = rho / (1 - c)) :
    twoLevelPopulationCost phi f scale c =
      rho * ∫ s in (0 : ℝ)..1, admittedRelativeCost phi f scale c s := by
  have hden : 0 < 1 - c := sub_pos.mpr hc
  have hphi : phi (scale c) ≠ 0 := by rw [hthreshold]; positivity
  have hchange := intervalIntegral.smul_integral_comp_add_mul
    (fun t => phi (scale c * (f c / f t))) (a := 0) (b := 1) (1 - c) c
  simp only [smul_eq_mul, mul_zero, add_zero, mul_one, add_sub_cancel] at hchange
  unfold twoLevelPopulationCost
  rw [← hchange]
  change (1 - c) * (∫ s in (0 : ℝ)..1, phi (scale c * (f c / f (admittedTailRank c s)))) = _
  simp only [admittedRelativeCost, intervalIntegral.integral_div]
  rw [hthreshold]
  field_simp

/-- Increasing upper-tail skill ratios and nonincreasing score-cost elasticity
make the normalized effort-cost share increase with the cutoff. -/
theorem admittedRelativeCost_monotone_of_skillRatio
    {phi f scale : ℝ → ℝ} {hi scoreFloor scoreMax : ℝ}
    (hhi : hi ≤ 1)
    (hfloor : 0 ≤ scoreFloor)
    (hf_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < f t)
    (hf_mono : MonotoneOn f (Ioc (0 : ℝ) 1))
    (hf_ratio : ∀ s ∈ Icc (0 : ℝ) 1,
      MonotoneOn (fun c => f c / f (admittedTailRank c s)) (Ioc (0 : ℝ) 1))
    (hscale_mem : ∀ c ∈ Ioc (0 : ℝ) hi, scale c ∈ Ioc scoreFloor scoreMax)
    (hscale_mono : MonotoneOn scale (Ioc (0 : ℝ) hi))
    (hphi_nonneg : ∀ y ∈ Ioc (0 : ℝ) scoreMax, 0 ≤ phi y)
    (hphi_zero : ∀ y ∈ Ioc (0 : ℝ) scoreMax, y ≤ scoreFloor → phi y = 0)
    (hphi_pos : ∀ y ∈ Ioc scoreFloor scoreMax, 0 < phi y)
    (hphi_mono : MonotoneOn phi (Ioc (0 : ℝ) scoreMax))
    (hphi_geo : ConcaveOn ℝ {z | scoreFloor < Real.exp z ∧ Real.exp z ≤ scoreMax}
      (fun z => Real.log (phi (Real.exp z))))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    MonotoneOn (fun c => admittedRelativeCost phi f scale c s) (Ioc (0 : ℝ) hi) := by
  intro a ha b hb hab
  have ha' : a ∈ Ioc (0 : ℝ) 1 := ⟨ha.1, ha.2.trans hhi⟩
  have hb' : b ∈ Ioc (0 : ℝ) 1 := ⟨hb.1, hb.2.trans hhi⟩
  have hta := admittedTailRank_mem_Icc ⟨ha'.1.le, ha'.2⟩ hs
  have htb := admittedTailRank_mem_Icc ⟨hb'.1.le, hb'.2⟩ hs
  have hta' : admittedTailRank a s ∈ Ioc (0 : ℝ) 1 := ⟨ha.1.trans_le hta.1, hta.2⟩
  have htb' : admittedTailRank b s ∈ Ioc (0 : ℝ) 1 := ⟨hb.1.trans_le htb.1, htb.2⟩
  have hratioA : 0 < f a / f (admittedTailRank a s) :=
    div_pos (hf_pos _ ha') (hf_pos _ hta')
  have hratioB : 0 < f b / f (admittedTailRank b s) :=
    div_pos (hf_pos _ hb') (hf_pos _ htb')
  have hratioOne : f a / f (admittedTailRank a s) ≤ 1 :=
    (div_le_one (hf_pos _ hta')).mpr (hf_mono ha' hta' hta.1)
  have hratioBOne : f b / f (admittedTailRank b s) ≤ 1 :=
    (div_le_one (hf_pos _ htb')).mpr (hf_mono hb' htb' htb.1)
  have hscaleBpos : 0 < scale b := hfloor.trans_lt (hscale_mem _ hb).1
  have hinput_mem (r : ℝ) (hr : 0 < r) (hr_one : r ≤ 1) :
      scale b * r ∈ Ioc (0 : ℝ) scoreMax :=
    ⟨mul_pos hscaleBpos hr,
      (mul_le_of_le_one_right hscaleBpos.le hr_one).trans (hscale_mem _ hb).2⟩
  have hratioOrder := hf_ratio s hs ha' hb' hab
  have hscale := relativeScoreCost_monotone_of_geometricConcavity_aboveFloor
    hfloor hphi_nonneg hphi_zero hphi_pos hphi_geo
    hratioA hratioOne (hscale_mem _ ha) (hscale_mem _ hb) (hscale_mono ha hb hab)
  unfold admittedRelativeCost
  calc
    phi (scale a * (f a / f (admittedTailRank a s))) / phi (scale a) ≤
        phi (scale b * (f a / f (admittedTailRank a s))) / phi (scale b) := by
      simpa only [mul_comm] using hscale
    _ ≤ phi (scale b * (f b / f (admittedTailRank b s))) / phi (scale b) := by
      apply div_le_div_of_nonneg_right _ (hphi_pos _ (hscale_mem _ hb)).le
      exact hphi_mono (hinput_mem _ hratioA hratioOne) (hinput_mem _ hratioB hratioBOne)
        (mul_le_mul_of_nonneg_left hratioOrder hscaleBpos.le)

/-- Log-concave increasing skills satisfy the upper-tail ratio comparison. -/
theorem admittedRelativeCost_monotone {phi f scale : ℝ → ℝ} {hi scoreFloor scoreMax : ℝ}
    (hhi : hi ≤ 1) (hfloor : 0 ≤ scoreFloor)
    (hf_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < f t)
    (hf_mono : MonotoneOn f (Ioc (0 : ℝ) 1))
    (hf_log : ConcaveOn ℝ (Ioc (0 : ℝ) 1) (fun t => Real.log (f t)))
    (hscale_mem : ∀ c ∈ Ioc (0 : ℝ) hi, scale c ∈ Ioc scoreFloor scoreMax)
    (hscale_mono : MonotoneOn scale (Ioc (0 : ℝ) hi))
    (hphi_nonneg : ∀ y ∈ Ioc (0 : ℝ) scoreMax, 0 ≤ phi y)
    (hphi_zero : ∀ y ∈ Ioc (0 : ℝ) scoreMax, y ≤ scoreFloor → phi y = 0)
    (hphi_pos : ∀ y ∈ Ioc scoreFloor scoreMax, 0 < phi y)
    (hphi_mono : MonotoneOn phi (Ioc (0 : ℝ) scoreMax))
    (hphi_geo : ConcaveOn ℝ {z | scoreFloor < Real.exp z ∧ Real.exp z ≤ scoreMax}
      (fun z => Real.log (phi (Real.exp z))))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    MonotoneOn (fun c => admittedRelativeCost phi f scale c s) (Ioc (0 : ℝ) hi) :=
  admittedRelativeCost_monotone_of_skillRatio hhi hfloor hf_pos hf_mono
    (fun _ hs => admittedTail_skill_ratio_monotone hf_pos hf_mono hf_log hs)
    hscale_mem hscale_mono hphi_nonneg hphi_zero hphi_pos hphi_mono hphi_geo hs

/-- Continuity of the production-cost and skill primitives supplies integrability
on the fixed normalized population; it is not an extra utility assumption. -/
theorem admittedRelativeCost_continuousOn {phi f scale : ℝ → ℝ} {c scoreMax : ℝ}
    (hc : c ∈ Ioc (0 : ℝ) 1)
    (hf : ContinuousOn f (Ioc (0 : ℝ) 1))
    (hf_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < f t)
    (hf_mono : MonotoneOn f (Ioc (0 : ℝ) 1))
    (hphi : ContinuousOn phi (Ioc (0 : ℝ) scoreMax))
    (hscale : scale c ∈ Ioc (0 : ℝ) scoreMax) :
    ContinuousOn (admittedRelativeCost phi f scale c) (Icc (0 : ℝ) 1) := by
  have htail : ContinuousOn (admittedTailRank c) (Icc (0 : ℝ) 1) := by
    unfold admittedTailRank
    fun_prop
  have htail_mem : MapsTo (admittedTailRank c) (Icc (0 : ℝ) 1) (Ioc (0 : ℝ) 1) := by
    intro s hs
    have h := admittedTailRank_mem_Icc ⟨hc.1.le, hc.2⟩ hs
    exact ⟨hc.1.trans_le h.1, h.2⟩
  have hden := hf.comp htail htail_mem
  have hratio : ContinuousOn (fun s => f c / f (admittedTailRank c s))
      (Icc (0 : ℝ) 1) :=
    continuousOn_const.div hden (fun s hs => (hf_pos _ (htail_mem hs)).ne')
  have hinput : ContinuousOn (fun s => scale c * (f c / f (admittedTailRank c s)))
      (Icc (0 : ℝ) 1) := continuousOn_const.mul hratio
  have houtput := hphi.comp hinput (fun s hs => show
      scale c * (f c / f (admittedTailRank c s)) ∈ Ioc (0 : ℝ) scoreMax from
    ⟨mul_pos hscale.1 (div_pos (hf_pos _ hc) (hf_pos _ (htail_mem hs))),
      (mul_le_of_le_one_right hscale.1.le
        ((div_le_one (hf_pos _ (htail_mem hs))).mpr
          (hf_mono hc (htail_mem hs)
            (admittedTailRank_mem_Icc ⟨hc.1.le, hc.2⟩ hs).1))).trans hscale.2⟩)
  exact houtput.div_const _

/-- The two-level monotonicity clause of Proposition 3.1, repaired with primitive
shape conditions. The conclusion concerns the actual integral over population
ranks, including the moving lower limit. -/
theorem applicantWelfare_antitone_of_skillRatio
    {phi f scale : ℝ → ℝ} {rho scoreFloor scoreMax : ℝ}
    (hrho : 0 < rho)
    (hfloor : 0 ≤ scoreFloor)
    (hf : ContinuousOn f (Ioc (0 : ℝ) 1))
    (hf_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < f t)
    (hf_mono : MonotoneOn f (Ioc (0 : ℝ) 1))
    (hf_ratio : ∀ s ∈ Icc (0 : ℝ) 1,
      MonotoneOn (fun c => f c / f (admittedTailRank c s)) (Ioc (0 : ℝ) 1))
    (hscale_mem : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), scale c ∈ Ioc scoreFloor scoreMax)
    (hscale_mono : MonotoneOn scale (Ioc (0 : ℝ) (1 - rho)))
    (hphi : ContinuousOn phi (Ioc (0 : ℝ) scoreMax))
    (hphi_nonneg : ∀ y ∈ Ioc (0 : ℝ) scoreMax, 0 ≤ phi y)
    (hphi_zero : ∀ y ∈ Ioc (0 : ℝ) scoreMax, y ≤ scoreFloor → phi y = 0)
    (hphi_pos : ∀ y ∈ Ioc scoreFloor scoreMax, 0 < phi y)
    (hphi_mono : MonotoneOn phi (Ioc (0 : ℝ) scoreMax))
    (hphi_geo : ConcaveOn ℝ {z | scoreFloor < Real.exp z ∧ Real.exp z ≤ scoreMax}
      (fun z => Real.log (phi (Real.exp z))))
    (hthreshold : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), phi (scale c) = rho / (1 - c)) :
    AntitoneOn (fun c => applicantWelfare rho (twoLevelPopulationCost phi f scale c))
      (Ioc (0 : ℝ) (1 - rho)) := by
  intro a ha b hb hab
  have hhi : 1 - rho ≤ 1 := by linarith
  have hcont (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :=
    admittedRelativeCost_continuousOn ⟨hc.1, hc.2.trans hhi⟩ hf hf_pos hf_mono hphi
      ⟨hfloor.trans_lt (hscale_mem c hc).1, (hscale_mem c hc).2⟩
  have hintegral := intervalIntegral.integral_mono_on (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1)
    ((hcont a ha).intervalIntegrable_of_Icc (by norm_num))
    ((hcont b hb).intervalIntegrable_of_Icc (by norm_num))
    (fun s hs => admittedRelativeCost_monotone_of_skillRatio hhi hfloor hf_pos hf_mono hf_ratio
      hscale_mem hscale_mono hphi_nonneg hphi_zero hphi_pos hphi_mono hphi_geo hs ha hb hab)
  apply applicantWelfare_nonincreasing_when_cost_increases
  rw [twoLevelPopulationCost_eq_normalized (by linarith [ha.2]) hrho (hthreshold a ha),
    twoLevelPopulationCost_eq_normalized (by linarith [hb.2]) hrho (hthreshold b hb)]
  exact mul_le_mul_of_nonneg_left hintegral hrho.le

/-- Log-concave skills and geometric score-cost concavity imply decreasing
applicant welfare as the two-level cutoff rises. -/
theorem applicantWelfare_antitone_of_geometricScoreCost
    {phi f scale : ℝ → ℝ} {rho scoreFloor scoreMax : ℝ}
    (hrho : 0 < rho) (hfloor : 0 ≤ scoreFloor)
    (hf : ContinuousOn f (Ioc (0 : ℝ) 1))
    (hf_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < f t)
    (hf_mono : MonotoneOn f (Ioc (0 : ℝ) 1))
    (hf_log : ConcaveOn ℝ (Ioc (0 : ℝ) 1) (fun t => Real.log (f t)))
    (hscale_mem : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), scale c ∈ Ioc scoreFloor scoreMax)
    (hscale_mono : MonotoneOn scale (Ioc (0 : ℝ) (1 - rho)))
    (hphi : ContinuousOn phi (Ioc (0 : ℝ) scoreMax))
    (hphi_nonneg : ∀ y ∈ Ioc (0 : ℝ) scoreMax, 0 ≤ phi y)
    (hphi_zero : ∀ y ∈ Ioc (0 : ℝ) scoreMax, y ≤ scoreFloor → phi y = 0)
    (hphi_pos : ∀ y ∈ Ioc scoreFloor scoreMax, 0 < phi y)
    (hphi_mono : MonotoneOn phi (Ioc (0 : ℝ) scoreMax))
    (hphi_geo : ConcaveOn ℝ {z | scoreFloor < Real.exp z ∧ Real.exp z ≤ scoreMax}
      (fun z => Real.log (phi (Real.exp z))))
    (hthreshold : ∀ c ∈ Ioc (0 : ℝ) (1 - rho), phi (scale c) = rho / (1 - c)) :
    AntitoneOn (fun c => applicantWelfare rho (twoLevelPopulationCost phi f scale c))
      (Ioc (0 : ℝ) (1 - rho)) :=
  applicantWelfare_antitone_of_skillRatio hrho hfloor hf hf_pos hf_mono
    (fun _ hs => admittedTail_skill_ratio_monotone hf_pos hf_mono hf_log hs)
    hscale_mem hscale_mono hphi hphi_nonneg hphi_zero hphi_pos hphi_mono hphi_geo hthreshold

/-- The source's strictly convex nonnegative cost, minimized at zero, is
strictly increasing on nonnegative efforts. -/
theorem sourceCost_strictMonoOn_of_strictConvex
    {cost : ℝ → ℝ} (hcost : StrictConvexOn ℝ (Ici 0) cost)
    (hnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hzero : cost 0 = 0) :
    StrictMonoOn cost (Ici 0) := by
  have hmin : IsMinOn cost (Ici 0) 0 := by
    intro e he
    simpa only [hzero] using hnonneg e he
  have hpos (e : ℝ) (he : 0 < e) : 0 < cost e := by
    by_contra hn
    have hz : cost e = 0 := le_antisymm (le_of_not_gt hn) (hnonneg e he.le)
    have hmine : IsMinOn cost (Ici 0) e := by
      intro x hx
      simpa only [hz] using hnonneg x hx
    have heq := hcost.eq_of_isMinOn hmin hmine (by simp) he.le
    linarith
  intro a ha b hb hab
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ a from ha) with rfl | ha0
  · simpa only [hzero] using hpos b hab
  have hmono := hcost.convexOn.strictMonoOn
    (by simp) ha0 (by simpa only [hzero] using hpos a ha0)
  exact hmono ⟨ha, by simp⟩ ⟨hb, hab.le⟩ hab

/-- The maximal possible reward determines a finite effort cap from the source
cost primitives. Its existence is not an extra bounded-effort assumption. -/
theorem exists_unitCost_effort_of_sourcePrimitives
    {cost : ℝ → ℝ} (hcont : ContinuousOn cost (Ici 0))
    (hcost : StrictConvexOn ℝ (Ici 0) cost)
    (hnonneg : ∀ e ∈ Ici (0 : ℝ), 0 ≤ cost e) (hzero : cost 0 = 0) :
    ∃ effortMax : ℝ, 0 < effortMax ∧ cost effortMax = 1 ∧
      StrictMonoOn cost (Ici 0) := by
  have hmono := sourceCost_strictMonoOn_of_strictConvex hcost hnonneg hzero
  have hp1 : 0 < cost 1 := by
    simpa only [hzero] using hmono (show (0 : ℝ) ∈ Ici 0 by simp)
      (show (1 : ℝ) ∈ Ici 0 by norm_num) (by norm_num)
  let R := max 1 (1 / cost 1)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR1
  have hRcost : 1 ≤ R * cost 1 := (div_le_iff₀ hp1).mp (le_max_right _ _)
  have hi : 0 ≤ 1 - R⁻¹ := by
    have := (inv_le_one₀ hRpos).mpr hR1
    linarith
  have hconv := hcost.convexOn.2 (show (0 : ℝ) ∈ Ici 0 by simp) hRpos.le
    hi (inv_nonneg.mpr hRpos.le) (by ring : 1 - R⁻¹ + R⁻¹ = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, inv_mul_cancel₀ hRpos.ne', hzero] at hconv
  have hbound : cost 1 * R ≤ cost R :=
    (le_div_iff₀ hRpos).mp (by simpa only [div_eq_mul_inv, mul_comm] using hconv)
  have hRreward : 1 ≤ cost R := by nlinarith
  have himage : (1 : ℝ) ∈ cost '' Icc 0 R := intermediate_value_Icc hRpos.le
    (hcont.mono Icc_subset_Ici_self) ⟨by rw [hzero]; norm_num, hRreward⟩
  rcases himage with ⟨effortMax, hcap, hcapcost⟩
  refine ⟨effortMax, ?_, hcapcost, hmono⟩
  rcases eq_or_lt_of_le hcap.1 with heq | hpos
  · subst effortMax
    rw [hzero] at hcapcost
    norm_num at hcapcost
  · exact hpos

/-- The inverse on the effort interval used by feasible ranking policies. -/
noncomputable def effortIntervalInverse (f : ℝ → ℝ) (effortMax : ℝ) : ℝ → ℝ :=
  Function.invFunOn f (Icc 0 effortMax)

/-- The interval inverse belongs to the feasible effort interval and realizes
every target in the production range. -/
theorem effortIntervalInverse_spec {f : ℝ → ℝ} {effortMax y : ℝ}
    (hmax : 0 ≤ effortMax) (hf : ContinuousOn f (Icc 0 effortMax))
    (hy : y ∈ Icc (f 0) (f effortMax)) :
    effortIntervalInverse f effortMax y ∈ Icc 0 effortMax ∧
      f (effortIntervalInverse f effortMax y) = y := by
  have hmem : y ∈ f '' Icc 0 effortMax :=
    intermediate_value_Icc hmax hf hy
  exact Function.invFunOn_pos hmem

private noncomputable def effortIntervalOrderIso {f : ℝ → ℝ} {effortMax : ℝ}
    (hmax : 0 ≤ effortMax) (hf : ContinuousOn f (Icc 0 effortMax))
    (hmono : StrictMonoOn f (Icc 0 effortMax)) :
    Icc (0 : ℝ) effortMax ≃o Icc (f 0) (f effortMax) where
  toFun x := ⟨f x, by
    constructor
    · exact hmono.monotoneOn ⟨le_rfl, hmax⟩ x.property x.property.1
    · exact hmono.monotoneOn x.property ⟨hmax, le_rfl⟩ x.property.2⟩
  invFun y := ⟨effortIntervalInverse f effortMax y,
    (effortIntervalInverse_spec hmax hf y.property).1⟩
  left_inv x := by
    apply Subtype.ext
    exact hmono.injOn.leftInvOn_invFunOn x.property
  right_inv y := by
    apply Subtype.ext
    exact (effortIntervalInverse_spec hmax hf y.property).2
  map_rel_iff' := by
    intro x y
    exact hmono.le_iff_le x.property y.property

/-- A continuous strictly increasing technology has a continuous interval inverse. -/
theorem effortIntervalInverse_continuousOn {f : ℝ → ℝ} {effortMax : ℝ}
    (hmax : 0 ≤ effortMax) (hf : ContinuousOn f (Icc 0 effortMax))
    (hmono : StrictMonoOn f (Icc 0 effortMax)) :
    ContinuousOn (effortIntervalInverse f effortMax) (Icc (f 0) (f effortMax)) := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_subtype_val.comp (effortIntervalOrderIso hmax hf hmono).symm.continuous

/-- The constructed interval inverse inherits strict monotonicity. -/
theorem effortIntervalInverse_strictMonoOn {f : ℝ → ℝ} {effortMax : ℝ}
    (hmax : 0 ≤ effortMax) (hf : ContinuousOn f (Icc 0 effortMax))
    (hmono : StrictMonoOn f (Icc 0 effortMax)) :
    StrictMonoOn (effortIntervalInverse f effortMax) (Icc (f 0) (f effortMax)) := by
  intro a ha b hb hab
  have hia := effortIntervalInverse_spec hmax hf ha
  have hib := effortIntervalInverse_spec hmax hf hb
  apply (hmono.lt_iff_lt hia.1 hib.1).mp
  simpa only [hia.2, hib.2] using hab

/-- Interior target production requires strictly interior effort. -/
theorem effortIntervalInverse_mem_Ioo {f : ℝ → ℝ} {effortMax y : ℝ}
    (hmax : 0 ≤ effortMax) (hf : ContinuousOn f (Icc 0 effortMax))
    (hmono : StrictMonoOn f (Icc 0 effortMax))
    (hy : y ∈ Ioo (f 0) (f effortMax)) :
    effortIntervalInverse f effortMax y ∈ Ioo (0 : ℝ) effortMax := by
  have hi := effortIntervalInverse_spec hmax hf ⟨hy.1.le, hy.2.le⟩
  constructor
  · apply (hmono.lt_iff_lt ⟨le_rfl, hmax⟩ hi.1).mp
    simpa only [hi.2] using hy.1
  · apply (hmono.lt_iff_lt hi.1 ⟨hmax, le_rfl⟩).mp
    simpa only [hi.2] using hy.2

/-- Cutoff effort is determined by indifference with rejection; its production
is the common score before multiplying by the cutoff applicant's skill. -/
noncomputable def sourceScoreScale (cost production : ℝ → ℝ) (effortMax rho c : ℝ) : ℝ :=
  production (effortIntervalInverse cost effortMax (rho / (1 - c)))

/-- The actual two-level effort formula from Theorem 2.2 with baseline effort
zero. Scores below baseline production require zero effort; clipping the
inverse's argument makes this convention meaningful when production at zero
effort is positive. -/
noncomputable def sourceTwoLevelEffort (cost production f : ℝ → ℝ)
    (effortMax rho c t : ℝ) : ℝ :=
  max (effortIntervalInverse production effortMax
    (max (sourceScoreScale cost production effortMax rho c * (f c / f t)) (production 0))) 0

/-- Clipping the score target at baseline output realizes the source's
nonnegative-effort constraint, including technologies with positive baseline
output. This identity determines the resulting score, not just the effort. -/
theorem production_clipped_effortIntervalInverse
    {production : ℝ → ℝ} {effortMax y : ℝ}
    (hmax : 0 ≤ effortMax) (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : MonotoneOn production (Icc 0 effortMax)) (hy : y ≤ production effortMax) :
    production (max (effortIntervalInverse production effortMax (max y (production 0))) 0) =
      max y (production 0) := by
  have hg0 := hg_mono ⟨le_rfl, hmax⟩ ⟨hmax, le_rfl⟩ hmax
  have hinv := effortIntervalInverse_spec hmax hg
    (show max y (production 0) ∈ Icc (production 0) (production effortMax) from
      ⟨le_max_right _ _, max_le hy hg0⟩)
  rw [max_eq_left hinv.1.1]
  exact hinv.2

/-- Applicant welfare calculated from the primitive effort profile over the
uniform population, with zero effort below the cutoff. -/
noncomputable def sourceTwoLevelApplicantWelfare (cost production f : ℝ → ℝ)
    (effortMax rho c : ℝ) : ℝ :=
  rho - ∫ t in c..1, cost (sourceTwoLevelEffort cost production f effortMax rho c t)

/-- Proposition 3.1's two-level monotonicity conclusion from skill, cost, and
technology primitives. `effortMax` is the effort costing the maximal reward
one. All inverse functions, their continuity, and the cutoff cost identity are
constructed. The extra shape requirements are increasing upper-tail skill ratios and
geometrically concave cost in produced score above the zero-cost production
floor. In particular, production at zero effort need not vanish. -/
theorem sourceTwoLevelApplicantWelfare_antitone_of_skillRatio
    {cost production f : ℝ → ℝ} {effortMax rho : ℝ}
    (hrho : 0 < rho) (hmax : 0 < effortMax)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : 0 ≤ production 0)
    (hf : ContinuousOn f (Ioc (0 : ℝ) 1))
    (hf_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < f t)
    (hf_mono : MonotoneOn f (Ioc (0 : ℝ) 1))
    (hf_ratio : ∀ s ∈ Icc (0 : ℝ) 1,
      MonotoneOn (fun c => f c / f (admittedTailRank c s)) (Ioc (0 : ℝ) 1))
    (hscoreCost : ConcaveOn ℝ
      {z | production 0 < Real.exp z ∧ Real.exp z ≤ production effortMax}
      (fun z => Real.log (cost (effortIntervalInverse production effortMax (Real.exp z))))) :
    AntitoneOn (sourceTwoLevelApplicantWelfare cost production f effortMax rho)
      (Ioc (0 : ℝ) (1 - rho)) := by
  let phi := fun y => cost (effortIntervalInverse production effortMax (max y (production 0)))
  let scale := sourceScoreScale cost production effortMax rho
  have hginv_spec {y : ℝ} (hy : y ∈ Icc (production 0) (production effortMax)) :=
    effortIntervalInverse_spec hmax.le hg hy
  have hpinv_spec {y : ℝ} (hy : y ∈ Icc 0 (cost effortMax)) :=
    effortIntervalInverse_spec hmax.le hcost (show y ∈ Icc (cost 0) (cost effortMax) by
      simpa only [hcost_zero] using hy)
  have hgmax : production 0 < production effortMax :=
    hg_mono ⟨le_rfl, hmax.le⟩ ⟨hmax.le, le_rfl⟩ hmax
  have hginv_zero : effortIntervalInverse production effortMax (production 0) = 0 :=
    hg_mono.injOn.leftInvOn_invFunOn ⟨le_rfl, hmax.le⟩
  have hclamp {y : ℝ} (hy : y ≤ production effortMax) :
      max y (production 0) ∈ Icc (production 0) (production effortMax) :=
    ⟨le_max_right _ _, max_le hy hgmax.le⟩
  have hreward (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
      rho / (1 - c) ∈ Ioc (0 : ℝ) (cost effortMax) := by
    have hden : 0 < 1 - c := by linarith [hc.2]
    refine ⟨div_pos hrho hden, ?_⟩
    rw [hcost_max, div_le_one hden]
    linarith [hc.2]
  have hq (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :=
    hpinv_spec (show rho / (1 - c) ∈ Icc 0 (cost effortMax) from
      ⟨(hreward c hc).1.le, (hreward c hc).2⟩)
  have hscale_mem (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
      scale c ∈ Ioc (production 0) (production effortMax) := by
    have hqpos : 0 < effortIntervalInverse cost effortMax (rho / (1 - c)) := by
      apply (hcost_mono.lt_iff_lt ⟨le_rfl, hmax.le⟩ (hq c hc).1).mp
      rw [hcost_zero, (hq c hc).2]
      exact (hreward c hc).1
    constructor
    · exact hg_mono ⟨le_rfl, hmax.le⟩ (hq c hc).1 hqpos
    · exact hg_mono.monotoneOn (hq c hc).1 ⟨hmax.le, le_rfl⟩ (hq c hc).1.2
  have hthreshold (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
      phi (scale c) = rho / (1 - c) := by
    change cost (effortIntervalInverse production effortMax (max (scale c) (production 0))) = _
    rw [max_eq_left (hscale_mem c hc).1.le]
    change cost (effortIntervalInverse production effortMax
      (production (effortIntervalInverse cost effortMax (rho / (1 - c))))) = _
    have hleft : effortIntervalInverse production effortMax
        (production (effortIntervalInverse cost effortMax (rho / (1 - c)))) =
        effortIntervalInverse cost effortMax (rho / (1 - c)) :=
      hg_mono.injOn.leftInvOn_invFunOn (hq c hc).1
    rw [hleft]
    exact (hq c hc).2
  have hginv_mono := effortIntervalInverse_strictMonoOn hmax.le hg hg_mono
  have hphi_mono : MonotoneOn phi (Icc 0 (production effortMax)) := by
    intro a ha b hb hab
    apply hcost_mono.monotoneOn (hginv_spec (hclamp ha.2)).1 (hginv_spec (hclamp hb.2)).1
    exact hginv_mono.monotoneOn (hclamp ha.2) (hclamp hb.2) (max_le_max_right _ hab)
  have hphi_zero (y : ℝ) (hy : y ≤ production 0) : phi y = 0 := by
    change cost (effortIntervalInverse production effortMax (max y (production 0))) = 0
    rw [max_eq_right hy, hginv_zero, hcost_zero]
  have hphi_nonneg (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) (production effortMax)) : 0 ≤ phi y := by
    have h := hphi_mono ⟨le_rfl, hg_zero.trans hgmax.le⟩ ⟨hy.1.le, hy.2⟩ hy.1.le
    rwa [hphi_zero 0 hg_zero] at h
  have hphi_pos (y : ℝ) (hy : y ∈ Ioc (production 0) (production effortMax)) :
      0 < phi y := by
    have hinv := hginv_spec ⟨hy.1.le, hy.2⟩
    have hi : 0 < effortIntervalInverse production effortMax y := by
      have h := hginv_mono ⟨le_rfl, hgmax.le⟩ ⟨hy.1.le, hy.2⟩ hy.1
      rwa [hginv_zero] at h
    change 0 < cost (effortIntervalInverse production effortMax (max y (production 0)))
    rw [max_eq_left hy.1.le]
    simpa only [hcost_zero] using hcost_mono ⟨le_rfl, hmax.le⟩ hinv.1 hi
  have hscale_mono : MonotoneOn scale (Ioc (0 : ℝ) (1 - rho)) := by
    intro a ha b hb hab
    apply hg_mono.monotoneOn (hq a ha).1 (hq b hb).1
    apply (hcost_mono.le_iff_le (hq a ha).1 (hq b hb).1).mp
    rw [(hq a ha).2, (hq b hb).2]
    exact twoLevel_highProb_mono_of_cutoff_mono hrho.le hab
      (by linarith [ha.2]) (by linarith [hb.2])
  have hphi_cont : ContinuousOn phi (Icc 0 (production effortMax)) :=
    hcost.comp ((effortIntervalInverse_continuousOn hmax.le hg hg_mono).comp
      (continuous_id.max continuous_const).continuousOn (fun y hy => hclamp hy.2))
      (fun y hy => (hginv_spec (hclamp hy.2)).1)
  have hphi_geo : ConcaveOn ℝ
      {z | production 0 < Real.exp z ∧ Real.exp z ≤ production effortMax}
      (fun z => Real.log (phi (Real.exp z))) :=
    hscoreCost.congr (fun z hz => by dsimp [phi]; rw [max_eq_left hz.1.le])
  have hanti := applicantWelfare_antitone_of_skillRatio hrho hg_zero hf hf_pos hf_mono hf_ratio
    hscale_mem hscale_mono (hphi_cont.mono Ioc_subset_Icc_self) hphi_nonneg
    (fun y _ hy => hphi_zero y hy) hphi_pos
    (hphi_mono.mono Ioc_subset_Icc_self) hphi_geo
    hthreshold
  have hwelfare (c : ℝ) (hc : c ∈ Ioc (0 : ℝ) (1 - rho)) :
      sourceTwoLevelApplicantWelfare cost production f effortMax rho c =
        applicantWelfare rho (twoLevelPopulationCost phi f scale c) := by
    unfold sourceTwoLevelApplicantWelfare applicantWelfare twoLevelPopulationCost
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by linarith [hc.2] : c ≤ 1)] at ht
    have hc' : c ∈ Ioc (0 : ℝ) 1 := ⟨hc.1, by linarith [hc.2]⟩
    have ht' : t ∈ Ioc (0 : ℝ) 1 := ⟨hc.1.trans_le ht.1, ht.2⟩
    have hratio_one : f c / f t ≤ 1 :=
      (div_le_one (hf_pos t ht')).mpr (hf_mono hc' ht' ht.1)
    have hinput : scale c * (f c / f t) ≤ production effortMax :=
      (mul_le_of_le_one_right (hg_zero.trans (hscale_mem c hc).1.le)
        hratio_one).trans (hscale_mem c hc).2
    have hinv_nonneg := (hginv_spec (hclamp hinput)).1.1
    change cost (max (effortIntervalInverse production effortMax
      (max (scale c * (f c / f t)) (production 0))) 0) = phi (scale c * (f c / f t))
    rw [max_eq_left hinv_nonneg]
  intro a ha b hb hab
  rw [hwelfare a ha, hwelfare b hb]
  exact hanti ha hb hab

/-- Log-concave skill is a sufficient primitive condition for the upper-tail
ratio comparison, giving the two-level welfare monotonicity. -/
theorem sourceTwoLevelApplicantWelfare_antitone
    {cost production f : ℝ → ℝ} {effortMax rho : ℝ}
    (hrho : 0 < rho) (hmax : 0 < effortMax)
    (hcost : ContinuousOn cost (Icc 0 effortMax))
    (hcost_mono : StrictMonoOn cost (Icc 0 effortMax))
    (hcost_zero : cost 0 = 0) (hcost_max : cost effortMax = 1)
    (hg : ContinuousOn production (Icc 0 effortMax))
    (hg_mono : StrictMonoOn production (Icc 0 effortMax)) (hg_zero : 0 ≤ production 0)
    (hf : ContinuousOn f (Ioc (0 : ℝ) 1))
    (hf_pos : ∀ t ∈ Ioc (0 : ℝ) 1, 0 < f t)
    (hf_mono : MonotoneOn f (Ioc (0 : ℝ) 1))
    (hf_log : ConcaveOn ℝ (Ioc (0 : ℝ) 1) (fun t => Real.log (f t)))
    (hscoreCost : ConcaveOn ℝ
      {z | production 0 < Real.exp z ∧ Real.exp z ≤ production effortMax}
      (fun z => Real.log (cost (effortIntervalInverse production effortMax (Real.exp z))))) :
    AntitoneOn (sourceTwoLevelApplicantWelfare cost production f effortMax rho)
      (Ioc (0 : ℝ) (1 - rho)) :=
  sourceTwoLevelApplicantWelfare_antitone_of_skillRatio hrho hmax hcost hcost_mono
    hcost_zero hcost_max hg hg_mono hg_zero hf hf_pos hf_mono
    (fun _ hs => admittedTail_skill_ratio_monotone hf_pos hf_mono hf_log hs) hscoreCost

/-- The repaired monotonicity applies to the paper's square-root technology
and quadratic effort cost, including a uniform skill distribution whose lower
endpoint has zero skill. -/
theorem sourceTwoLevelApplicantWelfare_antitone_sqrt_quadratic_uniform
    {rho : ℝ} (hrho : 0 < rho) :
    AntitoneOn (sourceTwoLevelApplicantWelfare (fun e => e ^ 2) Real.sqrt id 1 rho)
      (Ioc (0 : ℝ) (1 - rho)) := by
  have hg_mono : StrictMonoOn Real.sqrt (Icc (0 : ℝ) 1) :=
    Real.strictMonoOn_sqrt.mono Icc_subset_Ici_self
  have hinv {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
      effortIntervalInverse Real.sqrt 1 y = y ^ 2 := by
    have hi := effortIntervalInverse_spec (by norm_num : (0 : ℝ) ≤ 1)
      Real.continuous_sqrt.continuousOn
      (show y ∈ Icc (Real.sqrt 0) (Real.sqrt 1) by simpa using hy)
    calc
      effortIntervalInverse Real.sqrt 1 y = (Real.sqrt (effortIntervalInverse Real.sqrt 1 y)) ^ 2 :=
        (Real.sq_sqrt hi.1.1).symm
      _ = y ^ 2 := congrArg (fun x => x ^ 2) hi.2
  apply sourceTwoLevelApplicantWelfare_antitone hrho (by norm_num)
    (continuous_pow 2).continuousOn
    (fun _ ha _ _ hab => pow_lt_pow_left₀ hab ha.1 (by norm_num : (2 : ℕ) ≠ 0))
    (by norm_num) (by norm_num) Real.continuous_sqrt.continuousOn hg_mono
    (by norm_num) continuous_id.continuousOn (fun _ ht => ht.1)
    (monotone_id.monotoneOn _)
    (strictConcaveOn_log_Ioi.concaveOn.subset Ioc_subset_Ioi_self (convex_Ioc 0 1))
  have hD : {z : ℝ | Real.sqrt 0 < Real.exp z ∧ Real.exp z ≤ Real.sqrt 1} = Iic 0 := by
    ext z
    simp only [Real.sqrt_zero, Real.sqrt_one, mem_setOf_eq, Real.exp_pos, true_and,
      Real.exp_le_one_iff, mem_Iic]
  rw [hD]
  have hlinear : ConcaveOn ℝ (Iic (0 : ℝ)) (fun z => (4 : ℝ) * z) :=
    (concaveOn_id (convex_Iic 0)).smul (by norm_num)
  apply hlinear.congr
  intro z hz
  change 4 * z = Real.log (effortIntervalInverse Real.sqrt 1 (Real.exp z) ^ 2)
  rw [hinv ⟨(Real.exp_pos z).le, Real.exp_le_one_iff.mpr hz⟩]
  simp only [Real.log_pow, Real.log_exp]
  ring

end LBG22StrategicRanking
