import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.Order.Monotone

/-!
# Monotone Continuity Witnesses

Reusable witness lemmas for one-dimensional monotone functions.  Monotone real
functions have only countably many discontinuities, so every nonempty real
open interval contains a continuity point.  This is often the first analytic
witness needed in continuum ranking and large-deviation arguments.
-/

namespace AppliedModelingLib

open Set
open Filter Topology

/--
An injective real curve with a nonnegative derivative on the interior of a
closed interval is strictly increasing there.  The continuity and derivative
premises include the endpoint behavior needed by the one-dimensional mean
value argument.
-/
theorem strictMonoOn_Icc_of_continuousOn_hasDerivAt_nonneg_injOn
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x, x ∈ Ioo a b → HasDerivAt f (f' x) x)
    (hnonneg : ∀ x, x ∈ Ioo a b → 0 ≤ f' x)
    (hinj : (Icc a b).InjOn f) :
    StrictMonoOn f (Icc a b) := by
  apply (monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont ?_ ?_).strictMonoOn_of_injOn
    hinj
  · intro x hx
    rw [interior_Icc] at hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hderiv x hx).deriv]
    exact hnonneg x hx

/--
A strictly increasing real function with finite limit `L` at `+∞` stays
strictly below `L` at every finite point.
-/
theorem strictMono_lt_tendsto_atTop_limit
    {f : ℝ → ℝ} {L : ℝ} (hf : StrictMono f)
    (hlim : Filter.Tendsto f Filter.atTop (nhds L)) (x : ℝ) :
    f x < L := by
  let y : ℝ := x + 1
  have hxy : x < y := by
    dsimp [y]
    linarith
  have hy_le : f y ≤ L := by
    by_contra hnot
    have hL_lt : L < f y := lt_of_not_ge hnot
    have hlt : ∀ᶠ z in Filter.atTop, f z < f y :=
      hlim (isOpen_Iio.mem_nhds (show L ∈ Iio (f y) by exact hL_lt))
    have hgt : ∀ᶠ z in Filter.atTop, f y < f z :=
      (Filter.eventually_gt_atTop y).mono fun z hz => hf hz
    obtain ⟨z, hzlt, hzgt⟩ := (hlt.and hgt).exists
    exact (not_lt_of_ge hzlt.le) hzgt
  exact (hf hxy).trans_le hy_le

/--
A monotone real function with finite limit `L` at `+∞` stays strictly below
`L` at `x` if it has a strict increase somewhere to the right of `x`.
-/
theorem monotone_lt_tendsto_atTop_limit_of_exists_strict_right
    {f : ℝ → ℝ} {L x : ℝ} (hf : Monotone f)
    (hlim : Filter.Tendsto f Filter.atTop (nhds L))
    (hstrict : ∃ y : ℝ, x < y ∧ f x < f y) :
    f x < L := by
  rcases hstrict with ⟨y, _hxy, hxy_val⟩
  have hy_le : f y ≤ L := by
    by_contra hnot
    have hL_lt : L < f y := lt_of_not_ge hnot
    have hlt : ∀ᶠ z in Filter.atTop, f z < f y :=
      hlim (isOpen_Iio.mem_nhds (show L ∈ Iio (f y) by exact hL_lt))
    have hge : ∀ᶠ z in Filter.atTop, f y ≤ f z :=
      (Filter.eventually_ge_atTop y).mono fun z hz => hf hz
    obtain ⟨z, hzlt, hzge⟩ := (hlt.and hge).exists
    exact not_lt_of_ge hzge hzlt
  exact hxy_val.trans_le hy_le

/--
A countable subset of `ℝ` cannot cover a nonempty open interval.  The witness
form is convenient when a proof has first shown that the bad points are
countable.
-/
theorem exists_mem_Ioo_notMem_of_countable
    {a b : ℝ} {s : Set ℝ} (hab : a < b) (hs : s.Countable) :
    ∃ x : ℝ, x ∈ Ioo a b ∧ x ∉ s := by
  by_contra h
  push Not at h
  have hsubset : Ioo a b ⊆ s := by
    intro x hx
    exact h x hx
  have hcount : (Ioo a b : Set ℝ).Countable :=
    hs.mono hsubset
  have hnot : ¬ (Ioo a b : Set ℝ).Countable := by
    simpa [Cardinal.Real.Ioo_countable_iff] using not_le_of_gt hab
  exact hnot hcount

/-- Every nonempty open interval contains a continuity point of a monotone real function. -/
theorem exists_continuousAt_of_monotone_on_Ioo
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Monotone f) :
    ∃ x : ℝ, x ∈ Ioo a b ∧ ContinuousAt f x := by
  obtain ⟨x, hx, hnot_bad⟩ :=
    exists_mem_Ioo_notMem_of_countable (s := {x : ℝ | ¬ ContinuousAt f x})
      hab hf.countable_not_continuousAt
  exact ⟨x, hx, by simpa using hnot_bad⟩

/--
Range-preserving continuity-point witness for monotone Bernoulli-style curves.
If a monotone curve stays in `(0,1)` on a nonempty open interval, then it has a
continuity point there whose value is also in `(0,1)`.
-/
theorem exists_interior_continuity_point_of_monotone_on_Ioo
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : Monotone f)
    (hrange : ∀ x ∈ Ioo a b, 0 < f x ∧ f x < 1) :
    ∃ x : ℝ, x ∈ Ioo a b ∧ ContinuousAt f x ∧ 0 < f x ∧ f x < 1 := by
  obtain ⟨x, hx, hcont⟩ :=
    exists_continuousAt_of_monotone_on_Ioo (f := f) hab hf
  exact ⟨x, hx, hcont, (hrange x hx).1, (hrange x hx).2⟩

/--
Two ordered interior points with values below and above the target bounds give
a whole subinterval on which a monotone Bernoulli-style curve stays in
`(0, 1)`.
-/
theorem exists_Ioo_subset_preimage_Ioo_of_monotone_two_points
    {f : ℝ → ℝ} {lo hi x y : ℝ} (hf : Monotone f)
    (hx : x ∈ Ioo lo hi) (hy : y ∈ Ioo lo hi) (hxy : x < y)
    (h0 : 0 < f x) (h1 : f y < 1) :
    ∃ a b : ℝ, lo ≤ a ∧ a < b ∧ b ≤ hi ∧
      ∀ z : ℝ, z ∈ Ioo a b → 0 < f z ∧ f z < 1 := by
  refine ⟨x, y, hx.1.le, hxy, hy.2.le, ?_⟩
  intro z hz
  exact
    ⟨h0.trans_le (hf hz.1.le),
      (hf hz.2.le).trans_lt h1⟩

/--
If a monotone real function is not constant on an open interval, then it has
two ordered interior points where the value strictly increases.
-/
theorem exists_ordered_strict_value_of_monotone_not_constant_on_Ioo
    {f : ℝ → ℝ} {lo hi : ℝ} (hf : Monotone f)
    (hnot_const :
      ¬ ∀ x : ℝ, x ∈ Ioo lo hi →
        ∀ y : ℝ, y ∈ Ioo lo hi → f x = f y) :
    ∃ x y : ℝ,
      x ∈ Ioo lo hi ∧ y ∈ Ioo lo hi ∧ x < y ∧ f x < f y := by
  push Not at hnot_const
  rcases hnot_const with ⟨x, hx, y, hy, hxy_ne⟩
  by_cases hxy : x < y
  · exact ⟨x, y, hx, hy, hxy,
      lt_of_le_of_ne (hf hxy.le) hxy_ne⟩
  · have hpoints_ne : x ≠ y := by
      intro hxy_eq
      exact hxy_ne (by rw [hxy_eq])
    have hyx : y < x :=
      lt_of_le_of_ne (le_of_not_gt hxy) hpoints_ne.symm
    exact ⟨y, x, hy, hx, hyx,
      lt_of_le_of_ne (hf hyx.le) hxy_ne.symm⟩

/--
Local version of `exists_ordered_strict_value_of_monotone_not_constant_on_Ioo`.
If a monotone function is not constant on any neighborhood of `x0`, then every
positive-radius neighborhood of `x0` contains two ordered points where the
function strictly increases.
-/
theorem exists_ordered_strict_value_near_of_monotone_not_constant_on_nhds
    {f : ℝ → ℝ} {x0 ε : ℝ} (hf : Monotone f) (hε : 0 < ε)
    (hnot_const_nhds :
      ∀ a b : ℝ, a < x0 → x0 < b →
        ¬ ∀ x : ℝ, x ∈ Ioo a b →
          ∀ y : ℝ, y ∈ Ioo a b → f x = f y) :
    ∃ x y : ℝ,
      x ∈ Ioo (x0 - ε) (x0 + ε) ∧
        y ∈ Ioo (x0 - ε) (x0 + ε) ∧
          x < y ∧ f x < f y := by
  let a : ℝ := x0 - ε / 2
  let b : ℝ := x0 + ε / 2
  have ha : a < x0 := by
    dsimp [a]
    linarith
  have hb : x0 < b := by
    dsimp [b]
    linarith
  rcases
      exists_ordered_strict_value_of_monotone_not_constant_on_Ioo
        (f := f) hf (hnot_const_nhds a b ha hb) with
    ⟨x, y, hx, hy, hxy, hval⟩
  have hsub : Ioo a b ⊆ Ioo (x0 - ε) (x0 + ε) := by
    intro z hz
    dsimp [a, b] at hz
    constructor
    · have hleft : x0 - ε < x0 - ε / 2 := by linarith
      exact hleft.trans hz.1
    · have hright : x0 + ε / 2 < x0 + ε := by linarith
      exact hz.2.trans hright
  exact ⟨x, y, hsub hx, hsub hy, hxy, hval⟩

/--
Any neighborhood-eventual real predicate holds on some nondegenerate closed
interval around the point.  This is the source-shrink step commonly needed
after choosing a continuity point in continuum probability arguments.
-/
theorem exists_Icc_subset_eventually_nhds
    {x : ℝ} {P : ℝ → Prop} (hP : ∀ᶠ y in 𝓝 x, P y) :
    ∃ a b : ℝ, a < b ∧ x ∈ Ioo a b ∧
      ∀ y : ℝ, y ∈ Icc a b → P y := by
  rcases (mem_nhds_iff_exists_Ioo_subset.1 hP) with
    ⟨l, u, hxIoo, hsub⟩
  have hlx : l < x := hxIoo.1
  have hxu : x < u := hxIoo.2
  let a : ℝ := (l + x) / 2
  let b : ℝ := (x + u) / 2
  have hla : l < a := by
    dsimp [a]
    linarith
  have hax : a < x := by
    dsimp [a]
    linarith
  have hxb : x < b := by
    dsimp [b]
    linarith
  have hbu : b < u := by
    dsimp [b]
    linarith
  refine ⟨a, b, hax.trans hxb, ⟨hax, hxb⟩, ?_⟩
  intro y hy
  exact hsub ⟨hla.trans_le hy.1, hy.2.trans_lt hbu⟩

/--
If a continuous real-valued function is strictly interior at a point of an
ambient open interval, then it stays strictly interior on some smaller open
interval inside the ambient interval.
-/
theorem exists_Ioo_subset_preimage_Ioo_of_continuousAt_interior
    {f : ℝ → ℝ} {lo hi x : ℝ}
    (hx : x ∈ Ioo lo hi) (hf : ContinuousAt f x)
    (h0 : 0 < f x) (h1 : f x < 1) :
    ∃ a b : ℝ, lo ≤ a ∧ a < b ∧ b ≤ hi ∧
      ∀ y : ℝ, y ∈ Ioo a b → 0 < f y ∧ f y < 1 := by
  have hP :
      ∀ᶠ y in 𝓝 x, y ∈ Ioo lo hi ∧ 0 < f y ∧ f y < 1 := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2,
      hf.eventually (Ioo_mem_nhds h0 h1)] with y hyI hyf
    exact ⟨hyI, hyf⟩
  obtain ⟨a, b, hab, _hxab, hsub⟩ :=
    exists_Icc_subset_eventually_nhds (x := x) hP
  have ha_mem : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb_mem : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hlo_a : lo ≤ a := (hsub a ha_mem).1.1.le
  have hb_hi : b ≤ hi := (hsub b hb_mem).1.2.le
  refine ⟨a, b, hlo_a, hab, hb_hi, ?_⟩
  intro y hy
  exact (hsub y ⟨hy.1.le, hy.2.le⟩).2

/--
Continuous real-valued functions are locally bounded above, and the upper
bound can be chosen positive.  This form is useful when downstream estimates
need a concrete local constant.
-/
theorem exists_pos_eventually_le_of_continuousAt
    {f : ℝ → ℝ} {x : ℝ} (hf : ContinuousAt f x) :
    ∃ G : ℝ, 0 < G ∧ ∀ᶠ y in 𝓝 x, f y ≤ G := by
  obtain ⟨G, hG⟩ := hf.isBoundedUnder_le
  refine ⟨max G 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right G 1)
  · exact hG.mono fun y hy => hy.trans (le_max_left G 1)

end AppliedModelingLib
