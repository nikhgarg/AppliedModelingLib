import LBG22StrategicRanking.MainTheorems

namespace LBG22StrategicRanking

open Filter

/-!
Formula-level lemmas for the second-price effort expression in Lemma
`lem:effort`.  This file proves the local score, feasibility, uniqueness, and
two-level bridge facts used by the finite-band paper-facing endpoint in
`SecondPriceFinite.lean`.  Every analytic fact used below is supplied as a
visible, source-shaped hypothesis.
-/

@[simp]
theorem secondPriceEffort_def
    (e0 : ℝ) (gInv g f : ℝ → ℝ) (tildePrev c theta : ℝ) :
    secondPriceEffort e0 gInv g f tildePrev c theta =
      max (gInv (g tildePrev * f c / f theta)) e0 := rfl

/--
The displayed two-level effort profile from `lem:effort`: low-band applicants
choose the baseline effort `e0`; high-band applicants use the second-price
boundary effort formula.
-/
noncomputable def twoLevelSecondPriceEffort
    {α : Type*} (e0 : ℝ) (gInv g f : ℝ → ℝ) (tilde c : ℝ)
    (actualHigh : α → Prop) [DecidablePred actualHigh] (theta : α → ℝ)
    (x : α) : ℝ :=
  if actualHigh x then secondPriceEffort e0 gInv g f tilde c (theta x) else e0

theorem secondPriceEffort_ge_e0
    (e0 : ℝ) (gInv g f : ℝ → ℝ) (tildePrev c theta : ℝ) :
    e0 ≤ secondPriceEffort e0 gInv g f tildePrev c theta := by
  exact le_max_right _ _

theorem secondPriceEffort_ge_inverse_target
    (e0 : ℝ) (gInv g f : ℝ → ℝ) (tildePrev c theta : ℝ) :
    gInv (g tildePrev * f c / f theta)
      ≤ secondPriceEffort e0 gInv g f tildePrev c theta := by
  exact le_max_left _ _

theorem secondPriceEffort_underbid_inverse_target_ge_e0
    {e0 tildePrev c theta effort : ℝ} {gInv g f : ℝ → ℝ}
    (heffort_feasible : e0 ≤ effort)
    (hunder :
      secondPriceEffort e0 gInv g f tildePrev c theta > effort) :
    e0 ≤ gInv (g tildePrev * f c / f theta) := by
  by_contra hnot
  have htarget_lt : gInv (g tildePrev * f c / f theta) < e0 :=
    lt_of_not_ge hnot
  have hsp_eq :
      secondPriceEffort e0 gInv g f tildePrev c theta = e0 := by
    simp [secondPriceEffort, max_eq_right (le_of_lt htarget_lt)]
  have he0_gt : e0 > effort := by
    rw [hsp_eq] at hunder
    exact hunder
  exact not_lt_of_ge heffort_feasible he0_gt

theorem secondPriceEffort_eq_e0_of_inverse_target_le
    {e0 tildePrev c theta : ℝ} {gInv g f : ℝ → ℝ}
    (h : gInv (g tildePrev * f c / f theta) ≤ e0) :
    secondPriceEffort e0 gInv g f tildePrev c theta = e0 := by
  simp [secondPriceEffort, max_eq_right h]

theorem secondPriceEffort_eq_inverse_target_of_e0_le
    {e0 tildePrev c theta : ℝ} {gInv g f : ℝ → ℝ}
    (h : e0 ≤ gInv (g tildePrev * f c / f theta)) :
    secondPriceEffort e0 gInv g f tildePrev c theta =
      gInv (g tildePrev * f c / f theta) := by
  simp [secondPriceEffort, max_eq_left h]

/--
The source max-score calculation:

`g(e_k(theta)) f(theta) =
 max { g(tilde e_{k-1}) f(c_k), g(e0) f(theta) }`.

The right-inverse hypothesis is local to the boundary target rather than hidden
inside a certificate.
-/
theorem secondPriceEffort_score_eq_max
    {e0 tildePrev c theta : ℝ} {gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hf_theta_pos : 0 < f theta)
    (hInv :
      g (gInv (g tildePrev * f c / f theta))
        = g tildePrev * f c / f theta) :
    g (secondPriceEffort e0 gInv g f tildePrev c theta) * f theta =
      max (g tildePrev * f c) (g e0 * f theta) := by
  have hmap :
      g (max (gInv (g tildePrev * f c / f theta)) e0) =
        max (g (gInv (g tildePrev * f c / f theta))) (g e0) :=
    hg_mono.map_max
  have hcancel :
      (g tildePrev * f c / f theta) * f theta = g tildePrev * f c := by
    field_simp [ne_of_gt hf_theta_pos]
  calc
    g (secondPriceEffort e0 gInv g f tildePrev c theta) * f theta
        = max (g tildePrev * f c / f theta) (g e0) * f theta := by
          simp [secondPriceEffort, hmap, hInv]
    _ = max ((g tildePrev * f c / f theta) * f theta) (g e0 * f theta) := by
          rw [max_mul_of_nonneg _ _ (le_of_lt hf_theta_pos)]
    _ = max (g tildePrev * f c) (g e0 * f theta) := by
          rw [hcancel]

theorem secondPriceEffort_score_eq_max_of_rightInverse
    {e0 tildePrev c theta : ℝ} {gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hf_theta_pos : 0 < f theta)
    (hInv : Function.RightInverse gInv g) :
    g (secondPriceEffort e0 gInv g f tildePrev c theta) * f theta =
      max (g tildePrev * f c) (g e0 * f theta) :=
  secondPriceEffort_score_eq_max hg_mono hf_theta_pos
    (hInv (g tildePrev * f c / f theta))

theorem secondPriceEffort_score_ge_boundary_target
    {e0 tildePrev c theta : ℝ} {gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hf_theta_pos : 0 < f theta)
    (hInv :
      g (gInv (g tildePrev * f c / f theta))
        = g tildePrev * f c / f theta) :
    g tildePrev * f c
      ≤ g (secondPriceEffort e0 gInv g f tildePrev c theta) * f theta := by
  rw [secondPriceEffort_score_eq_max hg_mono hf_theta_pos hInv]
  exact le_max_left _ _

theorem secondPriceEffort_score_ge_baseline
    {e0 tildePrev c theta : ℝ} {gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hf_theta_pos : 0 < f theta)
    (hInv :
      g (gInv (g tildePrev * f c / f theta))
        = g tildePrev * f c / f theta) :
    g e0 * f theta
      ≤ g (secondPriceEffort e0 gInv g f tildePrev c theta) * f theta := by
  rw [secondPriceEffort_score_eq_max hg_mono hf_theta_pos hInv]
  exact le_max_right _ _

/--
Underbidding the displayed second-price effort puts the realized score
strictly below the source boundary target.  This is the forward algebraic
ingredient for the converse direction of Lemma `lem:effort`.
-/
theorem secondPriceEffort_underbid_score_lt_boundary
    {e0 tildePrev c theta effort : ℝ} {gInv g f : ℝ → ℝ}
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hInv :
      g (gInv (g tildePrev * f c / f theta))
        = g tildePrev * f c / f theta)
    (heffort_feasible : e0 ≤ effort)
    (hunder :
      secondPriceEffort e0 gInv g f tildePrev c theta > effort) :
    g effort * f theta < g tildePrev * f c := by
  let inverseTarget := gInv (g tildePrev * f c / f theta)
  have heffort_lt_inverse : effort < inverseTarget := by
    by_contra hnot
    have hinverse_le_effort : inverseTarget ≤ effort := le_of_not_gt hnot
    have hsp_le_effort :
        secondPriceEffort e0 gInv g f tildePrev c theta ≤ effort := by
      unfold secondPriceEffort
      exact max_le hinverse_le_effort heffort_feasible
    exact not_lt_of_ge hsp_le_effort hunder
  have hg_lt :
      g effort < g tildePrev * f c / f theta := by
    have h := hg_strict heffort_lt_inverse
    simpa [inverseTarget, hInv] using h
  calc
    g effort * f theta
        < (g tildePrev * f c / f theta) * f theta :=
          mul_lt_mul_of_pos_right hg_lt hf_theta_pos
    _ = g tildePrev * f c := by
          field_simp [ne_of_gt hf_theta_pos]

/--
Underbidding also makes the lower applicant's score-matching effort strictly
below the boundary effort, when the lower applicant is at the source cutoff
skill for the boundary.  This is the nonempty-interval ingredient in the
appendix converse proof.
-/
theorem secondPriceEffort_underbid_lower_required_effort_lt_boundary
    {e0 tildePrev c theta lowerTheta effort : ℝ} {gInv g f : ℝ → ℝ}
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hf_lower_pos : 0 < f lowerTheta)
    (hcutoff_skill : f lowerTheta = f c)
    (hInv : Function.RightInverse gInv g)
    (heffort_feasible : e0 ≤ effort)
    (hunder :
      secondPriceEffort e0 gInv g f tildePrev c theta > effort) :
    gInv (g effort * f theta / f lowerTheta) < tildePrev := by
  have hscore_lt :
      g effort * f theta < g tildePrev * f c :=
    secondPriceEffort_underbid_score_lt_boundary
      hg_strict hf_theta_pos (hInv (g tildePrev * f c / f theta))
      heffort_feasible hunder
  have htarget_lt : g effort * f theta / f lowerTheta < g tildePrev := by
    rw [div_lt_iff₀ hf_lower_pos]
    simpa [hcutoff_skill] using hscore_lt
  exact hg_strict.lt_iff_lt.mp (by
    rw [hInv (g effort * f theta / f lowerTheta)]
    exact htarget_lt)

theorem scoreMatchingEffort_ge_e0_of_source_skill_order
    {e0 theta lowerTheta effort : ℝ} {gInv g f : ℝ → ℝ}
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (heffort_feasible : e0 ≤ effort)
    (hg_effort_nonneg : 0 ≤ g effort)
    (hf_lower_pos : 0 < f lowerTheta)
    (hskill_order : f lowerTheta ≤ f theta) :
    e0 ≤ gInv (g effort * f theta / f lowerTheta) := by
  have hge0_effort : g e0 ≤ g effort :=
    hg_strict.monotone heffort_feasible
  have hfactor_ge_one : 1 ≤ f theta / f lowerTheta := by
    rw [le_div_iff₀ hf_lower_pos]
    simpa using hskill_order
  have htarget_ge_effort :
      g effort ≤ g effort * (f theta / f lowerTheta) := by
    calc
      g effort = g effort * 1 := by ring
      _ ≤ g effort * (f theta / f lowerTheta) :=
        mul_le_mul_of_nonneg_left hfactor_ge_one hg_effort_nonneg
  have htarget :
      g e0 ≤ g effort * f theta / f lowerTheta := by
    calc
      g e0 ≤ g effort := hge0_effort
      _ ≤ g effort * (f theta / f lowerTheta) := htarget_ge_effort
      _ = g effort * f theta / f lowerTheta := by ring
  apply hg_strict.le_iff_le.mp
  rw [hInv (g effort * f theta / f lowerTheta)]
  exact htarget

theorem scoreMatchingEffort_score_lt_of_lt
    {theta lowerTheta effort d : ℝ} {gInv g f : ℝ → ℝ}
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hf_lower_pos : 0 < f lowerTheta)
    (hlower_lt :
      gInv (g effort * f theta / f lowerTheta) < d) :
    g effort * f theta < g d * f lowerTheta := by
  have htarget_lt : g effort * f theta / f lowerTheta < g d := by
    have h := hg_strict hlower_lt
    simpa [hInv (g effort * f theta / f lowerTheta)] using h
  calc
    g effort * f theta
        = (g effort * f theta / f lowerTheta) * f lowerTheta := by
          field_simp [ne_of_gt hf_lower_pos]
    _ < g d * f lowerTheta :=
          mul_lt_mul_of_pos_right htarget_lt hf_lower_pos

/--
If the boundary effort itself reaches the boundary score for this type, then
the displayed second-price effort is no larger than the boundary effort.
-/
theorem secondPriceEffort_le_boundary_of_reaches_boundary_score
    {e0 tildePrev c theta : ℝ} {gInv g f : ℝ → ℝ}
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hInv :
      g (gInv (g tildePrev * f c / f theta))
        = g tildePrev * f c / f theta)
    (he0_le_tilde : e0 ≤ tildePrev)
    (hreach : g tildePrev * f c ≤ g tildePrev * f theta) :
    secondPriceEffort e0 gInv g f tildePrev c theta ≤ tildePrev := by
  have htarget_le : g tildePrev * f c / f theta ≤ g tildePrev := by
    rw [div_le_iff₀ hf_theta_pos]
    exact hreach
  have hinv_le :
      gInv (g tildePrev * f c / f theta) ≤ tildePrev := by
    apply hg_strict.le_iff_le.mp
    rw [hInv]
    exact htarget_le
  unfold secondPriceEffort
  exact max_le hinv_le he0_le_tilde

theorem secondPriceEffort_le_boundary_of_reaches_boundary_score_of_rightInverse
    {e0 tildePrev c theta : ℝ} {gInv g f : ℝ → ℝ}
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hInv : Function.RightInverse gInv g)
    (he0_le_tilde : e0 ≤ tildePrev)
    (hreach : g tildePrev * f c ≤ g tildePrev * f theta) :
    secondPriceEffort e0 gInv g f tildePrev c theta ≤ tildePrev :=
  secondPriceEffort_le_boundary_of_reaches_boundary_score
    hg_strict hf_theta_pos (hInv (g tildePrev * f c / f theta))
    he0_le_tilde hreach

/--
Minimal-cost boundary property of the source second-price effort formula:
among feasible efforts that reach the boundary score
`g tildePrev * f c`, the displayed effort has weakly lower cost.
-/
theorem secondPriceEffort_cost_le_of_reaches_boundary_score
    {e0 tildePrev c theta d : ℝ} {cost gInv g f : ℝ → ℝ}
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hInv :
      g (gInv (g tildePrev * f c / f theta))
        = g tildePrev * f c / f theta)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hd_feasible : e0 ≤ d)
    (hreach : g tildePrev * f c ≤ g d * f theta) :
    cost (secondPriceEffort e0 gInv g f tildePrev c theta) ≤ cost d := by
  have htarget_le : g tildePrev * f c / f theta ≤ g d := by
    rw [div_le_iff₀ hf_theta_pos]
    exact hreach
  have hinv_le : gInv (g tildePrev * f c / f theta) ≤ d := by
    apply hg_strict.le_iff_le.mp
    rw [hInv]
    exact htarget_le
  have heffort_le : secondPriceEffort e0 gInv g f tildePrev c theta ≤ d := by
    unfold secondPriceEffort
    exact max_le hinv_le hd_feasible
  exact hcost_mono
    (by
      exact secondPriceEffort_ge_e0 e0 gInv g f tildePrev c theta)
    (by simpa using hd_feasible)
    heffort_le

theorem secondPriceEffort_cost_le_of_reaches_boundary_score_of_rightInverse
    {e0 tildePrev c theta d : ℝ} {cost gInv g f : ℝ → ℝ}
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hd_feasible : e0 ≤ d)
    (hreach : g tildePrev * f c ≤ g d * f theta) :
    cost (secondPriceEffort e0 gInv g f tildePrev c theta) ≤ cost d :=
  secondPriceEffort_cost_le_of_reaches_boundary_score
    hg_strict hf_theta_pos (hInv (g tildePrev * f c / f theta))
    hcost_mono hd_feasible hreach

/--
Within one reward band, the effort formula weakly decreases with type whenever
`f` is positive and increasing, the boundary target is nonnegative, and `gInv`
is increasing.
-/
theorem secondPriceEffort_antitone_within_band
    {e0 tildePrev c : ℝ} {gInv g f : ℝ → ℝ}
    (hboundary_nonneg : 0 ≤ g tildePrev * f c)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (hgInv_mono : Monotone gInv) :
    ∀ {theta₁ theta₂ : ℝ}, theta₁ ≤ theta₂ →
      secondPriceEffort e0 gInv g f tildePrev c theta₂
        ≤ secondPriceEffort e0 gInv g f tildePrev c theta₁ := by
  intro theta₁ theta₂ htheta
  unfold secondPriceEffort
  refine max_le_max ?_ le_rfl
  exact hgInv_mono
    (div_le_div_of_nonneg_left hboundary_nonneg (hf_pos theta₁) (hf_mono htheta))

/--
The corresponding post-effort score weakly increases with type within a band.
-/
theorem secondPriceEffort_score_mono_within_band
    {e0 tildePrev c : ℝ} {gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (hbaseline_nonneg : 0 ≤ g e0)
    (hInv :
      ∀ theta,
        g (gInv (g tildePrev * f c / f theta))
          = g tildePrev * f c / f theta) :
    ∀ {theta₁ theta₂ : ℝ}, theta₁ ≤ theta₂ →
      g (secondPriceEffort e0 gInv g f tildePrev c theta₁) * f theta₁
        ≤ g (secondPriceEffort e0 gInv g f tildePrev c theta₂) * f theta₂ := by
  intro theta₁ theta₂ htheta
  rw [secondPriceEffort_score_eq_max hg_mono (hf_pos theta₁) (hInv theta₁)]
  rw [secondPriceEffort_score_eq_max hg_mono (hf_pos theta₂) (hInv theta₂)]
  exact max_le_max le_rfl (mul_le_mul_of_nonneg_left (hf_mono htheta) hbaseline_nonneg)

theorem secondPriceEffort_score_mono_within_band_of_rightInverse
    {e0 tildePrev c : ℝ} {gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (hbaseline_nonneg : 0 ≤ g e0)
    (hInv : Function.RightInverse gInv g) :
    ∀ {theta₁ theta₂ : ℝ}, theta₁ ≤ theta₂ →
      g (secondPriceEffort e0 gInv g f tildePrev c theta₁) * f theta₁
        ≤ g (secondPriceEffort e0 gInv g f tildePrev c theta₂) * f theta₂ :=
  secondPriceEffort_score_mono_within_band hg_mono hf_pos hf_mono
    hbaseline_nonneg (fun theta => hInv (g tildePrev * f c / f theta))

/--
Source-rank form of the within-band score monotonicity theorem: when the
score map is the second-price formula evaluated at the source rank, scores are
monotone in source rank.
-/
theorem secondPriceEffort_score_mono_of_source_rank_formula
    {α : Type*} {preRank score : α → ℝ}
    {e0 tildePrev c : ℝ} {gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (hbaseline_nonneg : 0 ≤ g e0)
    (hInv : Function.RightInverse gInv g)
    (hscore_formula :
      ∀ x,
        score x =
          g (secondPriceEffort e0 gInv g f tildePrev c (preRank x))
            * f (preRank x)) :
    ∀ x y, preRank y ≤ preRank x → score y ≤ score x := by
  intro x y hpre
  rw [hscore_formula y, hscore_formula x]
  exact secondPriceEffort_score_mono_within_band_of_rightInverse
    hg_mono hf_pos hf_mono hbaseline_nonneg hInv hpre

/--
More general source-order form: if the type parameter fed into the
second-price formula is monotone in source rank, then the resulting score map
is monotone in source rank.
-/
theorem secondPriceEffort_score_mono_of_type_mono
    {α : Type*} {preRank theta score : α → ℝ}
    {e0 tildePrev c : ℝ} {gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hf_pos : ∀ theta, 0 < f theta)
    (hf_mono : Monotone f)
    (hbaseline_nonneg : 0 ≤ g e0)
    (hInv : Function.RightInverse gInv g)
    (htheta_mono :
      ∀ x y, preRank y ≤ preRank x → theta y ≤ theta x)
    (hscore_formula :
      ∀ x,
        score x =
          g (secondPriceEffort e0 gInv g f tildePrev c (theta x))
            * f (theta x)) :
    ∀ x y, preRank y ≤ preRank x → score y ≤ score x := by
  intro x y hpre
  rw [hscore_formula y, hscore_formula x]
  exact secondPriceEffort_score_mono_within_band_of_rightInverse
    hg_mono hf_pos hf_mono hbaseline_nonneg hInv (htheta_mono x y hpre)

/--
Piecewise two-level source-order form.  Low-band applicants keep baseline
effort, high-band applicants use the displayed second-price effort, and the
high band is an upper set in source rank.  Under those source primitives the
realized score map is monotone in source rank.
-/
theorem secondPriceEffort_piecewise_score_mono_of_type_mono
    {α : Type*} {preRank theta score : α → ℝ}
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {e0 tildePrev c : ℝ} {gInv g f : ℝ → ℝ}
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
          g (secondPriceEffort e0 gInv g f tildePrev c (theta x))
            * f (theta x)) :
    ∀ x y, preRank y ≤ preRank x → score y ≤ score x := by
  intro x y hpre
  by_cases hy : actualHigh y
  · have hx : actualHigh x := hactualHigh_upper x y hpre hy
    rw [hscore_high y hy, hscore_high x hx]
    exact secondPriceEffort_score_mono_within_band_of_rightInverse
      hg_mono hf_pos hf_mono hbaseline_nonneg hInv (htheta_mono x y hpre)
  · by_cases hx : actualHigh x
    · rw [hscore_low y hy, hscore_high x hx]
      have hbase_le :
          g e0 * f (theta y) ≤ g e0 * f (theta x) :=
        mul_le_mul_of_nonneg_left (hf_mono (htheta_mono x y hpre))
          hbaseline_nonneg
      have hscore_ge :
          g e0 * f (theta x) ≤
            g (secondPriceEffort e0 gInv g f tildePrev c (theta x))
              * f (theta x) :=
        secondPriceEffort_score_ge_baseline hg_mono (hf_pos (theta x))
          (hInv (g tildePrev * f c / f (theta x)))
      exact le_trans hbase_le hscore_ge
    · rw [hscore_low y hy, hscore_low x hx]
      exact mul_le_mul_of_nonneg_left (hf_mono (htheta_mono x y hpre))
        hbaseline_nonneg

/--
Adjacent-band target ordering: if the inductive second-price boundary effort is
strictly above the previous boundary effort, then the new boundary score is
strictly above the previous boundary score.
-/
theorem secondPrice_boundaryTarget_gt_previousBoundaryScore
    {prevAtCutoff tildePrev c : ℝ} {g f : ℝ → ℝ}
    (hg_strict : StrictMono g)
    (hprev : prevAtCutoff < tildePrev)
    (hfc_pos : 0 < f c) :
    g prevAtCutoff * f c < g tildePrev * f c := by
  exact mul_lt_mul_of_pos_right (hg_strict hprev) hfc_pos

theorem secondPrice_boundaryEffort_gt_previous_of_cost_gap
    {prevAtCutoff tildePrev rewardGap : ℝ} {cost : ℝ → ℝ}
    (hprev_le_tilde : prevAtCutoff ≤ tildePrev)
    (hcost :
      cost tildePrev = cost prevAtCutoff + rewardGap)
    (hgap : 0 < rewardGap) :
    prevAtCutoff < tildePrev := by
  have hcost_lt : cost prevAtCutoff < cost tildePrev := by
    rw [hcost]
    linarith
  exact lt_of_le_of_ne hprev_le_tilde (by
    intro h
    subst tildePrev
    exact (lt_irrefl (cost prevAtCutoff)) hcost_lt)

/--
Boundary-effort uniqueness from the source cost equation: if `cost` is
strictly increasing on feasible efforts and a feasible boundary effort exists,
then it is unique.
-/
theorem secondPrice_boundaryEffort_unique_of_exists
    {e0 target : ℝ} {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hexists : ∃ tilde, e0 ≤ tilde ∧ cost tilde = target) :
    ∃! tilde, e0 ≤ tilde ∧ cost tilde = target := by
  rcases hexists with ⟨tilde, htilde_mem, htilde_eq⟩
  refine ⟨tilde, ⟨htilde_mem, htilde_eq⟩, ?_⟩
  intro other hother
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcost_lt : cost other < cost tilde :=
      hcost_strict hother.1 htilde_mem hlt
    rw [htilde_eq, hother.2] at hcost_lt
    exact (lt_irrefl target) hcost_lt
  · have hcost_lt : cost tilde < cost other :=
      hcost_strict htilde_mem hother.1 hgt
    rw [htilde_eq, hother.2] at hcost_lt
    exact (lt_irrefl target) hcost_lt

/--
Boundary-effort existence from a source-visible cost bracket: if the target
cost lies between the cost at the baseline effort and the cost at a feasible
upper effort, continuity supplies a boundary effort reaching the target.
-/
theorem secondPrice_boundaryEffort_exists_of_cost_bracket
    {e0 upper target : ℝ} {cost : ℝ → ℝ}
    (hupper : e0 ≤ upper)
    (hcost_cont : ContinuousOn cost (Set.Icc e0 upper))
    (hlow : cost e0 ≤ target)
    (hhigh : target ≤ cost upper) :
    ∃ tilde, e0 ≤ tilde ∧ tilde ≤ upper ∧ cost tilde = target := by
  have htarget_mem : target ∈ Set.Icc (cost e0) (cost upper) :=
    ⟨hlow, hhigh⟩
  rcases (intermediate_value_Icc hupper hcost_cont htarget_mem) with
    ⟨tilde, htilde_mem, htilde_cost⟩
  exact ⟨tilde, htilde_mem.1, htilde_mem.2, htilde_cost⟩

/--
Boundary-effort existence and uniqueness from a cost bracket plus strict
monotonicity on feasible efforts.
-/
theorem secondPrice_boundaryEffort_unique_of_cost_bracket
    {e0 upper target : ℝ} {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hupper : e0 ≤ upper)
    (hcost_cont : ContinuousOn cost (Set.Icc e0 upper))
    (hlow : cost e0 ≤ target)
    (hhigh : target ≤ cost upper) :
    ∃! tilde, e0 ≤ tilde ∧ cost tilde = target := by
  rcases secondPrice_boundaryEffort_exists_of_cost_bracket
      hupper hcost_cont hlow hhigh with
    ⟨tilde, htilde_low, _htilde_high, htilde_cost⟩
  exact secondPrice_boundaryEffort_unique_of_exists hcost_strict
    ⟨tilde, htilde_low, htilde_cost⟩

/--
Boundary-effort existence from the source-level unbounded-cost condition:
if cost is continuous, tends to infinity along feasible effort, and the target
is above baseline cost, then some feasible effort reaches the target.
-/
theorem secondPrice_boundaryEffort_exists_of_continuous_unbounded
    {e0 target : ℝ} {cost : ℝ → ℝ}
    (hcost_cont : Continuous cost)
    (hcost_atTop : Tendsto cost atTop atTop)
    (hlow : cost e0 ≤ target) :
    ∃ tilde, e0 ≤ tilde ∧ cost tilde = target := by
  have hhigh_eventually : ∀ᶠ upper in atTop, target ≤ cost upper :=
    hcost_atTop.eventually_ge_atTop target
  rcases (hhigh_eventually.and (eventually_ge_atTop e0)).exists with
    ⟨upper, hhigh, hupper⟩
  rcases secondPrice_boundaryEffort_exists_of_cost_bracket
      hupper hcost_cont.continuousOn hlow hhigh with
    ⟨tilde, htilde_low, _htilde_high, htilde_cost⟩
  exact ⟨tilde, htilde_low, htilde_cost⟩

/--
Boundary-effort existence and uniqueness from continuous unbounded cost plus
strict monotonicity on feasible efforts.
-/
theorem secondPrice_boundaryEffort_unique_of_continuous_unbounded
    {e0 target : ℝ} {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hcost_cont : Continuous cost)
    (hcost_atTop : Tendsto cost atTop atTop)
    (hlow : cost e0 ≤ target) :
    ∃! tilde, e0 ≤ tilde ∧ cost tilde = target :=
  secondPrice_boundaryEffort_unique_of_exists hcost_strict
    (secondPrice_boundaryEffort_exists_of_continuous_unbounded
      hcost_cont hcost_atTop hlow)

theorem secondPrice_boundaryTarget_gt_previousBoundaryScore_of_cost_gap
    {prevAtCutoff tildePrev rewardGap c : ℝ} {cost g f : ℝ → ℝ}
    (hg_strict : StrictMono g)
    (hprev_le_tilde : prevAtCutoff ≤ tildePrev)
    (hcost :
      cost tildePrev = cost prevAtCutoff + rewardGap)
    (hgap : 0 < rewardGap)
    (hfc_pos : 0 < f c) :
    g prevAtCutoff * f c < g tildePrev * f c :=
  secondPrice_boundaryTarget_gt_previousBoundaryScore hg_strict
    (secondPrice_boundaryEffort_gt_previous_of_cost_gap
      hprev_le_tilde hcost hgap)
    hfc_pos

theorem secondPrice_score_gt_previousBandSup_of_cost_gap
    {e0 prevAtCutoff tildePrev rewardGap c theta prevSup : ℝ}
    {cost gInv g f : ℝ → ℝ}
    (hg_mono : Monotone g)
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hfc_pos : 0 < f c)
    (hInv :
      g (gInv (g tildePrev * f c / f theta))
        = g tildePrev * f c / f theta)
    (hprevSup_le : prevSup ≤ g prevAtCutoff * f c)
    (hprev_le_tilde : prevAtCutoff ≤ tildePrev)
    (hcost :
      cost tildePrev = cost prevAtCutoff + rewardGap)
    (hgap : 0 < rewardGap) :
    prevSup < g (secondPriceEffort e0 gInv g f tildePrev c theta) * f theta := by
  have hprev_lt_boundary :
      prevSup < g tildePrev * f c :=
    lt_of_le_of_lt hprevSup_le
      (secondPrice_boundaryTarget_gt_previousBoundaryScore_of_cost_gap
        hg_strict hprev_le_tilde hcost hgap hfc_pos)
  exact lt_of_lt_of_le hprev_lt_boundary
    (secondPriceEffort_score_ge_boundary_target hg_mono hf_theta_pos hInv)

theorem secondPrice_no_profitable_deviation_of_reward_gap_le_cost_gap
    {stayReward devReward stayCost devCost : ℝ}
    (hgap : devReward - stayReward ≤ devCost - stayCost) :
    devReward - devCost ≤ stayReward - stayCost := by
  linarith

theorem secondPrice_profitable_deviation_of_cost_gap_lt_reward_gap
    {stayReward devReward stayCost devCost : ℝ}
    (hgap : devCost - stayCost < devReward - stayReward) :
    stayReward - stayCost < devReward - devCost := by
  linarith

/--
Two-level low-band best response.  If `baseCost` is the minimum cost and the
boundary cost exactly equals the base cost plus the high-low reward gap, then a
low-band applicant cannot profit from any deviation: deviations that remain in
the low band pay at least `baseCost`, and deviations that reach the high band
pay at least the boundary cost.
-/
theorem secondPrice_twoLevel_low_band_best_response
    {lowReward highReward baseCost boundaryCost : ℝ}
    {cost : ℝ → ℝ} {reachesHigh : ℝ → Prop} [DecidablePred reachesHigh]
    (hboundary : boundaryCost = baseCost + (highReward - lowReward))
    (hbase_min : ∀ d, baseCost ≤ cost d)
    (hboundary_min : ∀ d, reachesHigh d → boundaryCost ≤ cost d) :
    ∀ d, (if reachesHigh d then highReward else lowReward) - cost d
      ≤ lowReward - baseCost := by
  intro d
  by_cases hd : reachesHigh d
  · have hcost : boundaryCost ≤ cost d := hboundary_min d hd
    simp [hd]
    linarith
  · have hcost : baseCost ≤ cost d := hbase_min d
    simp [hd]
    linarith

/--
Two-level high-band best response.  A high-band applicant cannot profit from a
deviation that still reaches the high band when the actual effort is
minimum-cost among high-reaching efforts, and cannot profit from dropping to
the low band when its actual cost is no more than the boundary cost.
-/
theorem secondPrice_twoLevel_high_band_best_response
    {lowReward highReward baseCost actualCost boundaryCost : ℝ}
    {cost : ℝ → ℝ} {reachesHigh : ℝ → Prop} [DecidablePred reachesHigh]
    (hboundary : boundaryCost = baseCost + (highReward - lowReward))
    (hbase_min : ∀ d, baseCost ≤ cost d)
    (hactual_le_boundary : actualCost ≤ boundaryCost)
    (hactual_min_high : ∀ d, reachesHigh d → actualCost ≤ cost d) :
    ∀ d, (if reachesHigh d then highReward else lowReward) - cost d
      ≤ highReward - actualCost := by
  intro d
  by_cases hd : reachesHigh d
  · have hcost : actualCost ≤ cost d := hactual_min_high d hd
    simp [hd]
    linarith
  · have hcost : baseCost ≤ cost d := hbase_min d
    simp [hd]
    linarith

/--
The displayed two-level second-price effort is weakly no more costly than the
boundary effort for every type above the cutoff.  This is the source argument
that high-band applicants can always fall back to the boundary applicant's
effort, so their actual second-price effort cannot cost more.
-/
theorem secondPrice_twoLevel_highEffort_cost_le_boundary
    {e0 tilde c theta : ℝ} {cost gInv g f : ℝ → ℝ}
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (htilde_feasible : e0 ≤ tilde)
    (hboundary_reaches_at_theta : g tilde * f c ≤ g tilde * f theta) :
    cost (secondPriceEffort e0 gInv g f tilde c theta) ≤ cost tilde :=
  secondPriceEffort_cost_le_of_reaches_boundary_score_of_rightInverse
    hg_strict hf_theta_pos hInv hcost_mono htilde_feasible
    hboundary_reaches_at_theta

/--
Two-level second-price low-band best response with the concrete score boundary
condition.  Any feasible deviation that reaches the high-band boundary score
has cost at least the source boundary effort, so the general low-band
best-response lemma applies.
-/
theorem secondPrice_twoLevel_low_band_best_response_of_score_boundary
    {lowReward highReward e0 tilde c theta : ℝ}
    {cost g f : ℝ → ℝ} {reachesHigh : ℝ → Prop}
    [DecidablePred reachesHigh]
    (hg_strict : StrictMono g)
    (hfc_pos : 0 < f c)
    (hf_theta_le_cutoff : f theta ≤ f c)
    (hg_deviation_nonneg : ∀ d, reachesHigh d → 0 ≤ g d)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hreaches_boundary :
      ∀ d, reachesHigh d → e0 ≤ d → g tilde * f c ≤ g d * f theta)
    (hdeviation_feasible : ∀ d, reachesHigh d → e0 ≤ d) :
    ∀ d, (if reachesHigh d then highReward else lowReward) - cost d
      ≤ lowReward - cost e0 := by
  refine secondPrice_twoLevel_low_band_best_response
    (lowReward := lowReward) (highReward := highReward)
    (baseCost := cost e0) (boundaryCost := cost tilde)
    (cost := cost) (reachesHigh := reachesHigh) ?_ hbase_min ?_
  · exact htilde_cost
  · intro d hd
    have hscore :
        g tilde * f c ≤ g d * f c := by
      exact le_trans (hreaches_boundary d hd (hdeviation_feasible d hd))
        (mul_le_mul_of_nonneg_left hf_theta_le_cutoff
          (hg_deviation_nonneg d hd))
    have hgd : g tilde ≤ g d := by
      exact le_of_mul_le_mul_right hscore hfc_pos
    have htilde_le_d : tilde ≤ d := by
      exact hg_strict.le_iff_le.mp hgd
    exact hcost_mono htilde_feasible (hdeviation_feasible d hd)
      htilde_le_d

/--
Two-level second-price high-band best response with the concrete score
boundary condition.  The actual displayed effort is minimum-cost among
high-reaching deviations, and its cost is bounded by the boundary applicant's
cost, so no high-band applicant profits by changing effort.
-/
theorem secondPrice_twoLevel_high_band_best_response_of_score_boundary
    {lowReward highReward e0 tilde c theta : ℝ}
    {cost gInv g f : ℝ → ℝ} {reachesHigh : ℝ → Prop}
    [DecidablePred reachesHigh]
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hboundary_reaches_at_theta :
      g tilde * f c ≤ g tilde * f theta)
    (hreaches_boundary :
      ∀ d, reachesHigh d → e0 ≤ d → g tilde * f c ≤ g d * f theta)
    (hdeviation_feasible : ∀ d, reachesHigh d → e0 ≤ d) :
    ∀ d, (if reachesHigh d then highReward else lowReward) - cost d
      ≤ highReward -
        cost (secondPriceEffort e0 gInv g f tilde c theta) := by
  refine secondPrice_twoLevel_high_band_best_response
    (lowReward := lowReward) (highReward := highReward)
    (baseCost := cost e0)
    (actualCost := cost (secondPriceEffort e0 gInv g f tilde c theta))
    (boundaryCost := cost tilde) (cost := cost)
    (reachesHigh := reachesHigh) ?_ hbase_min ?_ ?_
  · exact htilde_cost
  · exact secondPrice_twoLevel_highEffort_cost_le_boundary
      hg_strict hf_theta_pos hInv hcost_mono htilde_feasible
      hboundary_reaches_at_theta
  · intro d hd
    exact secondPriceEffort_cost_le_of_reaches_boundary_score_of_rightInverse
      hg_strict hf_theta_pos hInv hcost_mono (hdeviation_feasible d hd)
      (hreaches_boundary d hd (hdeviation_feasible d hd))

/--
Inverse low-band step for the two-level source equilibrium.  If a low-band
applicant is already best responding and all feasible efforts cost at least
the baseline effort, strict cost monotonicity on feasible efforts pins the
chosen effort to `e0`.
-/
theorem secondPrice_twoLevel_low_band_effort_unique_of_best_response
    {lowReward highReward e0 effort : ℝ}
    {cost : ℝ → ℝ} {reachesHigh : ℝ → Prop} [DecidablePred reachesHigh]
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (heffort_feasible : e0 ≤ effort)
    (hactual_low : ¬ reachesHigh effort)
    (hbase_low : ¬ reachesHigh e0)
    (hbest :
      ∀ d, (if reachesHigh d then highReward else lowReward) - cost d
        ≤ (if reachesHigh effort then highReward else lowReward) -
          cost effort) :
    effort = e0 := by
  have hcost_le : cost effort ≤ cost e0 := by
    have h := hbest e0
    simp [hactual_low, hbase_low] at h
    linarith
  have hcost_ge : cost e0 ≤ cost effort := hbase_min effort
  have hcost_eq : cost effort = cost e0 := le_antisymm hcost_le hcost_ge
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (not_lt_of_ge heffort_feasible) hlt
  · have hcost_lt : cost e0 < cost effort :=
      hcost_strict (le_refl e0) heffort_feasible hgt
    rw [hcost_eq] at hcost_lt
    exact (lt_irrefl (cost e0)) hcost_lt

/--
Inverse high-band step for the two-level source equilibrium.  A high-band best
response must use the displayed second-price effort once high-reaching
deviations are exactly the deviations that cross the source boundary score.
-/
theorem secondPrice_twoLevel_high_band_effort_unique_of_best_response
    {lowReward highReward e0 tilde c theta effort : ℝ}
    {cost gInv g f : ℝ → ℝ} {reachesHigh : ℝ → Prop}
    [DecidablePred reachesHigh]
    (hg_strict : StrictMono g)
    (hf_theta_pos : 0 < f theta)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (heffort_feasible : e0 ≤ effort)
    (hactual_high : reachesHigh effort)
    (hreaches_boundary :
      ∀ d, reachesHigh d → e0 ≤ d → g tilde * f c ≤ g d * f theta)
    (hsp_high : reachesHigh (secondPriceEffort e0 gInv g f tilde c theta))
    (hbest :
      ∀ d, (if reachesHigh d then highReward else lowReward) - cost d
        ≤ (if reachesHigh effort then highReward else lowReward) -
          cost effort) :
    effort = secondPriceEffort e0 gInv g f tilde c theta := by
  let sp := secondPriceEffort e0 gInv g f tilde c theta
  have hsp_feasible : e0 ≤ sp := by
    simpa [sp] using secondPriceEffort_ge_e0 e0 gInv g f tilde c theta
  have hsp_cost_le_effort : cost sp ≤ cost effort := by
    simpa [sp] using
      secondPriceEffort_cost_le_of_reaches_boundary_score_of_rightInverse
        (e0 := e0) (tildePrev := tilde) (c := c) (theta := theta)
        (d := effort) (cost := cost) (gInv := gInv) (g := g) (f := f)
        hg_strict hf_theta_pos hInv hcost_mono heffort_feasible
        (hreaches_boundary effort hactual_high heffort_feasible)
  have heffort_cost_le_sp : cost effort ≤ cost sp := by
    have hsp_high' : reachesHigh sp := by
      simpa [sp] using hsp_high
    have h := hbest sp
    simp [hactual_high, hsp_high'] at h
    linarith
  have hcost_eq : cost effort = cost sp :=
    le_antisymm heffort_cost_le_sp hsp_cost_le_effort
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcost_lt : cost effort < cost sp :=
      hcost_strict heffort_feasible hsp_feasible hlt
    rw [hcost_eq] at hcost_lt
    exact (lt_irrefl (cost sp)) hcost_lt
  · have hcost_lt : cost sp < cost effort :=
      hcost_strict hsp_feasible heffort_feasible hgt
    rw [hcost_eq] at hcost_lt
    exact (lt_irrefl (cost sp)) hcost_lt

/--
Pointwise uniqueness of the displayed two-level second-price effort profile:
if an arbitrary effort profile is a source rank best response and the rank
layer is the source two-level threshold layer, then every type chooses the
displayed second-price effort, up to the visible low/high classification.
-/
theorem secondPrice_twoLevel_effort_eq_source_formula_of_best_response
    {α : Type*}
    {lowReward highReward e0 tilde c : ℝ}
    {cost gInv g f : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hbase_low : ∀ x, ¬ actualHigh x → ¬ reachesHigh x e0)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hsp_high :
      ∀ x, actualHigh x →
        reachesHigh x (secondPriceEffort e0 gInv g f tilde c (theta x)))
    (hbest :
      SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort) :
    ∀ x,
      effort x =
        twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta x := by
  classical
  intro x
  have hbest_scalar :
      ∀ d,
        (if reachesHigh x d then highReward else lowReward) - cost d
          ≤ (if reachesHigh x (effort x) then highReward else lowReward) -
            cost (effort x) := by
    intro d
    have h := hbest x d
    have hactual_reward :
        levelReward (rankLevel (rankOfEffort x (effort x))) =
          if reachesHigh x (effort x) then highReward else lowReward := by
      rw [hlevel x (effort x)]
      by_cases hxeffort : reachesHigh x (effort x)
      · simp [hxeffort, hlevel_one]
      · simp [hxeffort, hlevel_zero]
    have hdev_reward :
        levelReward (rankLevel (rankOfEffort x d)) =
          if reachesHigh x d then highReward else lowReward := by
      rw [hlevel x d]
      by_cases hd : reachesHigh x d
      · simp [hd, hlevel_one]
      · simp [hd, hlevel_zero]
    rw [hactual_reward, hdev_reward] at h
    exact h
  by_cases hx : actualHigh x
  · have hactual_high : reachesHigh x (effort x) :=
      (hactual_reaches x).2 hx
    have huniq :
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x) :=
      secondPrice_twoLevel_high_band_effort_unique_of_best_response
        (lowReward := lowReward) (highReward := highReward)
        (e0 := e0) (tilde := tilde) (c := c) (theta := theta x)
        (effort := effort x) (cost := cost) (gInv := gInv) (g := g)
        (f := f) (reachesHigh := reachesHigh x)
        hg_strict (hf_high_pos x hx) hInv hcost_mono hcost_strict
        (heffort_feasible x) hactual_high
        (fun d hd hd_feasible => hreaches_boundary x d hd hd_feasible)
        (hsp_high x hx) hbest_scalar
    simpa [twoLevelSecondPriceEffort, hx] using huniq
  · have hactual_low : ¬ reachesHigh x (effort x) := by
      intro hreach
      exact hx ((hactual_reaches x).1 hreach)
    have huniq : effort x = e0 :=
      secondPrice_twoLevel_low_band_effort_unique_of_best_response
        (lowReward := lowReward) (highReward := highReward)
        (e0 := e0) (effort := effort x) (cost := cost)
        (reachesHigh := reachesHigh x)
        hcost_strict hbase_min (heffort_feasible x) hactual_low
        (hbase_low x hx) hbest_scalar
    simpa [twoLevelSecondPriceEffort, hx] using huniq

/--
Almost-everywhere version of the two-level uniqueness direction.  This matches
the paper's "unique up to measure zero" language: an a.e. source rank best
response in the two-level threshold layer agrees a.e. with the displayed
second-price effort formula.
-/
theorem secondPrice_twoLevel_effort_eq_source_formula_ae_of_best_responseAE
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {lowReward highReward e0 tilde c : ℝ}
    {cost gInv g f : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x, reachesHigh x (effort x) ↔ actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (heffort_feasible : ∀ x, e0 ≤ effort x)
    (hbase_low : ∀ x, ¬ actualHigh x → ¬ reachesHigh x e0)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hsp_high :
      ∀ x, actualHigh x →
        reachesHigh x (secondPriceEffort e0 gInv g f tilde c (theta x)))
    (hbestAE :
      SourceRankBestResponseAE μ cost rankOfEffort rankLevel levelReward
        effort) :
    ∀ᵐ x ∂μ,
      effort x =
        twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta x := by
  classical
  have hbest_ae :
      ∀ᵐ x ∂μ, ∀ d,
        levelReward (rankLevel (rankOfEffort x d)) - cost d ≤
          levelReward (rankLevel (rankOfEffort x (effort x))) -
            cost (effort x) :=
    sourceRankBestResponseAE_best_response_ae hbestAE
  filter_upwards [hbest_ae] with x hbest_x
  have hbest_scalar :
      ∀ d,
        (if reachesHigh x d then highReward else lowReward) - cost d
          ≤ (if reachesHigh x (effort x) then highReward else lowReward) -
            cost (effort x) := by
    intro d
    have h := hbest_x d
    have hactual_reward :
        levelReward (rankLevel (rankOfEffort x (effort x))) =
          if reachesHigh x (effort x) then highReward else lowReward := by
      rw [hlevel x (effort x)]
      by_cases hxeffort : reachesHigh x (effort x)
      · simp [hxeffort, hlevel_one]
      · simp [hxeffort, hlevel_zero]
    have hdev_reward :
        levelReward (rankLevel (rankOfEffort x d)) =
          if reachesHigh x d then highReward else lowReward := by
      rw [hlevel x d]
      by_cases hd : reachesHigh x d
      · simp [hd, hlevel_one]
      · simp [hd, hlevel_zero]
    rw [hactual_reward, hdev_reward] at h
    exact h
  by_cases hx : actualHigh x
  · have hactual_high : reachesHigh x (effort x) :=
      (hactual_reaches x).2 hx
    have huniq :
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x) :=
      secondPrice_twoLevel_high_band_effort_unique_of_best_response
        (lowReward := lowReward) (highReward := highReward)
        (e0 := e0) (tilde := tilde) (c := c) (theta := theta x)
        (effort := effort x) (cost := cost) (gInv := gInv) (g := g)
        (f := f) (reachesHigh := reachesHigh x)
        hg_strict (hf_high_pos x hx) hInv hcost_mono hcost_strict
        (heffort_feasible x) hactual_high
        (fun d hd hd_feasible => hreaches_boundary x d hd hd_feasible)
        (hsp_high x hx) hbest_scalar
    simpa [twoLevelSecondPriceEffort, hx] using huniq
  · have hactual_low : ¬ reachesHigh x (effort x) := by
      intro hreach
      exact hx ((hactual_reaches x).1 hreach)
    have huniq : effort x = e0 :=
      secondPrice_twoLevel_low_band_effort_unique_of_best_response
        (lowReward := lowReward) (highReward := highReward)
        (e0 := e0) (effort := effort x) (cost := cost)
        (reachesHigh := reachesHigh x)
        hcost_strict hbase_min (heffort_feasible x) hactual_low
        (hbase_low x hx) hbest_scalar
    simpa [twoLevelSecondPriceEffort, hx] using huniq

/--
Pointwise two-level source best-response theorem.  Once the rank layer is
really two-level, chosen low-band efforts are the minimum-cost effort `e0`,
chosen high-band efforts use the displayed second-price formula, and the
high-reaching predicate is exactly the source score-boundary predicate, the
whole applicant profile satisfies `SourceRankBestResponse`.
-/
theorem secondPrice_twoLevel_sourceRankBestResponse_of_score_boundaries
    {α : Type*}
    {lowReward highReward e0 tilde c : ℝ}
    {cost gInv g f : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta effort : α → ℝ}
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
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
    (hg_deviation_nonneg :
      ∀ x d, reachesHigh x d → 0 ≤ g d)
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d) :
    SourceRankBestResponse cost rankOfEffort rankLevel levelReward effort := by
  classical
  intro x d
  have hactualLevel :
      rankLevel (rankOfEffort x (effort x)) =
        if actualHigh x then 1 else 0 := by
    rw [hlevel x (effort x)]
    by_cases hx : actualHigh x
    · have hreaches : reachesHigh x (effort x) := (hactual_reaches x).2 hx
      simp [hx, hreaches]
    · have hnreaches : ¬ reachesHigh x (effort x) := by
        intro hreaches
        exact hx ((hactual_reaches x).1 hreaches)
      simp [hx, hnreaches]
  rw [hactualLevel, hlevel x d]
  have hdevReward :
      levelReward (if reachesHigh x d then 1 else 0) =
        if reachesHigh x d then highReward else lowReward := by
    by_cases hd : reachesHigh x d
    · simp [hd, hlevel_one]
    · simp [hd, hlevel_zero]
  rw [hdevReward]
  by_cases hx : actualHigh x
  · have hbest :=
      secondPrice_twoLevel_high_band_best_response_of_score_boundary
        (lowReward := lowReward) (highReward := highReward)
        (e0 := e0) (tilde := tilde) (c := c) (theta := theta x)
        (cost := cost) (gInv := gInv) (g := g) (f := f)
        (reachesHigh := reachesHigh x)
        hg_strict (hf_high_pos x hx) hInv hcost_mono hbase_min
        htilde_feasible htilde_cost (hboundary_reaches_high x hx)
        (fun d hd hd_feasible => hreaches_boundary x d hd hd_feasible)
        (fun d hd => hdeviation_feasible x d hd)
    have heffort :
        effort x = secondPriceEffort e0 gInv g f tilde c (theta x) :=
      heffort_high x hx
    simpa [hx, heffort, hlevel_zero, hlevel_one, ge_iff_le] using hbest d
  · have hbest :=
      secondPrice_twoLevel_low_band_best_response_of_score_boundary
        (lowReward := lowReward) (highReward := highReward)
        (e0 := e0) (tilde := tilde) (c := c) (theta := theta x)
        (cost := cost) (g := g) (f := f)
        (reachesHigh := reachesHigh x)
        hg_strict hf_cutoff_pos (hf_low_le_cutoff x hx)
        (fun d hd => hg_deviation_nonneg x d hd) hcost_mono hbase_min
        htilde_feasible htilde_cost
        (fun d hd hd_feasible => hreaches_boundary x d hd hd_feasible)
        (fun d hd => hdeviation_feasible x d hd)
    have heffort : effort x = e0 := heffort_low x hx
    simpa [hx, heffort, hlevel_zero, hlevel_one, ge_iff_le] using hbest d

/--
Pointwise two-level source best-response theorem for the displayed effort
profile itself.  This packages the low/high effort equalities into the source
effort function instead of asking callers to provide them separately.
-/
theorem secondPrice_twoLevel_sourceRankBestResponse_of_score_boundaries_function
    {α : Type*}
    {lowReward highReward e0 tilde c : ℝ}
    {cost gInv g f : ℝ → ℝ}
    {rankOfEffort : α → ℝ → ℝ}
    {rankLevel : ℝ → ℕ} {levelReward : ℕ → ℝ}
    {theta : α → ℝ}
    {actualHigh : α → Prop} [DecidablePred actualHigh]
    {reachesHigh : α → ℝ → Prop} [∀ x, DecidablePred (reachesHigh x)]
    (hg_strict : StrictMono g)
    (hInv : Function.RightInverse gInv g)
    (hcost_mono : MonotoneOn cost (Set.Ici e0))
    (hbase_min : ∀ d, cost e0 ≤ cost d)
    (htilde_feasible : e0 ≤ tilde)
    (htilde_cost :
      cost tilde = cost e0 + (highReward - lowReward))
    (hlevel_zero : levelReward 0 = lowReward)
    (hlevel_one : levelReward 1 = highReward)
    (hactual_reaches :
      ∀ x,
        reachesHigh x
          (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta x) ↔
            actualHigh x)
    (hlevel :
      ∀ x d, rankLevel (rankOfEffort x d) =
        if reachesHigh x d then 1 else 0)
    (hf_cutoff_pos : 0 < f c)
    (hf_low_le_cutoff :
      ∀ x, ¬ actualHigh x → f (theta x) ≤ f c)
    (hf_high_pos :
      ∀ x, actualHigh x → 0 < f (theta x))
    (hboundary_reaches_high :
      ∀ x, actualHigh x → g tilde * f c ≤ g tilde * f (theta x))
    (hg_deviation_nonneg :
      ∀ x d, reachesHigh x d → 0 ≤ g d)
    (hreaches_boundary :
      ∀ x d, reachesHigh x d → e0 ≤ d →
        g tilde * f c ≤ g d * f (theta x))
    (hdeviation_feasible :
      ∀ x d, reachesHigh x d → e0 ≤ d) :
    SourceRankBestResponse cost rankOfEffort rankLevel levelReward
      (twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta) := by
  refine secondPrice_twoLevel_sourceRankBestResponse_of_score_boundaries
    (theta := theta)
    (effort := twoLevelSecondPriceEffort e0 gInv g f tilde c actualHigh theta)
    (actualHigh := actualHigh) (reachesHigh := reachesHigh)
    hg_strict hInv hcost_mono hbase_min htilde_feasible htilde_cost
    hlevel_zero hlevel_one hactual_reaches hlevel ?_ ?_
    hf_cutoff_pos hf_low_le_cutoff hf_high_pos hboundary_reaches_high
    hg_deviation_nonneg hreaches_boundary hdeviation_feasible
  · intro x hx
    simp [twoLevelSecondPriceEffort, hx]
  · intro x hx
    simp [twoLevelSecondPriceEffort, hx]

theorem secondPrice_adjacent_boundary_no_profit_of_cost_equation
    {ellPrev ellNext prevCost boundaryCost : ℝ}
    (hcost : boundaryCost = prevCost + (ellNext - ellPrev)) :
    ellNext - boundaryCost ≤ ellPrev - prevCost := by
  rw [hcost]
  linarith

theorem secondPrice_adjacent_boundary_profit_of_lower_cost
    {ellPrev ellNext prevCost devCost boundaryCost : ℝ}
    (hcost : boundaryCost = prevCost + (ellNext - ellPrev))
    (hdev : devCost < boundaryCost) :
    ellPrev - prevCost < ellNext - devCost := by
  rw [hcost] at hdev
  linarith

theorem secondPrice_boundaryEffort_mono_of_rewardGap_mono
    {e0 baseCost gapLow gapHigh tildeLow tildeHigh : ℝ} {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (htildeLow_mem : e0 ≤ tildeLow)
    (htildeHigh_mem : e0 ≤ tildeHigh)
    (hcostLow : cost tildeLow = baseCost + gapLow)
    (hcostHigh : cost tildeHigh = baseCost + gapHigh)
    (hgap : gapLow ≤ gapHigh) :
    tildeLow ≤ tildeHigh := by
  by_contra hnot
  have hlt : tildeHigh < tildeLow := lt_of_not_ge hnot
  have hcost_lt : cost tildeHigh < cost tildeLow :=
    hcost_strict htildeHigh_mem htildeLow_mem hlt
  have hcost_ge : cost tildeLow ≤ cost tildeHigh := by
    rw [hcostLow, hcostHigh]
    linarith
  exact not_lt_of_ge hcost_ge hcost_lt

theorem secondPrice_boundaryEffort_eq_of_rewardGap_eq
    {e0 baseCost gapLow gapHigh tildeLow tildeHigh : ℝ} {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (htildeLow_mem : e0 ≤ tildeLow)
    (htildeHigh_mem : e0 ≤ tildeHigh)
    (hcostLow : cost tildeLow = baseCost + gapLow)
    (hcostHigh : cost tildeHigh = baseCost + gapHigh)
    (hgap : gapLow = gapHigh) :
    tildeLow = tildeHigh := by
  have hle :
      tildeLow ≤ tildeHigh :=
    secondPrice_boundaryEffort_mono_of_rewardGap_mono
      hcost_strict htildeLow_mem htildeHigh_mem hcostLow hcostHigh
      (le_of_eq hgap)
  have hge :
      tildeHigh ≤ tildeLow :=
    secondPrice_boundaryEffort_mono_of_rewardGap_mono
      hcost_strict htildeHigh_mem htildeLow_mem hcostHigh hcostLow
      (ge_of_eq hgap)
  exact le_antisymm hle hge

theorem secondPrice_boundaryEffort_strictMono_of_rewardGap_strictMono
    {e0 baseCost gapLow gapHigh tildeLow tildeHigh : ℝ} {cost : ℝ → ℝ}
    (hcost_strict : StrictMonoOn cost (Set.Ici e0))
    (htildeLow_mem : e0 ≤ tildeLow)
    (htildeHigh_mem : e0 ≤ tildeHigh)
    (hcostLow : cost tildeLow = baseCost + gapLow)
    (hcostHigh : cost tildeHigh = baseCost + gapHigh)
    (hgap : gapLow < gapHigh) :
    tildeLow < tildeHigh := by
  have hle : tildeLow ≤ tildeHigh :=
    secondPrice_boundaryEffort_mono_of_rewardGap_mono
      hcost_strict htildeLow_mem htildeHigh_mem hcostLow hcostHigh
      (le_of_lt hgap)
  have hne : tildeLow ≠ tildeHigh := by
    intro h
    have hcost_eq : cost tildeLow = cost tildeHigh := by rw [h]
    rw [hcostLow, hcostHigh] at hcost_eq
    linarith
  exact lt_of_le_of_ne hle hne

end LBG22StrategicRanking
