import AppliedModelingLib.Foundations.Probability.SkorokhodJ1

/-!
# Deterministic translations of local Skorokhod paths

This module records the pathwise perturbation estimate for adding a varying
continuous deterministic path.  It is independent of any particular
stochastic model and is useful when a deterministic centering coefficient
converges along a functional limit.
-/

namespace AppliedModelingLib.Probability

open Filter Topology Metric

set_option maxHeartbeats 800000 in
-- The finite-entourage reduction expands the local path metric definition.
/-- If continuous deterministic forcings converge uniformly on every compact
nonnegative time interval, then translating an arbitrary sequence of local
Skorokhod paths by those forcings differs by a vanishing local-`J₁` metric
error from translation by the limiting forcing. -/
theorem eventually_forall_dist_addContinuous_lt_of_tendstoUniformlyOn
    {forcings : ℕ → ℝ → ℝ} {limitForcing : ℝ → ℝ}
    (hforcings : ∀ n, Continuous (forcings n))
    (hlimitForcing : Continuous limitForcing)
    (hconverges : ∀ horizon : ℕ,
      TendstoUniformlyOn forcings limitForcing atTop
        (Set.Icc (0 : ℝ) (horizon : ℝ)))
    (radius : ℝ) (hradius : 0 < radius) :
    letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
    letI : (@uniformity (SkorokhodJ1LocalPath ℝ)
      (SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ))).IsCountablyGenerated :=
      SkorokhodJ1LocalEntourage.uniformity_isCountablyGenerated (State := ℝ)
    letI : PseudoMetricSpace (SkorokhodJ1LocalPath ℝ) :=
      UniformSpace.pseudoMetricSpace (SkorokhodJ1LocalPath ℝ)
    ∀ᶠ n : ℕ in atTop, ∀ path : SkorokhodJ1LocalPath ℝ,
      dist
        (SkorokhodJ1LocalPath.addContinuous (forcings n) (hforcings n) path)
        (SkorokhodJ1LocalPath.addContinuous limitForcing hlimitForcing path) < radius := by
  letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
  letI : (@uniformity (SkorokhodJ1LocalPath ℝ) _).IsCountablyGenerated :=
    SkorokhodJ1LocalEntourage.uniformity_isCountablyGenerated (State := ℝ)
  letI : PseudoMetricSpace (SkorokhodJ1LocalPath ℝ) :=
    UniformSpace.pseudoMetricSpace (SkorokhodJ1LocalPath ℝ)
  obtain ⟨horizons, epsilon, hepsilon, hsubset⟩ :=
    SkorokhodJ1LocalEntourage.exists_localEntourage_subset_dist_lt (State := ℝ)
      radius hradius
  by_cases hnonempty : horizons.Nonempty
  · let horizon : ℕ := horizons.max' hnonempty
    have hhorizon : ∀ index ∈ horizons, index ≤ horizon := by
      intro index hindex
      exact Finset.le_max' horizons index hindex
    have huniform := (Metric.tendstoUniformlyOn_iff.mp (hconverges horizon))
      epsilon hepsilon
    filter_upwards [huniform] with n hn path
    have hpair :
        (SkorokhodJ1LocalPath.addContinuous (forcings n) (hforcings n) path,
          SkorokhodJ1LocalPath.addContinuous limitForcing hlimitForcing path) ∈
          SkorokhodJ1LocalEntourage horizons epsilon := by
      intro index hindex
      apply SkorokhodJ1CloseOn.of_forall_dist_lt hepsilon
      intro time htime
      rw [SkorokhodJ1LocalPath.addContinuous_apply,
        SkorokhodJ1LocalPath.addContinuous_apply]
      have hindex_horizon : (index : ℝ) ≤ (horizon : ℝ) := by
        exact_mod_cast hhorizon index hindex
      have htime_horizon : (time : ℝ) ≤ (horizon : ℝ) :=
        htime.2.trans hindex_horizon
      have hvalue := hn (time : ℝ)
        ⟨htime.1, htime_horizon⟩
      calc
        dist (path time + forcings n time)
            (path time + limitForcing time) =
            dist (forcings n time) (limitForcing time) := by
              rw [Real.dist_eq, Real.dist_eq]
              congr 1
              ring
        _ < epsilon := by simpa [dist_comm] using hvalue
    have hdist := hsubset hpair
    simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hdist
  · have hempty : horizons = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    subst horizons
    filter_upwards [] with n path
    have hpair :
        (SkorokhodJ1LocalPath.addContinuous (forcings n) (hforcings n) path,
          SkorokhodJ1LocalPath.addContinuous limitForcing hlimitForcing path) ∈
          SkorokhodJ1LocalEntourage ∅ epsilon := by
      simp [SkorokhodJ1LocalEntourage]
    have hdist := hsubset hpair
    exact hdist

/-- The uniform translation estimate gives convergence of the pathwise
local-`J₁` metric error for any selected sequence of input paths. -/
theorem tendsto_dist_addContinuous_of_tendstoUniformlyOn
    {paths : ℕ → SkorokhodJ1LocalPath ℝ}
    {forcings : ℕ → ℝ → ℝ} {limitForcing : ℝ → ℝ}
    (hforcings : ∀ n, Continuous (forcings n))
    (hlimitForcing : Continuous limitForcing)
    (hconverges : ∀ horizon : ℕ,
      TendstoUniformlyOn forcings limitForcing atTop
        (Set.Icc (0 : ℝ) (horizon : ℝ))) :
    letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
    letI : (@uniformity (SkorokhodJ1LocalPath ℝ)
      (SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ))).IsCountablyGenerated :=
      SkorokhodJ1LocalEntourage.uniformity_isCountablyGenerated (State := ℝ)
    letI : PseudoMetricSpace (SkorokhodJ1LocalPath ℝ) :=
      UniformSpace.pseudoMetricSpace (SkorokhodJ1LocalPath ℝ)
    Tendsto
      (fun n => dist
        (SkorokhodJ1LocalPath.addContinuous (forcings n) (hforcings n) (paths n))
        (SkorokhodJ1LocalPath.addContinuous limitForcing hlimitForcing (paths n)))
      atTop (𝓝 0) := by
  letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
  letI : (@uniformity (SkorokhodJ1LocalPath ℝ) _).IsCountablyGenerated :=
    SkorokhodJ1LocalEntourage.uniformity_isCountablyGenerated (State := ℝ)
  letI : PseudoMetricSpace (SkorokhodJ1LocalPath ℝ) :=
    UniformSpace.pseudoMetricSpace (SkorokhodJ1LocalPath ℝ)
  apply Metric.tendsto_atTop.2
  intro radius hradius
  rcases (eventually_atTop.1
    (eventually_forall_dist_addContinuous_lt_of_tendstoUniformlyOn
      hforcings hlimitForcing hconverges radius hradius)) with ⟨threshold, hthreshold⟩
  refine ⟨threshold, fun n hn => ?_⟩
  simpa [Real.dist_eq, abs_of_nonneg dist_nonneg] using hthreshold n hn (paths n)

end AppliedModelingLib.Probability
