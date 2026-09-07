import AppliedModelingLib.Queueing.ManyServerDiffusionCoefficients
import AppliedModelingLib.Foundations.Probability.SkorokhodJ1
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Additively driven diffusion paths for many-server queues

The Halfin--Whitt limiting diffusion has constant variance and a globally
Lipschitz, piecewise-linear drift.  Before choosing a probability law for the
continuous noise, its sample-path equation is an ordinary differential equation
with a continuous additive forcing path.  This module gives the corresponding
pathwise uniqueness result.  It deliberately does not assert the existence of
a Brownian probability space or a functional central limit theorem.
-/

namespace AppliedModelingLib.Probability.Queueing

open Filter Topology
open scoped Interval NNReal

/-- A path satisfying the differential form of an additively forced equation.
For a continuous forcing `w`, the condition says that `y - w` has derivative
`drift y`; the companion theorem below gives the equivalent integral equation.
-/
structure IsAdditiveDrivenSolution
    (drift forcing : ℝ → ℝ) (initialTime initialValue : ℝ) (path : ℝ → ℝ) : Prop where
  continuous : Continuous path
  initial : path initialTime = initialValue
  hasDeriv_sub_forcing : ∀ time : ℝ,
    HasDerivAt (fun u => path u - forcing u) (drift (path time)) time

namespace IsAdditiveDrivenSolution

/-- The differential form of an additive driven equation satisfies its exact
integral equation on every finite interval. -/
theorem integral_equation
    {drift forcing path : ℝ → ℝ} {initialTime initialValue : ℝ}
    {lipschitzConstant : ℝ≥0}
    (hdrift : LipschitzWith lipschitzConstant drift)
    (hsolution : IsAdditiveDrivenSolution drift forcing initialTime initialValue path)
    (time : ℝ) :
    path time = initialValue + (forcing time - forcing initialTime) +
      ∫ u in initialTime..time, drift (path u) := by
  have hintegrable : IntervalIntegrable (fun u => drift (path u)) MeasureTheory.volume
      initialTime time :=
    (hdrift.continuous.comp hsolution.continuous).intervalIntegrable _ _
  have hftc : ∫ u in initialTime..time, drift (path u) =
      (path time - forcing time) - (path initialTime - forcing initialTime) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hsolution.hasDeriv_sub_forcing u) hintegrable
  rw [hsolution.initial] at hftc
  linarith

/-- For a continuous forcing path, a globally Lipschitz drift has at most one
additively driven solution with any prescribed initial value.  This is the
pathwise uniqueness component of the constant-noise-coefficient SDE. -/
theorem unique
    {drift forcing first second : ℝ → ℝ} {initialTime initialValue : ℝ}
    {lipschitzConstant : ℝ≥0}
    (hforcing : Continuous forcing)
    (hdrift : LipschitzWith lipschitzConstant drift)
    (hfirst : IsAdditiveDrivenSolution drift forcing initialTime initialValue first)
    (hsecond : IsAdditiveDrivenSolution drift forcing initialTime initialValue second) :
    first = second := by
  let field : ℝ → ℝ → ℝ := fun time value => drift (value + forcing time)
  have hfield : ∀ time, LipschitzWith lipschitzConstant (field time) := by
    intro time
    simpa [field, Function.comp_def] using
      hdrift.comp (LipschitzWith.id.add (LipschitzWith.const (forcing time)))
  have hsubeq : (fun time => first time - forcing time) =
      (fun time => second time - forcing time) := by
    apply ODE_solution_unique_univ (s := fun _ : ℝ => Set.univ)
      (fun time => (hfield time).lipschitzOnWith)
    · intro time
      refine ⟨?_, Set.mem_univ _⟩
      simpa [field] using hfirst.hasDeriv_sub_forcing time
    · intro time
      refine ⟨?_, Set.mem_univ _⟩
      simpa [field] using hsecond.hasDeriv_sub_forcing time
    · rw [hfirst.initial, hsecond.initial]
  funext time
  have heq := congrFun hsubeq time
  linarith

/-- A finite-horizon stability estimate for additively driven solutions.  The
estimate is stated for the drift-free coordinates `path - forcing`, where the
ordinary Grönwall argument applies directly.  It is the deterministic
continuous-mapping ingredient for a later functional-noise limit. -/
theorem transformed_dist_le_of_forcing_dist_le
    {drift firstForcing secondForcing first second : ℝ → ℝ}
    {initialTime initialValue terminal epsilon : ℝ} {lipschitzConstant : ℝ≥0}
    (hinitial_terminal : initialTime ≤ terminal)
    (hfirstForcing : Continuous firstForcing)
    (hsecondForcing : Continuous secondForcing)
    (hdrift : LipschitzWith lipschitzConstant drift)
    (hforcing_initial : firstForcing initialTime = secondForcing initialTime)
    (hforcing_close : ∀ time ∈ Set.Icc initialTime terminal,
      dist (firstForcing time) (secondForcing time) ≤ epsilon)
    (hfirst : IsAdditiveDrivenSolution drift firstForcing initialTime initialValue first)
    (hsecond : IsAdditiveDrivenSolution drift secondForcing initialTime initialValue second) :
    ∀ time ∈ Set.Icc initialTime terminal,
      dist (first time - firstForcing time) (second time - secondForcing time) ≤
        gronwallBound 0 lipschitzConstant (lipschitzConstant * epsilon) (time - initialTime) := by
  let field : ℝ → ℝ → ℝ := fun time value => drift (value + firstForcing time)
  have hfield : ∀ time, LipschitzWith lipschitzConstant (field time) := by
    intro time
    simpa [field, Function.comp_def] using
      hdrift.comp (LipschitzWith.id.add (LipschitzWith.const (firstForcing time)))
  have hfirst_continuous : ContinuousOn (fun time => first time - firstForcing time)
      (Set.Icc initialTime terminal) :=
    (hfirst.continuous.sub hfirstForcing).continuousOn
  have hsecond_continuous : ContinuousOn (fun time => second time - secondForcing time)
      (Set.Icc initialTime terminal) :=
    (hsecond.continuous.sub hsecondForcing).continuousOn
  have hfirst_deriv : ∀ time ∈ Set.Ico initialTime terminal,
      HasDerivWithinAt (fun u => first u - firstForcing u)
        (field time (first time - firstForcing time)) (Set.Ici time) time := by
    intro time _
    simpa [field] using (hfirst.hasDeriv_sub_forcing time).hasDerivWithinAt
  have hsecond_deriv : ∀ time ∈ Set.Ico initialTime terminal,
      HasDerivWithinAt (fun u => second u - secondForcing u)
        (drift (second time)) (Set.Ici time) time := by
    intro time _
    exact (hsecond.hasDeriv_sub_forcing time).hasDerivWithinAt
  have hfirst_error : ∀ time ∈ Set.Ico initialTime terminal,
      dist (field time (first time - firstForcing time))
        (field time (first time - firstForcing time)) ≤ 0 := by
    intro time _
    exact dist_self _ |>.le
  have hsecond_error : ∀ time ∈ Set.Ico initialTime terminal,
      dist (drift (second time))
        (field time (second time - secondForcing time)) ≤
          (lipschitzConstant : ℝ) * epsilon := by
    intro time htime
    have hdistance : dist (second time) (second time - secondForcing time + firstForcing time) =
        dist (secondForcing time) (firstForcing time) := by
      rw [Real.dist_eq, Real.dist_eq]
      congr 1
      ring
    calc
      dist (drift (second time))
          (field time (second time - secondForcing time)) =
          dist (drift (second time))
            (drift (second time - secondForcing time + firstForcing time)) := by
              rfl
      _ ≤ (lipschitzConstant : ℝ) *
          dist (second time) (second time - secondForcing time + firstForcing time) :=
            hdrift.dist_le_mul _ _
      _ = (lipschitzConstant : ℝ) * dist (secondForcing time) (firstForcing time) := by
            rw [hdistance]
      _ = (lipschitzConstant : ℝ) * dist (firstForcing time) (secondForcing time) := by
            rw [dist_comm]
      _ ≤ (lipschitzConstant : ℝ) * epsilon := by
            gcongr
            exact hforcing_close time ⟨htime.1, htime.2.le⟩
  have hinitial : dist (first initialTime - firstForcing initialTime)
      (second initialTime - secondForcing initialTime) ≤ 0 := by
    rw [hfirst.initial, hsecond.initial, hforcing_initial, dist_self]
  simpa using (dist_le_of_approx_trajectories_ODE hfield hfirst_continuous hfirst_deriv
    hfirst_error hsecond_continuous hsecond_deriv hsecond_error hinitial)

/-- Uniformly close forcing paths give uniformly close solutions on a finite
interval, with the explicit Grönwall bound from
`transformed_dist_le_of_forcing_dist_le`. -/
theorem dist_le_of_forcing_dist_le
    {drift firstForcing secondForcing first second : ℝ → ℝ}
    {initialTime initialValue terminal epsilon : ℝ} {lipschitzConstant : ℝ≥0}
    (hinitial_terminal : initialTime ≤ terminal)
    (hfirstForcing : Continuous firstForcing)
    (hsecondForcing : Continuous secondForcing)
    (hdrift : LipschitzWith lipschitzConstant drift)
    (hforcing_initial : firstForcing initialTime = secondForcing initialTime)
    (hforcing_close : ∀ time ∈ Set.Icc initialTime terminal,
      dist (firstForcing time) (secondForcing time) ≤ epsilon)
    (hfirst : IsAdditiveDrivenSolution drift firstForcing initialTime initialValue first)
    (hsecond : IsAdditiveDrivenSolution drift secondForcing initialTime initialValue second) :
    ∀ time ∈ Set.Icc initialTime terminal,
      dist (first time) (second time) ≤
        gronwallBound 0 lipschitzConstant (lipschitzConstant * epsilon) (time - initialTime) +
          epsilon := by
  intro time htime
  have htransformed := transformed_dist_le_of_forcing_dist_le hinitial_terminal
    hfirstForcing hsecondForcing hdrift hforcing_initial hforcing_close hfirst hsecond time htime
  calc
    dist (first time) (second time) =
        dist ((first time - firstForcing time) + firstForcing time)
          ((second time - secondForcing time) + secondForcing time) := by ring_nf
    _ ≤ dist (first time - firstForcing time) (second time - secondForcing time) +
        dist (firstForcing time) (secondForcing time) := dist_add_add_le _ _ _ _
    _ ≤ gronwallBound 0 lipschitzConstant (lipschitzConstant * epsilon)
          (time - initialTime) + epsilon := by
        gcongr
        exact hforcing_close time htime

/-- Compact-uniform convergence of continuous additive forcing paths transfers
to local `J₁` convergence of the associated solutions.  The result is wholly
deterministic: it records the continuity of the additive-noise solution map
needed when a separate probabilistic argument supplies convergence of the
driving paths. -/
theorem locallyConverges_of_forcing_tendstoUniformlyOn
    {drift limitForcing limitPath : ℝ → ℝ}
    {forcings paths : ℕ → ℝ → ℝ}
    {initialValue : ℝ} {lipschitzConstant : ℝ≥0}
    (hforcings_continuous : ∀ n, Continuous (forcings n))
    (hlimitForcing_continuous : Continuous limitForcing)
    (hdrift : LipschitzWith lipschitzConstant drift)
    (hforcing_initial : ∀ n, forcings n 0 = limitForcing 0)
    (hsolutions : ∀ n,
      IsAdditiveDrivenSolution drift (forcings n) 0 initialValue (paths n))
    (hlimitSolution :
      IsAdditiveDrivenSolution drift limitForcing 0 initialValue limitPath)
    (hforcings : ∀ horizon : ℕ,
      TendstoUniformlyOn forcings limitForcing atTop
        (Set.Icc (0 : ℝ) (horizon : ℝ))) :
    SkorokhodJ1LocallyConverges
      (fun n => SkorokhodJ1LocalPath.ofContinuous (paths n)
        (hsolutions n).continuous)
      (SkorokhodJ1LocalPath.ofContinuous limitPath hlimitSolution.continuous) := by
  apply SkorokhodJ1LocallyConverges.of_tendstoUniformlyOn
  intro horizon
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  let stabilization : ℝ → ℝ := fun perturbation =>
    gronwallBound 0 (lipschitzConstant : ℝ)
      ((lipschitzConstant : ℝ) * perturbation) (horizon : ℝ) + perturbation
  have hstabilization_continuous : Continuous stabilization := by
    exact ((gronwallBound_continuous_ε 0 (lipschitzConstant : ℝ) (horizon : ℝ)).comp
      (continuous_const.mul continuous_id)).add continuous_id
  have hstabilization_zero : stabilization 0 = 0 := by
    simp [stabilization, gronwallBound_ε0_δ0]
  rcases Metric.continuousAt_iff.mp
      (hstabilization_continuous.continuousAt : ContinuousAt stabilization 0)
      epsilon hepsilon with ⟨delta, hdelta_pos, hdelta⟩
  let perturbation : ℝ := delta / 2
  have hperturbation_pos : 0 < perturbation := by
    dsimp [perturbation]
    linarith
  have hforcing_eventually :=
    Metric.tendstoUniformlyOn_iff.mp (hforcings horizon) perturbation hperturbation_pos
  filter_upwards [hforcing_eventually] with n hn time htime
  have hforcing_close : ∀ point ∈ Set.Icc (0 : ℝ) (horizon : ℝ),
      dist (forcings n point) (limitForcing point) ≤ perturbation := by
    intro point hpoint
    simpa only [dist_comm] using (hn point hpoint).le
  have hsolution_bound := dist_le_of_forcing_dist_le
    (initialTime := 0) (initialValue := initialValue) (terminal := (horizon : ℝ))
    (epsilon := perturbation) (lipschitzConstant := lipschitzConstant)
    (by positivity) (hforcings_continuous n) hlimitForcing_continuous hdrift
    (hforcing_initial n) hforcing_close (hsolutions n) hlimitSolution time htime
  have htime_le : time - 0 ≤ (horizon : ℝ) := by
    linarith [htime.2]
  have hgronwall_le := gronwallBound_mono (δ := 0)
    (ε := (lipschitzConstant : ℝ) * perturbation)
    (by positivity) (by positivity) lipschitzConstant.coe_nonneg htime_le
  have hsolution_stabilization :
      dist (paths n time) (limitPath time) ≤ stabilization perturbation := by
    calc
      dist (paths n time) (limitPath time) ≤
          gronwallBound 0 (lipschitzConstant : ℝ)
            ((lipschitzConstant : ℝ) * perturbation) (time - 0) + perturbation := hsolution_bound
      _ ≤ gronwallBound 0 (lipschitzConstant : ℝ)
            ((lipschitzConstant : ℝ) * perturbation) (horizon : ℝ) + perturbation := by
          simpa only [add_comm] using add_le_add_right hgronwall_le perturbation
      _ = stabilization perturbation := by rfl
  have hperturbation_small : dist perturbation 0 < delta := by
    dsimp [perturbation]
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < delta / 2)]
    linarith
  have hstabilization_abs : |stabilization perturbation| < epsilon := by
    simpa [Real.dist_eq, hstabilization_zero] using hdelta hperturbation_small
  have hresult : dist (paths n time) (limitPath time) < epsilon :=
    hsolution_stabilization.trans_lt
      (lt_of_le_of_lt (le_abs_self _) hstabilization_abs)
  simpa only [SkorokhodJ1LocalPath.ofContinuous_apply, dist_comm] using hresult

end IsAdditiveDrivenSolution

/-- A possibly discontinuous path whose drift-free coordinate is a
right-differentiable solution of an additive driven equation.  This form is
tailored to jump prelimit paths: all jumps may be carried by `forcing`, while
`path - forcing` is continuous and has the drift as its right derivative. -/
structure IsAdditiveDrivenPath
    (drift forcing : ℝ → ℝ) (initialTime initialValue : ℝ) (path : ℝ → ℝ) : Prop where
  continuous_sub_forcing : Continuous (fun u => path u - forcing u)
  initial : path initialTime = initialValue
  hasDerivWithinAt_sub_forcing : ∀ time : ℝ,
    HasDerivWithinAt (fun u => path u - forcing u) (drift (path time))
      (Set.Ici time) time

/-- The source-domain version of an additively driven path.  Queueing
diffusion limits are naturally specified from their initial time onward, so
this predicate deliberately makes no claim about an arbitrary negative-time
extension of the path or forcing. -/
structure IsAdditiveDrivenPathOn
    (drift forcing : ℝ → ℝ) (initialTime initialValue : ℝ) (path : ℝ → ℝ) : Prop where
  continuousOn_sub_forcing : ContinuousOn (fun u => path u - forcing u)
    (Set.Ici initialTime)
  initial : path initialTime = initialValue
  hasDerivWithinAt_sub_forcing : ∀ time : ℝ, time ∈ Set.Ici initialTime →
    HasDerivWithinAt (fun u => path u - forcing u) (drift (path time))
      (Set.Ici time) time

namespace IsAdditiveDrivenPathOn

/-- A globally driven path restricts to the corresponding source-domain
relation. -/
theorem of_isAdditiveDrivenPath
    {drift forcing path : ℝ → ℝ} {initialTime initialValue : ℝ}
    (hpath : IsAdditiveDrivenPath drift forcing initialTime initialValue path) :
    IsAdditiveDrivenPathOn drift forcing initialTime initialValue path := by
  exact ⟨hpath.continuous_sub_forcing.continuousOn, hpath.initial,
    fun time _ => hpath.hasDerivWithinAt_sub_forcing time⟩

/-- Replacing a forcing by an equal path on the source time domain preserves
the additively driven-path relation. -/
theorem congr_forcing_eqOn
    {drift forcing₁ forcing₂ path : ℝ → ℝ} {initialTime initialValue : ℝ}
    (hpath : IsAdditiveDrivenPathOn drift forcing₁ initialTime initialValue path)
    (hforcing : Set.EqOn forcing₁ forcing₂ (Set.Ici initialTime)) :
    IsAdditiveDrivenPathOn drift forcing₂ initialTime initialValue path := by
  refine ⟨?_, hpath.initial, ?_⟩
  · refine hpath.continuousOn_sub_forcing.congr ?_
    intro time htime
    change path time - forcing₂ time = path time - forcing₁ time
    rw [(hforcing htime).symm]
  · intro time htime
    refine (hpath.hasDerivWithinAt_sub_forcing time htime).congr ?_ ?_
    · intro point hpoint
      change path point - forcing₂ point = path point - forcing₁ point
      have htime' : initialTime ≤ time := htime
      have hpoint' : time ≤ point := hpoint
      have hsource : point ∈ Set.Ici initialTime := htime'.trans hpoint'
      rw [(hforcing hsource).symm]
    · change path time - forcing₂ time = path time - forcing₁ time
      rw [(hforcing htime).symm]

/-- Anchoring the forcing path at time zero does not change the driven-path
relation.  The drift-free coordinate changes only by a constant, while the
anchored local `J₁` path has value zero at the initial time. -/
theorem anchorAtZero
    {drift : ℝ → ℝ} {forcing path : SkorokhodJ1LocalPath ℝ} {initialValue : ℝ}
    (hpath : IsAdditiveDrivenPathOn drift (fun time => forcing time) 0 initialValue
      (fun time => path time)) :
    IsAdditiveDrivenPathOn drift
      (fun time => SkorokhodJ1LocalPath.anchorAtZero forcing time) 0 initialValue
      (fun time => path time) := by
  refine ⟨?_, hpath.initial, ?_⟩
  · have hcontinuous := hpath.continuousOn_sub_forcing.add
      (continuousOn_const : ContinuousOn (fun _ : ℝ => forcing 0) (Set.Ici (0 : ℝ)))
    convert hcontinuous using 1
    funext time
    simp only [SkorokhodJ1LocalPath.anchorAtZero_apply, Pi.add_apply]
    ring
  · intro time htime
    have hderiv := (hpath.hasDerivWithinAt_sub_forcing time htime).const_add (forcing 0)
    convert hderiv using 1
    funext point
    simp only [SkorokhodJ1LocalPath.anchorAtZero_apply]
    ring

end IsAdditiveDrivenPathOn

namespace IsAdditiveDrivenPath

/-- Build a right-differentiable driven path from its integral equation.  This
is the bridge appropriate for jump-process compensators: right continuity of
the integrand yields the right derivative of its primitive even at a jump
time. -/
theorem of_integral_equation
    {drift forcing path : ℝ → ℝ} {initialTime initialValue offset : ℝ}
    (hinitial : path initialTime = initialValue)
    (hintegrable : ∀ first second : ℝ,
      IntervalIntegrable (fun time => drift (path time)) MeasureTheory.volume first second)
    (hstronglyMeasurable : ∀ time : ℝ,
      StronglyMeasurableAtFilter (fun u => drift (path u))
        (𝓝[Set.Ioi time] time) MeasureTheory.volume)
    (hright_continuous : ∀ time : ℝ,
      ContinuousWithinAt (fun u => drift (path u)) (Set.Ici time) time)
    (hintegral : ∀ time : ℝ,
      path time - forcing time = offset +
        ∫ u in initialTime..time, drift (path u)) :
    IsAdditiveDrivenPath drift forcing initialTime initialValue path := by
  refine ⟨?_, hinitial, ?_⟩
  · have hpath_eq : (fun time => path time - forcing time) =
        (fun time => offset + ∫ u in initialTime..time, drift (path u)) := by
      funext time
      exact hintegral time
    rw [hpath_eq]
    exact continuous_const.add
      (intervalIntegral.continuous_primitive hintegrable initialTime)
  · intro time
    have hpath_eq : (fun time => path time - forcing time) =
        (fun time => offset + ∫ u in initialTime..time, drift (path u)) := by
      funext u
      exact hintegral u
    rw [hpath_eq]
    exact HasDerivWithinAt.const_add _
      (intervalIntegral.integral_hasDerivWithinAt_right
        (s := Set.Ici time) (t := Set.Ioi time)
        (hintegrable initialTime time) (hstronglyMeasurable time)
        ((hright_continuous time).mono Set.Ioi_subset_Ici_self))

/-- Stability of the continuous drift-free coordinates does not require the
forcing paths themselves to be continuous. -/
theorem transformed_dist_le_of_forcing_dist_le
    {drift firstForcing secondForcing first second : ℝ → ℝ}
    {initialTime initialValue terminal epsilon : ℝ} {lipschitzConstant : ℝ≥0}
    (hinitial_terminal : initialTime ≤ terminal)
    (hdrift : LipschitzWith lipschitzConstant drift)
    (hforcing_initial : firstForcing initialTime = secondForcing initialTime)
    (hforcing_close : ∀ time ∈ Set.Icc initialTime terminal,
      dist (firstForcing time) (secondForcing time) ≤ epsilon)
    (hfirst : IsAdditiveDrivenPath drift firstForcing initialTime initialValue first)
    (hsecond : IsAdditiveDrivenPath drift secondForcing initialTime initialValue second) :
    ∀ time ∈ Set.Icc initialTime terminal,
      dist (first time - firstForcing time) (second time - secondForcing time) ≤
        gronwallBound 0 lipschitzConstant (lipschitzConstant * epsilon) (time - initialTime) := by
  let field : ℝ → ℝ → ℝ := fun time value => drift (value + firstForcing time)
  have hfield : ∀ time, LipschitzWith lipschitzConstant (field time) := by
    intro time
    simpa [field, Function.comp_def] using
      hdrift.comp (LipschitzWith.id.add (LipschitzWith.const (firstForcing time)))
  have hfirst_continuous : ContinuousOn (fun time => first time - firstForcing time)
      (Set.Icc initialTime terminal) := hfirst.continuous_sub_forcing.continuousOn
  have hsecond_continuous : ContinuousOn (fun time => second time - secondForcing time)
      (Set.Icc initialTime terminal) := hsecond.continuous_sub_forcing.continuousOn
  have hfirst_deriv : ∀ time ∈ Set.Ico initialTime terminal,
      HasDerivWithinAt (fun u => first u - firstForcing u)
        (field time (first time - firstForcing time)) (Set.Ici time) time := by
    intro time _
    simpa [field] using hfirst.hasDerivWithinAt_sub_forcing time
  have hsecond_deriv : ∀ time ∈ Set.Ico initialTime terminal,
      HasDerivWithinAt (fun u => second u - secondForcing u)
        (drift (second time)) (Set.Ici time) time := by
    intro time _
    exact hsecond.hasDerivWithinAt_sub_forcing time
  have hfirst_error : ∀ time ∈ Set.Ico initialTime terminal,
      dist (field time (first time - firstForcing time))
        (field time (first time - firstForcing time)) ≤ 0 := by
    intro time _
    exact dist_self _ |>.le
  have hsecond_error : ∀ time ∈ Set.Ico initialTime terminal,
      dist (drift (second time))
        (field time (second time - secondForcing time)) ≤
          (lipschitzConstant : ℝ) * epsilon := by
    intro time htime
    have hdistance : dist (second time) (second time - secondForcing time + firstForcing time) =
        dist (secondForcing time) (firstForcing time) := by
      rw [Real.dist_eq, Real.dist_eq]
      congr 1
      ring
    calc
      dist (drift (second time))
          (field time (second time - secondForcing time)) =
          dist (drift (second time))
            (drift (second time - secondForcing time + firstForcing time)) := by rfl
      _ ≤ (lipschitzConstant : ℝ) *
          dist (second time) (second time - secondForcing time + firstForcing time) :=
            hdrift.dist_le_mul _ _
      _ = (lipschitzConstant : ℝ) * dist (secondForcing time) (firstForcing time) := by
            rw [hdistance]
      _ = (lipschitzConstant : ℝ) * dist (firstForcing time) (secondForcing time) := by
            rw [dist_comm]
      _ ≤ (lipschitzConstant : ℝ) * epsilon := by
            gcongr
            exact hforcing_close time ⟨htime.1, htime.2.le⟩
  have hinitial : dist (first initialTime - firstForcing initialTime)
      (second initialTime - secondForcing initialTime) ≤ 0 := by
    rw [hfirst.initial, hsecond.initial, hforcing_initial, dist_self]
  simpa using (dist_le_of_approx_trajectories_ODE hfield hfirst_continuous hfirst_deriv
    hfirst_error hsecond_continuous hsecond_deriv hsecond_error hinitial)

/-- Uniform forcing errors control possibly discontinuous driven paths, as
long as their drift-free coordinates are classical trajectories. -/
theorem dist_le_of_forcing_dist_le
    {drift firstForcing secondForcing first second : ℝ → ℝ}
    {initialTime initialValue terminal epsilon : ℝ} {lipschitzConstant : ℝ≥0}
    (hinitial_terminal : initialTime ≤ terminal)
    (hdrift : LipschitzWith lipschitzConstant drift)
    (hforcing_initial : firstForcing initialTime = secondForcing initialTime)
    (hforcing_close : ∀ time ∈ Set.Icc initialTime terminal,
      dist (firstForcing time) (secondForcing time) ≤ epsilon)
    (hfirst : IsAdditiveDrivenPath drift firstForcing initialTime initialValue first)
    (hsecond : IsAdditiveDrivenPath drift secondForcing initialTime initialValue second) :
    ∀ time ∈ Set.Icc initialTime terminal,
      dist (first time) (second time) ≤
        gronwallBound 0 lipschitzConstant (lipschitzConstant * epsilon) (time - initialTime) +
          epsilon := by
  intro time htime
  have htransformed := transformed_dist_le_of_forcing_dist_le hinitial_terminal hdrift
    hforcing_initial hforcing_close hfirst hsecond time htime
  calc
    dist (first time) (second time) =
        dist ((first time - firstForcing time) + firstForcing time)
          ((second time - secondForcing time) + secondForcing time) := by ring_nf
    _ ≤ dist (first time - firstForcing time) (second time - secondForcing time) +
        dist (firstForcing time) (secondForcing time) := dist_add_add_le _ _ _ _
    _ ≤ gronwallBound 0 lipschitzConstant (lipschitzConstant * epsilon)
          (time - initialTime) + epsilon := by
        gcongr
        exact hforcing_close time htime

/-- Uniform forcing errors and a controlled initial displacement control two
possibly discontinuous driven paths.  This is the version of the deterministic
solution-map estimate needed when a queueing heavy-traffic limit has a varying
initial condition. -/
theorem dist_le_of_forcing_dist_le_of_initial_dist_le
    {drift firstForcing secondForcing first second : ℝ → ℝ}
    {initialTime firstInitialValue secondInitialValue terminal epsilon initialError : ℝ}
    {lipschitzConstant : ℝ≥0}
    (hinitial_terminal : initialTime ≤ terminal)
    (hdrift : LipschitzWith lipschitzConstant drift)
    (hforcing_initial : firstForcing initialTime = secondForcing initialTime)
    (hforcing_close : ∀ time ∈ Set.Icc initialTime terminal,
      dist (firstForcing time) (secondForcing time) ≤ epsilon)
    (hinitial_close : dist firstInitialValue secondInitialValue ≤ initialError)
    (hfirst : IsAdditiveDrivenPath drift firstForcing initialTime firstInitialValue first)
    (hsecond : IsAdditiveDrivenPath drift secondForcing initialTime secondInitialValue second) :
    ∀ time ∈ Set.Icc initialTime terminal,
      dist (first time) (second time) ≤
        gronwallBound initialError lipschitzConstant (lipschitzConstant * epsilon)
          (time - initialTime) + epsilon := by
  intro time htime
  let field : ℝ → ℝ → ℝ := fun point value => drift (value + firstForcing point)
  have hfield : ∀ point, LipschitzWith lipschitzConstant (field point) := by
    intro point
    simpa [field, Function.comp_def] using
      hdrift.comp (LipschitzWith.id.add (LipschitzWith.const (firstForcing point)))
  have hfirst_continuous : ContinuousOn (fun point => first point - firstForcing point)
      (Set.Icc initialTime terminal) := hfirst.continuous_sub_forcing.continuousOn
  have hsecond_continuous : ContinuousOn (fun point => second point - secondForcing point)
      (Set.Icc initialTime terminal) := hsecond.continuous_sub_forcing.continuousOn
  have hfirst_deriv : ∀ point ∈ Set.Ico initialTime terminal,
      HasDerivWithinAt (fun u => first u - firstForcing u)
        (field point (first point - firstForcing point)) (Set.Ici point) point := by
    intro point _
    simpa [field] using hfirst.hasDerivWithinAt_sub_forcing point
  have hsecond_deriv : ∀ point ∈ Set.Ico initialTime terminal,
      HasDerivWithinAt (fun u => second u - secondForcing u)
        (drift (second point)) (Set.Ici point) point := by
    intro point _
    exact hsecond.hasDerivWithinAt_sub_forcing point
  have hfirst_error : ∀ point ∈ Set.Ico initialTime terminal,
      dist (field point (first point - firstForcing point))
        (field point (first point - firstForcing point)) ≤ 0 := by
    intro point _
    exact dist_self _ |>.le
  have hsecond_error : ∀ point ∈ Set.Ico initialTime terminal,
      dist (drift (second point))
        (field point (second point - secondForcing point)) ≤
          (lipschitzConstant : ℝ) * epsilon := by
    intro point hpoint
    have hdistance : dist (second point)
        (second point - secondForcing point + firstForcing point) =
        dist (secondForcing point) (firstForcing point) := by
      rw [Real.dist_eq, Real.dist_eq]
      congr 1
      ring
    calc
      dist (drift (second point))
          (field point (second point - secondForcing point)) =
          dist (drift (second point))
            (drift (second point - secondForcing point + firstForcing point)) := by rfl
      _ ≤ (lipschitzConstant : ℝ) *
          dist (second point) (second point - secondForcing point + firstForcing point) :=
            hdrift.dist_le_mul _ _
      _ = (lipschitzConstant : ℝ) * dist (secondForcing point) (firstForcing point) := by
            rw [hdistance]
      _ = (lipschitzConstant : ℝ) * dist (firstForcing point) (secondForcing point) := by
            rw [dist_comm]
      _ ≤ (lipschitzConstant : ℝ) * epsilon := by
            gcongr
            exact hforcing_close point ⟨hpoint.1, hpoint.2.le⟩
  have hinitial : dist (first initialTime - firstForcing initialTime)
      (second initialTime - secondForcing initialTime) ≤ initialError := by
    rw [hfirst.initial, hsecond.initial, hforcing_initial]
    calc
      dist (firstInitialValue - secondForcing initialTime)
          (secondInitialValue - secondForcing initialTime) =
          dist firstInitialValue secondInitialValue := by
            rw [Real.dist_eq, Real.dist_eq]
            congr 1
            ring
      _ ≤ initialError := hinitial_close
  have htransformed := dist_le_of_approx_trajectories_ODE hfield hfirst_continuous hfirst_deriv
    hfirst_error hsecond_continuous hsecond_deriv hsecond_error hinitial time htime
  calc
    dist (first time) (second time) =
        dist ((first time - firstForcing time) + firstForcing time)
          ((second time - secondForcing time) + secondForcing time) := by ring_nf
    _ ≤ dist (first time - firstForcing time) (second time - secondForcing time) +
        dist (firstForcing time) (secondForcing time) := dist_add_add_le _ _ _ _
    _ ≤ gronwallBound initialError lipschitzConstant (lipschitzConstant * epsilon)
          (time - initialTime) + dist (firstForcing time) (secondForcing time) := by
        gcongr
        simpa using htransformed
    _ ≤ gronwallBound initialError lipschitzConstant (lipschitzConstant * epsilon)
          (time - initialTime) + epsilon := by
        gcongr
        exact hforcing_close time htime

/-- If càdlàg forcing paths converge locally in `J₁` to a continuous forcing
path, their additively driven càdlàg solutions converge locally in `J₁`.
The proof reduces `J₁` convergence of the forcing paths to compact-uniform
convergence at the continuous limit, then applies the explicit Grönwall
estimate. -/
theorem locallyConverges_of_forcing_locallyConverges
    {drift : ℝ → ℝ}
    {forcings paths : ℕ → SkorokhodJ1LocalPath ℝ}
    {limitForcing limitPath : SkorokhodJ1LocalPath ℝ}
    {initialValue : ℝ} {lipschitzConstant : ℝ≥0}
    (hlimitForcing_continuous : Continuous (fun time : ℝ => limitForcing time))
    (hdrift : LipschitzWith lipschitzConstant drift)
    (hforcing_initial : ∀ n, forcings n 0 = limitForcing 0)
    (hsolutions : ∀ n,
      IsAdditiveDrivenPath drift (fun time : ℝ => forcings n time) 0 initialValue
        (fun time : ℝ => paths n time))
    (hlimitSolution :
      IsAdditiveDrivenPath drift (fun time : ℝ => limitForcing time) 0 initialValue
        (fun time : ℝ => limitPath time))
    (hforcings : SkorokhodJ1LocallyConverges (fun n => forcings n) limitForcing) :
    SkorokhodJ1LocallyConverges (fun n => paths n) limitPath := by
  apply SkorokhodJ1LocallyConverges.of_tendstoUniformlyOn
  intro horizon
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  let stabilization : ℝ → ℝ := fun perturbation =>
    gronwallBound 0 (lipschitzConstant : ℝ)
      ((lipschitzConstant : ℝ) * perturbation) (horizon : ℝ) + perturbation
  have hstabilization_continuous : Continuous stabilization := by
    exact ((gronwallBound_continuous_ε 0 (lipschitzConstant : ℝ) (horizon : ℝ)).comp
      (continuous_const.mul continuous_id)).add continuous_id
  have hstabilization_zero : stabilization 0 = 0 := by
    simp [stabilization, gronwallBound_ε0_δ0]
  rcases Metric.continuousAt_iff.mp
      (hstabilization_continuous.continuousAt : ContinuousAt stabilization 0)
      epsilon hepsilon with ⟨delta, hdelta_pos, hdelta⟩
  let perturbation : ℝ := delta / 2
  have hperturbation_pos : 0 < perturbation := by
    dsimp [perturbation]
    linarith
  have huniform := SkorokhodJ1LocallyConverges.tendstoUniformlyOn_of_continuousOn
    horizon hforcings hlimitForcing_continuous.continuousOn
  have hforcing_eventually :=
    Metric.tendstoUniformlyOn_iff.mp huniform perturbation hperturbation_pos
  filter_upwards [hforcing_eventually] with n hn time htime
  have hforcing_close : ∀ point ∈ Set.Icc (0 : ℝ) (horizon : ℝ),
      dist (forcings n point) (limitForcing point) ≤ perturbation := by
    intro point hpoint
    simpa only [dist_comm] using (hn point hpoint).le
  have hsolution_bound := dist_le_of_forcing_dist_le
    (initialTime := 0) (initialValue := initialValue) (terminal := (horizon : ℝ))
    (epsilon := perturbation) (lipschitzConstant := lipschitzConstant)
    (by positivity) hdrift (hforcing_initial n) hforcing_close
    (hsolutions n) hlimitSolution time htime
  have htime_le : time - 0 ≤ (horizon : ℝ) := by
    linarith [htime.2]
  have hgronwall_le := gronwallBound_mono (δ := 0)
    (ε := (lipschitzConstant : ℝ) * perturbation)
    (by positivity) (by positivity) lipschitzConstant.coe_nonneg htime_le
  have hsolution_stabilization :
      dist (paths n time) (limitPath time) ≤ stabilization perturbation := by
    calc
      dist (paths n time) (limitPath time) ≤
          gronwallBound 0 (lipschitzConstant : ℝ)
            ((lipschitzConstant : ℝ) * perturbation) (time - 0) + perturbation := hsolution_bound
      _ ≤ gronwallBound 0 (lipschitzConstant : ℝ)
            ((lipschitzConstant : ℝ) * perturbation) (horizon : ℝ) + perturbation := by
          simpa only [add_comm] using add_le_add_right hgronwall_le perturbation
      _ = stabilization perturbation := by rfl
  have hperturbation_small : dist perturbation 0 < delta := by
    dsimp [perturbation]
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < delta / 2)]
    linarith
  have hstabilization_abs : |stabilization perturbation| < epsilon := by
    simpa [Real.dist_eq, hstabilization_zero] using hdelta hperturbation_small
  have hresult : dist (paths n time) (limitPath time) < epsilon :=
    hsolution_stabilization.trans_lt
      (lt_of_le_of_lt (le_abs_self _) hstabilization_abs)
  simpa only [dist_comm] using hresult

/-- The local-`J₁` solution-map theorem with converging initial states.  This
is the deterministic continuous-mapping input appropriate for diffusion
limits whose initial fluctuations converge together with their driving
noise. -/
theorem locallyConverges_of_forcing_locallyConverges_of_initial_tendsto
    {drift : ℝ → ℝ}
    {forcings paths : ℕ → SkorokhodJ1LocalPath ℝ}
    {limitForcing limitPath : SkorokhodJ1LocalPath ℝ}
    {initialValues : ℕ → ℝ} {initialValue : ℝ} {lipschitzConstant : ℝ≥0}
    (hlimitForcing_continuous : Continuous (fun time : ℝ => limitForcing time))
    (hdrift : LipschitzWith lipschitzConstant drift)
    (hforcing_initial : ∀ n, forcings n 0 = limitForcing 0)
    (hsolutions : ∀ n,
      IsAdditiveDrivenPath drift (fun time : ℝ => forcings n time) 0 (initialValues n)
        (fun time : ℝ => paths n time))
    (hlimitSolution :
      IsAdditiveDrivenPath drift (fun time : ℝ => limitForcing time) 0 initialValue
        (fun time : ℝ => limitPath time))
    (hinitialValues : Tendsto initialValues atTop (𝓝 initialValue))
    (hforcings : SkorokhodJ1LocallyConverges (fun n => forcings n) limitForcing) :
    SkorokhodJ1LocallyConverges (fun n => paths n) limitPath := by
  apply SkorokhodJ1LocallyConverges.of_tendstoUniformlyOn
  intro horizon
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  let stabilization : ℝ → ℝ := fun perturbation =>
    gronwallBound perturbation (lipschitzConstant : ℝ)
      ((lipschitzConstant : ℝ) * perturbation) (horizon : ℝ) + perturbation
  have hstabilization_continuous : Continuous stabilization := by
    dsimp [stabilization]
    unfold gronwallBound
    split_ifs with hzero
    · fun_prop
    · fun_prop
  have hstabilization_zero : stabilization 0 = 0 := by
    simp [stabilization, gronwallBound_ε0_δ0]
  rcases Metric.continuousAt_iff.mp
      (hstabilization_continuous.continuousAt : ContinuousAt stabilization 0)
      epsilon hepsilon with ⟨delta, hdelta_pos, hdelta⟩
  let perturbation : ℝ := delta / 2
  have hperturbation_pos : 0 < perturbation := by
    dsimp [perturbation]
    linarith
  have huniform := SkorokhodJ1LocallyConverges.tendstoUniformlyOn_of_continuousOn
    horizon hforcings hlimitForcing_continuous.continuousOn
  have hforcing_eventually :=
    Metric.tendstoUniformlyOn_iff.mp huniform perturbation hperturbation_pos
  rcases (Metric.tendsto_atTop.1 hinitialValues) perturbation hperturbation_pos with
    ⟨threshold, hinitial_eventually⟩
  filter_upwards [hforcing_eventually, eventually_atTop.2 ⟨threshold,
    fun n hn => hinitial_eventually n hn⟩] with n hn hinitial time htime
  have hforcing_close : ∀ point ∈ Set.Icc (0 : ℝ) (horizon : ℝ),
      dist (forcings n point) (limitForcing point) ≤ perturbation := by
    intro point hpoint
    simpa only [dist_comm] using (hn point hpoint).le
  have hsolution_bound := dist_le_of_forcing_dist_le_of_initial_dist_le
    (initialTime := 0) (firstInitialValue := initialValues n)
    (secondInitialValue := initialValue) (terminal := (horizon : ℝ))
    (epsilon := perturbation) (initialError := perturbation)
    (lipschitzConstant := lipschitzConstant)
    (by positivity) hdrift (hforcing_initial n) hforcing_close hinitial.le
    (hsolutions n) hlimitSolution time htime
  have htime_le : time - 0 ≤ (horizon : ℝ) := by
    linarith [htime.2]
  have hgronwall_le := gronwallBound_mono (δ := perturbation)
    (ε := (lipschitzConstant : ℝ) * perturbation)
    (by positivity) (by positivity) lipschitzConstant.coe_nonneg htime_le
  have hsolution_stabilization :
      dist (paths n time) (limitPath time) ≤ stabilization perturbation := by
    calc
      dist (paths n time) (limitPath time) ≤
          gronwallBound perturbation (lipschitzConstant : ℝ)
            ((lipschitzConstant : ℝ) * perturbation) (time - 0) + perturbation := hsolution_bound
      _ ≤ gronwallBound perturbation (lipschitzConstant : ℝ)
            ((lipschitzConstant : ℝ) * perturbation) (horizon : ℝ) + perturbation := by
          simpa only [add_comm] using add_le_add_right hgronwall_le perturbation
      _ = stabilization perturbation := by rfl
  have hperturbation_small : dist perturbation 0 < delta := by
    dsimp [perturbation]
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < delta / 2)]
    linarith
  have hstabilization_abs : |stabilization perturbation| < epsilon := by
    simpa [Real.dist_eq, hstabilization_zero] using hdelta hperturbation_small
  have hresult : dist (paths n time) (limitPath time) < epsilon :=
    hsolution_stabilization.trans_lt
      (lt_of_le_of_lt (le_abs_self _) hstabilization_abs)
  simpa only [dist_comm] using hresult

end IsAdditiveDrivenPath

namespace IsAdditiveDrivenPathOn

/-- Uniform forcing errors and a controlled initial displacement control two
source-domain driven paths.  This is the Grönwall estimate underlying a
local-`J₁` solution-map theorem without any artificial negative-time
extension. -/
theorem dist_le_of_forcing_dist_le_of_initial_dist_le
    {drift firstForcing secondForcing first second : ℝ → ℝ}
    {initialTime firstInitialValue secondInitialValue terminal epsilon initialError : ℝ}
    {lipschitzConstant : ℝ≥0}
    (hinitial_terminal : initialTime ≤ terminal)
    (hdrift : LipschitzWith lipschitzConstant drift)
    (hforcing_initial : firstForcing initialTime = secondForcing initialTime)
    (hforcing_close : ∀ time ∈ Set.Icc initialTime terminal,
      dist (firstForcing time) (secondForcing time) ≤ epsilon)
    (hinitial_close : dist firstInitialValue secondInitialValue ≤ initialError)
    (hfirst : IsAdditiveDrivenPathOn drift firstForcing initialTime firstInitialValue first)
    (hsecond : IsAdditiveDrivenPathOn drift secondForcing initialTime secondInitialValue second) :
    ∀ time ∈ Set.Icc initialTime terminal,
      dist (first time) (second time) ≤
        gronwallBound initialError lipschitzConstant (lipschitzConstant * epsilon)
          (time - initialTime) + epsilon := by
  intro time htime
  let field : ℝ → ℝ → ℝ := fun point value => drift (value + firstForcing point)
  have hfield : ∀ point, LipschitzWith lipschitzConstant (field point) := by
    intro point
    simpa [field, Function.comp_def] using
      hdrift.comp (LipschitzWith.id.add (LipschitzWith.const (firstForcing point)))
  have hfirst_continuous : ContinuousOn (fun point => first point - firstForcing point)
      (Set.Icc initialTime terminal) :=
    hfirst.continuousOn_sub_forcing.mono (fun _ hpoint => hpoint.1)
  have hsecond_continuous : ContinuousOn (fun point => second point - secondForcing point)
      (Set.Icc initialTime terminal) :=
    hsecond.continuousOn_sub_forcing.mono (fun _ hpoint => hpoint.1)
  have hfirst_deriv : ∀ point ∈ Set.Ico initialTime terminal,
      HasDerivWithinAt (fun u => first u - firstForcing u)
        (field point (first point - firstForcing point)) (Set.Ici point) point := by
    intro point hpoint
    simpa [field] using hfirst.hasDerivWithinAt_sub_forcing point hpoint.1
  have hsecond_deriv : ∀ point ∈ Set.Ico initialTime terminal,
      HasDerivWithinAt (fun u => second u - secondForcing u)
        (drift (second point)) (Set.Ici point) point := by
    intro point hpoint
    exact hsecond.hasDerivWithinAt_sub_forcing point hpoint.1
  have hfirst_error : ∀ point ∈ Set.Ico initialTime terminal,
      dist (field point (first point - firstForcing point))
        (field point (first point - firstForcing point)) ≤ 0 := by
    intro point _
    exact dist_self _ |>.le
  have hsecond_error : ∀ point ∈ Set.Ico initialTime terminal,
      dist (drift (second point))
        (field point (second point - secondForcing point)) ≤
          (lipschitzConstant : ℝ) * epsilon := by
    intro point hpoint
    have hdistance : dist (second point)
        (second point - secondForcing point + firstForcing point) =
        dist (secondForcing point) (firstForcing point) := by
      rw [Real.dist_eq, Real.dist_eq]
      congr 1
      ring
    calc
      dist (drift (second point))
          (field point (second point - secondForcing point)) =
          dist (drift (second point))
            (drift (second point - secondForcing point + firstForcing point)) := by rfl
      _ ≤ (lipschitzConstant : ℝ) *
          dist (second point) (second point - secondForcing point + firstForcing point) :=
            hdrift.dist_le_mul _ _
      _ = (lipschitzConstant : ℝ) * dist (secondForcing point) (firstForcing point) := by
            rw [hdistance]
      _ = (lipschitzConstant : ℝ) * dist (firstForcing point) (secondForcing point) := by
            rw [dist_comm]
      _ ≤ (lipschitzConstant : ℝ) * epsilon := by
            gcongr
            exact hforcing_close point ⟨hpoint.1, hpoint.2.le⟩
  have hinitial : dist (first initialTime - firstForcing initialTime)
      (second initialTime - secondForcing initialTime) ≤ initialError := by
    rw [hfirst.initial, hsecond.initial, hforcing_initial]
    calc
      dist (firstInitialValue - secondForcing initialTime)
          (secondInitialValue - secondForcing initialTime) =
          dist firstInitialValue secondInitialValue := by
            rw [Real.dist_eq, Real.dist_eq]
            congr 1
            ring
      _ ≤ initialError := hinitial_close
  have htransformed := dist_le_of_approx_trajectories_ODE hfield hfirst_continuous hfirst_deriv
    hfirst_error hsecond_continuous hsecond_deriv hsecond_error hinitial time htime
  calc
    dist (first time) (second time) =
        dist ((first time - firstForcing time) + firstForcing time)
          ((second time - secondForcing time) + secondForcing time) := by ring_nf
    _ ≤ dist (first time - firstForcing time) (second time - secondForcing time) +
        dist (firstForcing time) (secondForcing time) := dist_add_add_le _ _ _ _
    _ ≤ gronwallBound initialError lipschitzConstant (lipschitzConstant * epsilon)
          (time - initialTime) + dist (firstForcing time) (secondForcing time) := by
        gcongr
        simpa using htransformed
      _ ≤ gronwallBound initialError lipschitzConstant (lipschitzConstant * epsilon)
          (time - initialTime) + epsilon := by
        gcongr
        exact hforcing_close time htime

/-- If càdlàg forcings converge locally in `J₁` to a forcing continuous on
the source time domain, then their source-domain additively driven solutions
with converging initial states converge locally in `J₁`.  No behavior before
the initial time is used. -/
theorem locallyConverges_of_forcing_locallyConverges_of_initial_tendsto
    {drift : ℝ → ℝ}
    {forcings paths : ℕ → SkorokhodJ1LocalPath ℝ}
    {limitForcing limitPath : SkorokhodJ1LocalPath ℝ}
    {initialValues : ℕ → ℝ} {initialValue : ℝ} {lipschitzConstant : ℝ≥0}
    (hlimitForcing_continuous : ContinuousOn (fun time : ℝ => limitForcing time)
      (Set.Ici (0 : ℝ)))
    (hdrift : LipschitzWith lipschitzConstant drift)
    (hforcing_initial : ∀ n, forcings n 0 = limitForcing 0)
    (hsolutions : ∀ n,
      IsAdditiveDrivenPathOn drift (fun time : ℝ => forcings n time) 0 (initialValues n)
        (fun time : ℝ => paths n time))
    (hlimitSolution :
      IsAdditiveDrivenPathOn drift (fun time : ℝ => limitForcing time) 0 initialValue
        (fun time : ℝ => limitPath time))
    (hinitialValues : Tendsto initialValues atTop (𝓝 initialValue))
    (hforcings : SkorokhodJ1LocallyConverges (fun n => forcings n) limitForcing) :
    SkorokhodJ1LocallyConverges (fun n => paths n) limitPath := by
  apply SkorokhodJ1LocallyConverges.of_tendstoUniformlyOn
  intro horizon
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  let stabilization : ℝ → ℝ := fun perturbation =>
    gronwallBound perturbation (lipschitzConstant : ℝ)
      ((lipschitzConstant : ℝ) * perturbation) (horizon : ℝ) + perturbation
  have hstabilization_continuous : Continuous stabilization := by
    dsimp [stabilization]
    unfold gronwallBound
    split_ifs with hzero
    · fun_prop
    · fun_prop
  have hstabilization_zero : stabilization 0 = 0 := by
    simp [stabilization, gronwallBound_ε0_δ0]
  rcases Metric.continuousAt_iff.mp
      (hstabilization_continuous.continuousAt : ContinuousAt stabilization 0)
      epsilon hepsilon with ⟨delta, hdelta_pos, hdelta⟩
  let perturbation : ℝ := delta / 2
  have hperturbation_pos : 0 < perturbation := by
    dsimp [perturbation]
    linarith
  have huniform := SkorokhodJ1LocallyConverges.tendstoUniformlyOn_of_continuousOn
    horizon hforcings (hlimitForcing_continuous.mono (fun _ htime => htime.1))
  have hforcing_eventually :=
    Metric.tendstoUniformlyOn_iff.mp huniform perturbation hperturbation_pos
  rcases (Metric.tendsto_atTop.1 hinitialValues) perturbation hperturbation_pos with
    ⟨threshold, hinitial_eventually⟩
  filter_upwards [hforcing_eventually, eventually_atTop.2 ⟨threshold,
    fun n hn => hinitial_eventually n hn⟩] with n hn hinitial time htime
  have hforcing_close : ∀ point ∈ Set.Icc (0 : ℝ) (horizon : ℝ),
      dist (forcings n point) (limitForcing point) ≤ perturbation := by
    intro point hpoint
    simpa only [dist_comm] using (hn point hpoint).le
  have hsolution_bound := dist_le_of_forcing_dist_le_of_initial_dist_le
    (initialTime := 0) (firstInitialValue := initialValues n)
    (secondInitialValue := initialValue) (terminal := (horizon : ℝ))
    (epsilon := perturbation) (initialError := perturbation)
    (lipschitzConstant := lipschitzConstant)
    (by positivity) hdrift (hforcing_initial n) hforcing_close hinitial.le
    (hsolutions n) hlimitSolution time htime
  have htime_le : time - 0 ≤ (horizon : ℝ) := by
    linarith [htime.2]
  have hgronwall_le := gronwallBound_mono (δ := perturbation)
    (ε := (lipschitzConstant : ℝ) * perturbation)
    (by positivity) (by positivity) lipschitzConstant.coe_nonneg htime_le
  have hsolution_stabilization :
      dist (paths n time) (limitPath time) ≤ stabilization perturbation := by
    calc
      dist (paths n time) (limitPath time) ≤
          gronwallBound perturbation (lipschitzConstant : ℝ)
            ((lipschitzConstant : ℝ) * perturbation) (time - 0) + perturbation := hsolution_bound
      _ ≤ gronwallBound perturbation (lipschitzConstant : ℝ)
            ((lipschitzConstant : ℝ) * perturbation) (horizon : ℝ) + perturbation := by
          simpa only [add_comm] using add_le_add_right hgronwall_le perturbation
      _ = stabilization perturbation := by rfl
  have hperturbation_small : dist perturbation 0 < delta := by
    dsimp [perturbation]
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith : 0 < delta / 2)]
    linarith
  have hstabilization_abs : |stabilization perturbation| < epsilon := by
    simpa [Real.dist_eq, hstabilization_zero] using hdelta hperturbation_small
  have hresult : dist (paths n time) (limitPath time) < epsilon :=
    hsolution_stabilization.trans_lt
      (lt_of_le_of_lt (le_abs_self _) hstabilization_abs)
  simpa only [dist_comm] using hresult

end IsAdditiveDrivenPathOn

/-- Inputs consisting of an initial value and a forcing path for which the
source-domain additive driven relation has a solution. -/
def additiveDrivenInputDomainOn (drift : ℝ → ℝ) :
    Set (ℝ × SkorokhodJ1LocalPath ℝ) :=
  {input | ∃ path : SkorokhodJ1LocalPath ℝ,
    IsAdditiveDrivenPathOn drift (fun time => input.2 time) 0 input.1
      (fun time => path time)}

/-- A chosen source-domain solution for every input in the solvable domain.
The selector is only used on this subtype; it does not assert existence away
from the domain. -/
noncomputable def additiveDrivenSolutionOn (drift : ℝ → ℝ) :
    additiveDrivenInputDomainOn drift → SkorokhodJ1LocalPath ℝ :=
  fun input => Classical.choose input.property

/-- The selected output satisfies the source-domain driven relation. -/
theorem additiveDrivenSolutionOn_spec {drift : ℝ → ℝ}
    (input : additiveDrivenInputDomainOn drift) :
    IsAdditiveDrivenPathOn drift (fun time => input.1.2 time) 0 input.1.1
      (fun time => additiveDrivenSolutionOn drift input time) :=
  Classical.choose_spec input.property

/-- On the domain of solvable source-domain inputs, the selected output path
depends continuously on the initial value and the local-`J₁` forcing at every
input whose forcing is continuous from the initial time onward.  The proof
anchors both forcing paths at time zero before applying the explicit
Grönwall stability estimate. -/
theorem continuousAt_additiveDrivenSolutionOn_of_forcing_continuousOn
    {drift : ℝ → ℝ} {lipschitzConstant : ℝ≥0}
    (hdrift : LipschitzWith lipschitzConstant drift)
    {limit : additiveDrivenInputDomainOn drift}
    (hlimitForcing_continuous : ContinuousOn (fun time : ℝ => limit.1.2 time)
      (Set.Ici (0 : ℝ))) :
    letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
      SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
    letI : (@uniformity (SkorokhodJ1LocalPath ℝ)
      (SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ))).IsCountablyGenerated :=
      SkorokhodJ1LocalEntourage.uniformity_isCountablyGenerated (State := ℝ)
    letI : PseudoMetricSpace (SkorokhodJ1LocalPath ℝ) :=
      UniformSpace.pseudoMetricSpace (SkorokhodJ1LocalPath ℝ)
    ContinuousAt (additiveDrivenSolutionOn drift) limit := by
  letI : UniformSpace (SkorokhodJ1LocalPath ℝ) :=
    SkorokhodJ1LocalEntourage.uniformSpace (State := ℝ)
  letI : (@uniformity (SkorokhodJ1LocalPath ℝ) _).IsCountablyGenerated :=
    SkorokhodJ1LocalEntourage.uniformity_isCountablyGenerated (State := ℝ)
  letI : PseudoMetricSpace (SkorokhodJ1LocalPath ℝ) :=
    UniformSpace.pseudoMetricSpace (SkorokhodJ1LocalPath ℝ)
  rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
  intro input hinput
  have hinputValues : Tendsto (fun n : ℕ => (input n).1) atTop (𝓝 limit.1) := by
    exact continuous_subtype_val.continuousAt.tendsto.comp hinput
  have hinitial : Tendsto (fun n : ℕ => (input n).1.1) atTop (𝓝 limit.1.1) := by
    exact continuous_fst.continuousAt.tendsto.comp hinputValues
  have hforcings : Tendsto (fun n : ℕ => (input n).1.2) atTop (𝓝 limit.1.2) := by
    exact continuous_snd.continuousAt.tendsto.comp hinputValues
  have hanchoredForcings :
      Tendsto (fun n : ℕ => SkorokhodJ1LocalPath.anchorAtZero (input n).1.2)
        atTop (𝓝 (SkorokhodJ1LocalPath.anchorAtZero limit.1.2)) := by
    exact (SkorokhodJ1LocalEntourage.continuous_anchorAtZero.continuousAt.tendsto).comp
      hforcings
  have hanchoredForcingsLocal : SkorokhodJ1LocallyConverges
      (fun n : ℕ => SkorokhodJ1LocalPath.anchorAtZero (input n).1.2)
      (SkorokhodJ1LocalPath.anchorAtZero limit.1.2) :=
    SkorokhodJ1LocallyConverges.tendsto_iff.mp hanchoredForcings
  have hlimitAnchoredContinuous : ContinuousOn
      (fun time : ℝ => SkorokhodJ1LocalPath.anchorAtZero limit.1.2 time)
      (Set.Ici (0 : ℝ)) := by
    simpa only [SkorokhodJ1LocalPath.anchorAtZero_apply] using
      hlimitForcing_continuous.sub continuousOn_const
  have hpaths : SkorokhodJ1LocallyConverges
      (fun n : ℕ => additiveDrivenSolutionOn drift (input n))
      (additiveDrivenSolutionOn drift limit) := by
    refine IsAdditiveDrivenPathOn.locallyConverges_of_forcing_locallyConverges_of_initial_tendsto
      (forcings := fun n : ℕ => SkorokhodJ1LocalPath.anchorAtZero (input n).1.2)
      (paths := fun n : ℕ => additiveDrivenSolutionOn drift (input n))
      (limitForcing := SkorokhodJ1LocalPath.anchorAtZero limit.1.2)
      (limitPath := additiveDrivenSolutionOn drift limit)
      (initialValues := fun n : ℕ => (input n).1.1)
      (initialValue := limit.1.1)
      hlimitAnchoredContinuous hdrift ?_ ?_ ?_ hinitial hanchoredForcingsLocal
    · intro n
      simp only [SkorokhodJ1LocalPath.anchorAtZero_apply, sub_self]
    · intro n
      exact (additiveDrivenSolutionOn_spec (input n)).anchorAtZero
    · exact (additiveDrivenSolutionOn_spec limit).anchorAtZero
  simpa only [Function.comp_def] using
    SkorokhodJ1LocallyConverges.tendsto_iff.mpr hpaths

/-- The Halfin--Whitt piecewise-linear drift has pathwise uniqueness under any
continuous additive forcing.  The constant diffusion coefficient can be
absorbed into `forcing` (for example, as a scalar multiple of a Brownian
path), so no stochastic-calculus primitive is required for this statement. -/
theorem manyServerLimitingDrift_additiveDrivenSolution_unique
    (beta serviceRate : ℝ) {forcing first second : ℝ → ℝ}
    {initialTime initialValue : ℝ}
    (hforcing : Continuous forcing)
    (hfirst : IsAdditiveDrivenSolution
      (fun x : ℝ => serviceRate * (-beta - min x 0))
      forcing initialTime initialValue first)
    (hsecond : IsAdditiveDrivenSolution
      (fun x : ℝ => serviceRate * (-beta - min x 0))
      forcing initialTime initialValue second) :
    first = second := by
  exact IsAdditiveDrivenSolution.unique hforcing
    (lipschitzWith_manyServerLimitingDrift beta serviceRate) hfirst hsecond

end AppliedModelingLib.Probability.Queueing
